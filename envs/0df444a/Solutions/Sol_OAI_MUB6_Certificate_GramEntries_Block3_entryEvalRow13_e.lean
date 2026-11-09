-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:12:47.840826+00:00
-- url     : https://prove2.me/submissions/3f3a5a2f-14d0-40f7-aed9-58373fbcd138

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E057
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval13_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_13_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8841 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow8841 := by decide +kernel

theorem rowCheck8841 : row8841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8841 := by decide +kernel

theorem rowEval8841 (x : Key → ℝ) : Integer.Sparse.eval row8841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8841, Integer.Sparse.eval_collectBalanced, rawRowCheck8841]

theorem rawRowCheck8842 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow8842 := by decide +kernel

theorem rowCheck8842 : row8842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8842 := by decide +kernel

theorem rowEval8842 (x : Key → ℝ) : Integer.Sparse.eval row8842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8842, Integer.Sparse.eval_collectBalanced, rawRowCheck8842]

theorem rawRowCheck8843 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow8843 := by decide +kernel

theorem rowCheck8843 : row8843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8843 := by decide +kernel

theorem rowEval8843 (x : Key → ℝ) : Integer.Sparse.eval row8843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8843, Integer.Sparse.eval_collectBalanced, rawRowCheck8843]

theorem rawRowCheck8844 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8844 := by decide +kernel

theorem rowCheck8844 : row8844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8844 := by decide +kernel

theorem rowEval8844 (x : Key → ℝ) : Integer.Sparse.eval row8844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8844, Integer.Sparse.eval_collectBalanced, rawRowCheck8844]

theorem rawRowCheck8845 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form0 = rawRow8845 := by decide +kernel

theorem rowCheck8845 : row8845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8845 := by decide +kernel

theorem rowEval8845 (x : Key → ℝ) : Integer.Sparse.eval row8845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8845, Integer.Sparse.eval_collectBalanced, rawRowCheck8845]

theorem rawRowCheck8846 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form0 = rawRow8846 := by decide +kernel

theorem rowCheck8846 : row8846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8846 := by decide +kernel

theorem rowEval8846 (x : Key → ℝ) : Integer.Sparse.eval row8846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8846, Integer.Sparse.eval_collectBalanced, rawRowCheck8846]

theorem rawRowCheck8847 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form0 = rawRow8847 := by decide +kernel

theorem rowCheck8847 : row8847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8847 := by decide +kernel

theorem rowEval8847 (x : Key → ℝ) : Integer.Sparse.eval row8847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8847, Integer.Sparse.eval_collectBalanced, rawRowCheck8847]

theorem rawRowCheck8848 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form0 = rawRow8848 := by decide +kernel

theorem rowCheck8848 : row8848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8848 := by decide +kernel

theorem rowEval8848 (x : Key → ℝ) : Integer.Sparse.eval row8848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8848, Integer.Sparse.eval_collectBalanced, rawRowCheck8848]

theorem rawRowCheck8849 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form0 = rawRow8849 := by decide +kernel

theorem rowCheck8849 : row8849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8849 := by decide +kernel

theorem rowEval8849 (x : Key → ℝ) : Integer.Sparse.eval row8849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8849, Integer.Sparse.eval_collectBalanced, rawRowCheck8849]

theorem rawRowCheck8850 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form0 = rawRow8850 := by decide +kernel

theorem rowCheck8850 : row8850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8850 := by decide +kernel

theorem rowEval8850 (x : Key → ℝ) : Integer.Sparse.eval row8850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8850, Integer.Sparse.eval_collectBalanced, rawRowCheck8850]

theorem rawRowCheck8851 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form0 = rawRow8851 := by decide +kernel

theorem rowCheck8851 : row8851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8851 := by decide +kernel

theorem rowEval8851 (x : Key → ℝ) : Integer.Sparse.eval row8851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8851, Integer.Sparse.eval_collectBalanced, rawRowCheck8851]

theorem rawRowCheck8852 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form0 = rawRow8852 := by decide +kernel

theorem rowCheck8852 : row8852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8852 := by decide +kernel

theorem rowEval8852 (x : Key → ℝ) : Integer.Sparse.eval row8852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8852, Integer.Sparse.eval_collectBalanced, rawRowCheck8852]

theorem rawRowCheck8853 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form0 = rawRow8853 := by decide +kernel

theorem rowCheck8853 : row8853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8853 := by decide +kernel

theorem rowEval8853 (x : Key → ℝ) : Integer.Sparse.eval row8853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8853, Integer.Sparse.eval_collectBalanced, rawRowCheck8853]

theorem rawRowCheck8854 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow8854 := by decide +kernel

theorem rowCheck8854 : row8854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8854 := by decide +kernel

theorem rowEval8854 (x : Key → ℝ) : Integer.Sparse.eval row8854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8854, Integer.Sparse.eval_collectBalanced, rawRowCheck8854]

theorem rawRowCheck8855 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow8855 := by decide +kernel

theorem rowCheck8855 : row8855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8855 := by decide +kernel

theorem rowEval8855 (x : Key → ℝ) : Integer.Sparse.eval row8855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8855, Integer.Sparse.eval_collectBalanced, rawRowCheck8855]

theorem rawRowCheck8856 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow8856 := by decide +kernel

theorem rowCheck8856 : row8856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8856 := by decide +kernel

theorem rowEval8856 (x : Key → ℝ) : Integer.Sparse.eval row8856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8856, Integer.Sparse.eval_collectBalanced, rawRowCheck8856]

theorem rawRowCheck8857 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow8857 := by decide +kernel

theorem rowCheck8857 : row8857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8857 := by decide +kernel

theorem rowEval8857 (x : Key → ℝ) : Integer.Sparse.eval row8857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8857, Integer.Sparse.eval_collectBalanced, rawRowCheck8857]

theorem rawRowCheck8858 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow8858 := by decide +kernel

theorem rowCheck8858 : row8858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8858 := by decide +kernel

theorem rowEval8858 (x : Key → ℝ) : Integer.Sparse.eval row8858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8858, Integer.Sparse.eval_collectBalanced, rawRowCheck8858]

theorem rawRowCheck8859 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow8859 := by decide +kernel

theorem rowCheck8859 : row8859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8859 := by decide +kernel

theorem rowEval8859 (x : Key → ℝ) : Integer.Sparse.eval row8859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8859, Integer.Sparse.eval_collectBalanced, rawRowCheck8859]

theorem rawRowCheck8860 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8860 := by decide +kernel

theorem rowCheck8860 : row8860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8860 := by decide +kernel

theorem rowEval8860 (x : Key → ℝ) : Integer.Sparse.eval row8860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8860, Integer.Sparse.eval_collectBalanced, rawRowCheck8860]

theorem rawRowCheck8861 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form1 = rawRow8861 := by decide +kernel

theorem rowCheck8861 : row8861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8861 := by decide +kernel

theorem rowEval8861 (x : Key → ℝ) : Integer.Sparse.eval row8861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8861, Integer.Sparse.eval_collectBalanced, rawRowCheck8861]

theorem rawRowCheck8862 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form1 = rawRow8862 := by decide +kernel

theorem rowCheck8862 : row8862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8862 := by decide +kernel

theorem rowEval8862 (x : Key → ℝ) : Integer.Sparse.eval row8862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8862, Integer.Sparse.eval_collectBalanced, rawRowCheck8862]

theorem rawRowCheck8863 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form1 = rawRow8863 := by decide +kernel

theorem rowCheck8863 : row8863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8863 := by decide +kernel

theorem rowEval8863 (x : Key → ℝ) : Integer.Sparse.eval row8863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8863, Integer.Sparse.eval_collectBalanced, rawRowCheck8863]

theorem rawRowCheck8864 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form1 = rawRow8864 := by decide +kernel

theorem rowCheck8864 : row8864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8864 := by decide +kernel

theorem rowEval8864 (x : Key → ℝ) : Integer.Sparse.eval row8864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8864, Integer.Sparse.eval_collectBalanced, rawRowCheck8864]

theorem rawRowCheck8865 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form1 = rawRow8865 := by decide +kernel

theorem rowCheck8865 : row8865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8865 := by decide +kernel

theorem rowEval8865 (x : Key → ℝ) : Integer.Sparse.eval row8865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8865, Integer.Sparse.eval_collectBalanced, rawRowCheck8865]

theorem rawRowCheck8866 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form1 = rawRow8866 := by decide +kernel

theorem rowCheck8866 : row8866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8866 := by decide +kernel

theorem rowEval8866 (x : Key → ℝ) : Integer.Sparse.eval row8866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8866, Integer.Sparse.eval_collectBalanced, rawRowCheck8866]

theorem rawRowCheck8867 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form1 = rawRow8867 := by decide +kernel

theorem rowCheck8867 : row8867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8867 := by decide +kernel

theorem rowEval8867 (x : Key → ℝ) : Integer.Sparse.eval row8867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8867, Integer.Sparse.eval_collectBalanced, rawRowCheck8867]

theorem rawRowCheck8868 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form1 = rawRow8868 := by decide +kernel

theorem rowCheck8868 : row8868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8868 := by decide +kernel

theorem rowEval8868 (x : Key → ℝ) : Integer.Sparse.eval row8868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8868, Integer.Sparse.eval_collectBalanced, rawRowCheck8868]

theorem rawRowCheck8869 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form1 = rawRow8869 := by decide +kernel

theorem rowCheck8869 : row8869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8869 := by decide +kernel

theorem rowEval8869 (x : Key → ℝ) : Integer.Sparse.eval row8869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8869, Integer.Sparse.eval_collectBalanced, rawRowCheck8869]

theorem rawRowCheck8870 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow8870 := by decide +kernel

theorem rowCheck8870 : row8870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8870 := by decide +kernel

theorem rowEval8870 (x : Key → ℝ) : Integer.Sparse.eval row8870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8870, Integer.Sparse.eval_collectBalanced, rawRowCheck8870]

theorem rawRowCheck8871 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow8871 := by decide +kernel

theorem rowCheck8871 : row8871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8871 := by decide +kernel

theorem rowEval8871 (x : Key → ℝ) : Integer.Sparse.eval row8871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8871, Integer.Sparse.eval_collectBalanced, rawRowCheck8871]

theorem rawRowCheck8872 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow8872 := by decide +kernel

theorem rowCheck8872 : row8872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8872 := by decide +kernel

theorem rowEval8872 (x : Key → ℝ) : Integer.Sparse.eval row8872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8872, Integer.Sparse.eval_collectBalanced, rawRowCheck8872]

theorem rawRowCheck8873 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow8873 := by decide +kernel

theorem rowCheck8873 : row8873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8873 := by decide +kernel

theorem rowEval8873 (x : Key → ℝ) : Integer.Sparse.eval row8873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8873, Integer.Sparse.eval_collectBalanced, rawRowCheck8873]

theorem rawRowCheck8874 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow8874 := by decide +kernel

theorem rowCheck8874 : row8874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8874 := by decide +kernel

theorem rowEval8874 (x : Key → ℝ) : Integer.Sparse.eval row8874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8874, Integer.Sparse.eval_collectBalanced, rawRowCheck8874]

theorem rawRowCheck8875 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow8875 := by decide +kernel

theorem rowCheck8875 : row8875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8875 := by decide +kernel

theorem rowEval8875 (x : Key → ℝ) : Integer.Sparse.eval row8875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8875, Integer.Sparse.eval_collectBalanced, rawRowCheck8875]

theorem rawRowCheck8876 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8876 := by decide +kernel

theorem rowCheck8876 : row8876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8876 := by decide +kernel

theorem rowEval8876 (x : Key → ℝ) : Integer.Sparse.eval row8876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8876, Integer.Sparse.eval_collectBalanced, rawRowCheck8876]

theorem rawRowCheck8877 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form2 = rawRow8877 := by decide +kernel

theorem rowCheck8877 : row8877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8877 := by decide +kernel

theorem rowEval8877 (x : Key → ℝ) : Integer.Sparse.eval row8877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8877, Integer.Sparse.eval_collectBalanced, rawRowCheck8877]

theorem rawRowCheck8878 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form2 = rawRow8878 := by decide +kernel

theorem rowCheck8878 : row8878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8878 := by decide +kernel

theorem rowEval8878 (x : Key → ℝ) : Integer.Sparse.eval row8878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8878, Integer.Sparse.eval_collectBalanced, rawRowCheck8878]

theorem rawRowCheck8879 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form2 = rawRow8879 := by decide +kernel

theorem rowCheck8879 : row8879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8879 := by decide +kernel

theorem rowEval8879 (x : Key → ℝ) : Integer.Sparse.eval row8879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8879, Integer.Sparse.eval_collectBalanced, rawRowCheck8879]

theorem rawRowCheck8880 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form2 = rawRow8880 := by decide +kernel

theorem rowCheck8880 : row8880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8880 := by decide +kernel

theorem rowEval8880 (x : Key → ℝ) : Integer.Sparse.eval row8880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8880, Integer.Sparse.eval_collectBalanced, rawRowCheck8880]

theorem rawRowCheck8881 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form2 = rawRow8881 := by decide +kernel

theorem rowCheck8881 : row8881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8881 := by decide +kernel

theorem rowEval8881 (x : Key → ℝ) : Integer.Sparse.eval row8881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8881, Integer.Sparse.eval_collectBalanced, rawRowCheck8881]

theorem rawRowCheck8882 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form2 = rawRow8882 := by decide +kernel

theorem rowCheck8882 : row8882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8882 := by decide +kernel

theorem rowEval8882 (x : Key → ℝ) : Integer.Sparse.eval row8882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8882, Integer.Sparse.eval_collectBalanced, rawRowCheck8882]

theorem rawRowCheck8883 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form2 = rawRow8883 := by decide +kernel

theorem rowCheck8883 : row8883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8883 := by decide +kernel

theorem rowEval8883 (x : Key → ℝ) : Integer.Sparse.eval row8883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8883, Integer.Sparse.eval_collectBalanced, rawRowCheck8883]

theorem rawRowCheck8884 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form2 = rawRow8884 := by decide +kernel

theorem rowCheck8884 : row8884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8884 := by decide +kernel

theorem rowEval8884 (x : Key → ℝ) : Integer.Sparse.eval row8884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8884, Integer.Sparse.eval_collectBalanced, rawRowCheck8884]

theorem rawRowCheck8885 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form2 = rawRow8885 := by decide +kernel

theorem rowCheck8885 : row8885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8885 := by decide +kernel

theorem rowEval8885 (x : Key → ℝ) : Integer.Sparse.eval row8885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8885, Integer.Sparse.eval_collectBalanced, rawRowCheck8885]

theorem rawRowCheck8886 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow8886 := by decide +kernel

theorem rowCheck8886 : row8886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8886 := by decide +kernel

theorem rowEval8886 (x : Key → ℝ) : Integer.Sparse.eval row8886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8886, Integer.Sparse.eval_collectBalanced, rawRowCheck8886]

theorem rawRowCheck8887 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow8887 := by decide +kernel

theorem rowCheck8887 : row8887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8887 := by decide +kernel

theorem rowEval8887 (x : Key → ℝ) : Integer.Sparse.eval row8887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8887, Integer.Sparse.eval_collectBalanced, rawRowCheck8887]

theorem rawRowCheck8888 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow8888 := by decide +kernel

theorem rowCheck8888 : row8888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8888 := by decide +kernel

theorem rowEval8888 (x : Key → ℝ) : Integer.Sparse.eval row8888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8888, Integer.Sparse.eval_collectBalanced, rawRowCheck8888]

theorem rawRowCheck8889 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow8889 := by decide +kernel

theorem rowCheck8889 : row8889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8889 := by decide +kernel

theorem rowEval8889 (x : Key → ℝ) : Integer.Sparse.eval row8889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8889, Integer.Sparse.eval_collectBalanced, rawRowCheck8889]

theorem rawRowCheck8890 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow8890 := by decide +kernel

theorem rowCheck8890 : row8890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8890 := by decide +kernel

theorem rowEval8890 (x : Key → ℝ) : Integer.Sparse.eval row8890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8890, Integer.Sparse.eval_collectBalanced, rawRowCheck8890]

theorem rawRowCheck8891 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow8891 := by decide +kernel

theorem rowCheck8891 : row8891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8891 := by decide +kernel

theorem rowEval8891 (x : Key → ℝ) : Integer.Sparse.eval row8891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8891, Integer.Sparse.eval_collectBalanced, rawRowCheck8891]

theorem rawRowCheck8892 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8892 := by decide +kernel

theorem rowCheck8892 : row8892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8892 := by decide +kernel

theorem rowEval8892 (x : Key → ℝ) : Integer.Sparse.eval row8892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8892, Integer.Sparse.eval_collectBalanced, rawRowCheck8892]

theorem rawRowCheck8893 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form3 = rawRow8893 := by decide +kernel

theorem rowCheck8893 : row8893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8893 := by decide +kernel

theorem rowEval8893 (x : Key → ℝ) : Integer.Sparse.eval row8893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8893, Integer.Sparse.eval_collectBalanced, rawRowCheck8893]

theorem rawRowCheck8894 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form3 = rawRow8894 := by decide +kernel

theorem rowCheck8894 : row8894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8894 := by decide +kernel

theorem rowEval8894 (x : Key → ℝ) : Integer.Sparse.eval row8894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8894, Integer.Sparse.eval_collectBalanced, rawRowCheck8894]

theorem rawRowCheck8895 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form3 = rawRow8895 := by decide +kernel

theorem rowCheck8895 : row8895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8895 := by decide +kernel

theorem rowEval8895 (x : Key → ℝ) : Integer.Sparse.eval row8895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8895, Integer.Sparse.eval_collectBalanced, rawRowCheck8895]

theorem rawRowCheck8896 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form3 = rawRow8896 := by decide +kernel

theorem rowCheck8896 : row8896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8896 := by decide +kernel

theorem rowEval8896 (x : Key → ℝ) : Integer.Sparse.eval row8896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8896, Integer.Sparse.eval_collectBalanced, rawRowCheck8896]

theorem rawRowCheck8897 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form3 = rawRow8897 := by decide +kernel

theorem rowCheck8897 : row8897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8897 := by decide +kernel

theorem rowEval8897 (x : Key → ℝ) : Integer.Sparse.eval row8897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8897, Integer.Sparse.eval_collectBalanced, rawRowCheck8897]

theorem rawRowCheck8898 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form3 = rawRow8898 := by decide +kernel

theorem rowCheck8898 : row8898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8898 := by decide +kernel

theorem rowEval8898 (x : Key → ℝ) : Integer.Sparse.eval row8898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8898, Integer.Sparse.eval_collectBalanced, rawRowCheck8898]

theorem rawRowCheck8899 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form3 = rawRow8899 := by decide +kernel

theorem rowCheck8899 : row8899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8899 := by decide +kernel

theorem rowEval8899 (x : Key → ℝ) : Integer.Sparse.eval row8899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8899, Integer.Sparse.eval_collectBalanced, rawRowCheck8899]

theorem rawRowCheck8900 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form3 = rawRow8900 := by decide +kernel

theorem rowCheck8900 : row8900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8900 := by decide +kernel

theorem rowEval8900 (x : Key → ℝ) : Integer.Sparse.eval row8900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8900, Integer.Sparse.eval_collectBalanced, rawRowCheck8900]

theorem rawRowCheck8901 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form3 = rawRow8901 := by decide +kernel

theorem rowCheck8901 : row8901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8901 := by decide +kernel

theorem rowEval8901 (x : Key → ℝ) : Integer.Sparse.eval row8901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8901, Integer.Sparse.eval_collectBalanced, rawRowCheck8901]

theorem rawRowCheck8902 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow8902 := by decide +kernel

theorem rowCheck8902 : row8902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8902 := by decide +kernel

theorem rowEval8902 (x : Key → ℝ) : Integer.Sparse.eval row8902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8902, Integer.Sparse.eval_collectBalanced, rawRowCheck8902]

theorem rawRowCheck8903 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow8903 := by decide +kernel

theorem rowCheck8903 : row8903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8903 := by decide +kernel

theorem rowEval8903 (x : Key → ℝ) : Integer.Sparse.eval row8903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8903, Integer.Sparse.eval_collectBalanced, rawRowCheck8903]

theorem rawRowCheck8904 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow8904 := by decide +kernel

theorem rowCheck8904 : row8904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8904 := by decide +kernel

theorem rowEval8904 (x : Key → ℝ) : Integer.Sparse.eval row8904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8904, Integer.Sparse.eval_collectBalanced, rawRowCheck8904]

theorem rawRowCheck8905 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow8905 := by decide +kernel

theorem rowCheck8905 : row8905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8905 := by decide +kernel

theorem rowEval8905 (x : Key → ℝ) : Integer.Sparse.eval row8905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8905, Integer.Sparse.eval_collectBalanced, rawRowCheck8905]

theorem rawRowCheck8906 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow8906 := by decide +kernel

theorem rowCheck8906 : row8906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8906 := by decide +kernel

theorem rowEval8906 (x : Key → ℝ) : Integer.Sparse.eval row8906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8906, Integer.Sparse.eval_collectBalanced, rawRowCheck8906]

theorem rawRowCheck8907 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow8907 := by decide +kernel

theorem rowCheck8907 : row8907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8907 := by decide +kernel

theorem rowEval8907 (x : Key → ℝ) : Integer.Sparse.eval row8907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8907, Integer.Sparse.eval_collectBalanced, rawRowCheck8907]

theorem rawRowCheck8908 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8908 := by decide +kernel

theorem rowCheck8908 : row8908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8908 := by decide +kernel

theorem rowEval8908 (x : Key → ℝ) : Integer.Sparse.eval row8908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8908, Integer.Sparse.eval_collectBalanced, rawRowCheck8908]

theorem rawRowCheck8909 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form4 = rawRow8909 := by decide +kernel

theorem rowCheck8909 : row8909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8909 := by decide +kernel

theorem rowEval8909 (x : Key → ℝ) : Integer.Sparse.eval row8909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8909, Integer.Sparse.eval_collectBalanced, rawRowCheck8909]

theorem rawRowCheck8910 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form4 = rawRow8910 := by decide +kernel

theorem rowCheck8910 : row8910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8910 := by decide +kernel

theorem rowEval8910 (x : Key → ℝ) : Integer.Sparse.eval row8910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8910, Integer.Sparse.eval_collectBalanced, rawRowCheck8910]

theorem rawRowCheck8911 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form4 = rawRow8911 := by decide +kernel

theorem rowCheck8911 : row8911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8911 := by decide +kernel

theorem rowEval8911 (x : Key → ℝ) : Integer.Sparse.eval row8911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8911, Integer.Sparse.eval_collectBalanced, rawRowCheck8911]

theorem rawRowCheck8912 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form4 = rawRow8912 := by decide +kernel

theorem rowCheck8912 : row8912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8912 := by decide +kernel

theorem rowEval8912 (x : Key → ℝ) : Integer.Sparse.eval row8912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8912, Integer.Sparse.eval_collectBalanced, rawRowCheck8912]

theorem rawRowCheck8913 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form4 = rawRow8913 := by decide +kernel

theorem rowCheck8913 : row8913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8913 := by decide +kernel

theorem rowEval8913 (x : Key → ℝ) : Integer.Sparse.eval row8913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8913, Integer.Sparse.eval_collectBalanced, rawRowCheck8913]

theorem rawRowCheck8914 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form4 = rawRow8914 := by decide +kernel

theorem rowCheck8914 : row8914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8914 := by decide +kernel

theorem rowEval8914 (x : Key → ℝ) : Integer.Sparse.eval row8914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8914, Integer.Sparse.eval_collectBalanced, rawRowCheck8914]

theorem rawRowCheck8915 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form4 = rawRow8915 := by decide +kernel

theorem rowCheck8915 : row8915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8915 := by decide +kernel

theorem rowEval8915 (x : Key → ℝ) : Integer.Sparse.eval row8915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8915, Integer.Sparse.eval_collectBalanced, rawRowCheck8915]

theorem rawRowCheck8916 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form4 = rawRow8916 := by decide +kernel

theorem rowCheck8916 : row8916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8916 := by decide +kernel

theorem rowEval8916 (x : Key → ℝ) : Integer.Sparse.eval row8916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8916, Integer.Sparse.eval_collectBalanced, rawRowCheck8916]

theorem rawRowCheck8917 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form4 = rawRow8917 := by decide +kernel

theorem rowCheck8917 : row8917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8917 := by decide +kernel

theorem rowEval8917 (x : Key → ℝ) : Integer.Sparse.eval row8917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8917, Integer.Sparse.eval_collectBalanced, rawRowCheck8917]

theorem rawRowCheck8918 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow8918 := by decide +kernel

theorem rowCheck8918 : row8918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8918 := by decide +kernel

theorem rowEval8918 (x : Key → ℝ) : Integer.Sparse.eval row8918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8918, Integer.Sparse.eval_collectBalanced, rawRowCheck8918]

theorem rawRowCheck8919 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow8919 := by decide +kernel

theorem rowCheck8919 : row8919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8919 := by decide +kernel

theorem rowEval8919 (x : Key → ℝ) : Integer.Sparse.eval row8919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8919, Integer.Sparse.eval_collectBalanced, rawRowCheck8919]

theorem rawRowCheck8920 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow8920 := by decide +kernel

theorem rowCheck8920 : row8920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8920 := by decide +kernel

theorem rowEval8920 (x : Key → ℝ) : Integer.Sparse.eval row8920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8920, Integer.Sparse.eval_collectBalanced, rawRowCheck8920]

theorem rawRowCheck8921 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form5 = rawRow8921 := by decide +kernel

theorem rowCheck8921 : row8921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8921 := by decide +kernel

theorem rowEval8921 (x : Key → ℝ) : Integer.Sparse.eval row8921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8921, Integer.Sparse.eval_collectBalanced, rawRowCheck8921]

theorem rawRowCheck8922 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form5 = rawRow8922 := by decide +kernel

theorem rowCheck8922 : row8922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8922 := by decide +kernel

theorem rowEval8922 (x : Key → ℝ) : Integer.Sparse.eval row8922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8922, Integer.Sparse.eval_collectBalanced, rawRowCheck8922]

theorem rawRowCheck8923 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form5 = rawRow8923 := by decide +kernel

theorem rowCheck8923 : row8923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8923 := by decide +kernel

theorem rowEval8923 (x : Key → ℝ) : Integer.Sparse.eval row8923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8923, Integer.Sparse.eval_collectBalanced, rawRowCheck8923]

theorem rawRowCheck8924 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8924 := by decide +kernel

theorem rowCheck8924 : row8924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8924 := by decide +kernel

theorem rowEval8924 (x : Key → ℝ) : Integer.Sparse.eval row8924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8924, Integer.Sparse.eval_collectBalanced, rawRowCheck8924]

theorem rawRowCheck8925 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form5 = rawRow8925 := by decide +kernel

theorem rowCheck8925 : row8925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8925 := by decide +kernel

theorem rowEval8925 (x : Key → ℝ) : Integer.Sparse.eval row8925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8925, Integer.Sparse.eval_collectBalanced, rawRowCheck8925]

theorem rawRowCheck8926 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form5 = rawRow8926 := by decide +kernel

theorem rowCheck8926 : row8926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8926 := by decide +kernel

theorem rowEval8926 (x : Key → ℝ) : Integer.Sparse.eval row8926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8926, Integer.Sparse.eval_collectBalanced, rawRowCheck8926]

theorem rawRowCheck8927 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form5 = rawRow8927 := by decide +kernel

theorem rowCheck8927 : row8927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8927 := by decide +kernel

theorem rowEval8927 (x : Key → ℝ) : Integer.Sparse.eval row8927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8927, Integer.Sparse.eval_collectBalanced, rawRowCheck8927]

theorem rawRowCheck8928 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form5 = rawRow8928 := by decide +kernel

theorem rowCheck8928 : row8928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8928 := by decide +kernel

theorem rowEval8928 (x : Key → ℝ) : Integer.Sparse.eval row8928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8928, Integer.Sparse.eval_collectBalanced, rawRowCheck8928]

theorem rawRowCheck8929 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form5 = rawRow8929 := by decide +kernel

theorem rowCheck8929 : row8929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8929 := by decide +kernel

theorem rowEval8929 (x : Key → ℝ) : Integer.Sparse.eval row8929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8929, Integer.Sparse.eval_collectBalanced, rawRowCheck8929]

theorem rawRowCheck8930 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form5 = rawRow8930 := by decide +kernel

theorem rowCheck8930 : row8930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8930 := by decide +kernel

theorem rowEval8930 (x : Key → ℝ) : Integer.Sparse.eval row8930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8930, Integer.Sparse.eval_collectBalanced, rawRowCheck8930]

theorem rawRowCheck8931 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form5 = rawRow8931 := by decide +kernel

theorem rowCheck8931 : row8931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8931 := by decide +kernel

theorem rowEval8931 (x : Key → ℝ) : Integer.Sparse.eval row8931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8931, Integer.Sparse.eval_collectBalanced, rawRowCheck8931]

theorem rawRowCheck8932 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form5 = rawRow8932 := by decide +kernel

theorem rowCheck8932 : row8932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8932 := by decide +kernel

theorem rowEval8932 (x : Key → ℝ) : Integer.Sparse.eval row8932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8932, Integer.Sparse.eval_collectBalanced, rawRowCheck8932]

theorem rawRowCheck8933 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form5 = rawRow8933 := by decide +kernel

theorem rowCheck8933 : row8933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8933 := by decide +kernel

theorem rowEval8933 (x : Key → ℝ) : Integer.Sparse.eval row8933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8933, Integer.Sparse.eval_collectBalanced, rawRowCheck8933]

theorem rawRowCheck8934 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form5 = rawRow8934 := by decide +kernel

theorem rowCheck8934 : row8934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8934 := by decide +kernel

theorem rowEval8934 (x : Key → ℝ) : Integer.Sparse.eval row8934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8934, Integer.Sparse.eval_collectBalanced, rawRowCheck8934]

theorem rawRowCheck8935 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form5 = rawRow8935 := by decide +kernel

theorem rowCheck8935 : row8935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8935 := by decide +kernel

theorem rowEval8935 (x : Key → ℝ) : Integer.Sparse.eval row8935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8935, Integer.Sparse.eval_collectBalanced, rawRowCheck8935]

theorem rawRowCheck8936 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form5 = rawRow8936 := by decide +kernel

theorem rowCheck8936 : row8936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8936 := by decide +kernel

theorem rowEval8936 (x : Key → ℝ) : Integer.Sparse.eval row8936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8936, Integer.Sparse.eval_collectBalanced, rawRowCheck8936]

theorem rawRowCheck8937 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8937 := by decide +kernel

theorem rowCheck8937 : row8937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8937 := by decide +kernel

theorem rowEval8937 (x : Key → ℝ) : Integer.Sparse.eval row8937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8937, Integer.Sparse.eval_collectBalanced, rawRowCheck8937]

theorem rawRowCheck8938 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8938 := by decide +kernel

theorem rowCheck8938 : row8938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8938 := by decide +kernel

theorem rowEval8938 (x : Key → ℝ) : Integer.Sparse.eval row8938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8938, Integer.Sparse.eval_collectBalanced, rawRowCheck8938]

theorem rawRowCheck8939 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8939 := by decide +kernel

theorem rowCheck8939 : row8939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8939 := by decide +kernel

theorem rowEval8939 (x : Key → ℝ) : Integer.Sparse.eval row8939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8939, Integer.Sparse.eval_collectBalanced, rawRowCheck8939]

theorem rawRowCheck8940 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8940 := by decide +kernel

theorem rowCheck8940 : row8940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8940 := by decide +kernel

theorem rowEval8940 (x : Key → ℝ) : Integer.Sparse.eval row8940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8940, Integer.Sparse.eval_collectBalanced, rawRowCheck8940]

theorem rawRowCheck8941 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8941 := by decide +kernel

theorem rowCheck8941 : row8941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8941 := by decide +kernel

theorem rowEval8941 (x : Key → ℝ) : Integer.Sparse.eval row8941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8941, Integer.Sparse.eval_collectBalanced, rawRowCheck8941]

theorem rawRowCheck8942 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8942 := by decide +kernel

theorem rowCheck8942 : row8942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8942 := by decide +kernel

theorem rowEval8942 (x : Key → ℝ) : Integer.Sparse.eval row8942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8942, Integer.Sparse.eval_collectBalanced, rawRowCheck8942]

theorem rawRowCheck8943 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8943 := by decide +kernel

theorem rowCheck8943 : row8943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8943 := by decide +kernel

theorem rowEval8943 (x : Key → ℝ) : Integer.Sparse.eval row8943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8943, Integer.Sparse.eval_collectBalanced, rawRowCheck8943]

theorem rawRowCheck8944 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form6 = rawRow8944 := by decide +kernel

theorem rowCheck8944 : row8944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8944 := by decide +kernel

theorem rowEval8944 (x : Key → ℝ) : Integer.Sparse.eval row8944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8944, Integer.Sparse.eval_collectBalanced, rawRowCheck8944]

theorem rawRowCheck8945 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form6 = rawRow8945 := by decide +kernel

theorem rowCheck8945 : row8945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8945 := by decide +kernel

theorem rowEval8945 (x : Key → ℝ) : Integer.Sparse.eval row8945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8945, Integer.Sparse.eval_collectBalanced, rawRowCheck8945]

theorem rawRowCheck8946 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form6 = rawRow8946 := by decide +kernel

theorem rowCheck8946 : row8946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8946 := by decide +kernel

theorem rowEval8946 (x : Key → ℝ) : Integer.Sparse.eval row8946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8946, Integer.Sparse.eval_collectBalanced, rawRowCheck8946]

theorem rawRowCheck8947 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form6 = rawRow8947 := by decide +kernel

theorem rowCheck8947 : row8947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8947 := by decide +kernel

theorem rowEval8947 (x : Key → ℝ) : Integer.Sparse.eval row8947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8947, Integer.Sparse.eval_collectBalanced, rawRowCheck8947]

theorem rawRowCheck8948 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form6 = rawRow8948 := by decide +kernel

theorem rowCheck8948 : row8948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8948 := by decide +kernel

theorem rowEval8948 (x : Key → ℝ) : Integer.Sparse.eval row8948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8948, Integer.Sparse.eval_collectBalanced, rawRowCheck8948]

theorem rawRowCheck8949 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form6 = rawRow8949 := by decide +kernel

theorem rowCheck8949 : row8949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8949 := by decide +kernel

theorem rowEval8949 (x : Key → ℝ) : Integer.Sparse.eval row8949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8949, Integer.Sparse.eval_collectBalanced, rawRowCheck8949]

theorem rawRowCheck8950 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow8950 := by decide +kernel

theorem rowCheck8950 : row8950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8950 := by decide +kernel

theorem rowEval8950 (x : Key → ℝ) : Integer.Sparse.eval row8950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8950, Integer.Sparse.eval_collectBalanced, rawRowCheck8950]

theorem rawRowCheck8951 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow8951 := by decide +kernel

theorem rowCheck8951 : row8951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8951 := by decide +kernel

theorem rowEval8951 (x : Key → ℝ) : Integer.Sparse.eval row8951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8951, Integer.Sparse.eval_collectBalanced, rawRowCheck8951]

theorem rawRowCheck8952 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow8952 := by decide +kernel

theorem rowCheck8952 : row8952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8952 := by decide +kernel

theorem rowEval8952 (x : Key → ℝ) : Integer.Sparse.eval row8952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8952, Integer.Sparse.eval_collectBalanced, rawRowCheck8952]

theorem rawRowCheck8953 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8953 := by decide +kernel

theorem rowCheck8953 : row8953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8953 := by decide +kernel

theorem rowEval8953 (x : Key → ℝ) : Integer.Sparse.eval row8953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8953, Integer.Sparse.eval_collectBalanced, rawRowCheck8953]

theorem rawRowCheck8954 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8954 := by decide +kernel

theorem rowCheck8954 : row8954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8954 := by decide +kernel

theorem rowEval8954 (x : Key → ℝ) : Integer.Sparse.eval row8954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8954, Integer.Sparse.eval_collectBalanced, rawRowCheck8954]

theorem rawRowCheck8955 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8955 := by decide +kernel

theorem rowCheck8955 : row8955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8955 := by decide +kernel

theorem rowEval8955 (x : Key → ℝ) : Integer.Sparse.eval row8955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8955, Integer.Sparse.eval_collectBalanced, rawRowCheck8955]

theorem rawRowCheck8956 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8956 := by decide +kernel

theorem rowCheck8956 : row8956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8956 := by decide +kernel

theorem rowEval8956 (x : Key → ℝ) : Integer.Sparse.eval row8956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8956, Integer.Sparse.eval_collectBalanced, rawRowCheck8956]

theorem rawRowCheck8957 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8957 := by decide +kernel

theorem rowCheck8957 : row8957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8957 := by decide +kernel

theorem rowEval8957 (x : Key → ℝ) : Integer.Sparse.eval row8957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8957, Integer.Sparse.eval_collectBalanced, rawRowCheck8957]

theorem rawRowCheck8958 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8958 := by decide +kernel

theorem rowCheck8958 : row8958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8958 := by decide +kernel

theorem rowEval8958 (x : Key → ℝ) : Integer.Sparse.eval row8958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8958, Integer.Sparse.eval_collectBalanced, rawRowCheck8958]

theorem rawRowCheck8959 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8959 := by decide +kernel

theorem rowCheck8959 : row8959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8959 := by decide +kernel

theorem rowEval8959 (x : Key → ℝ) : Integer.Sparse.eval row8959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8959, Integer.Sparse.eval_collectBalanced, rawRowCheck8959]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8960 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form7 = rawRow8960 := by decide +kernel

theorem rowCheck8960 : row8960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8960 := by decide +kernel

theorem rowEval8960 (x : Key → ℝ) : Integer.Sparse.eval row8960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8960, Integer.Sparse.eval_collectBalanced, rawRowCheck8960]

theorem rawRowCheck8961 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form7 = rawRow8961 := by decide +kernel

theorem rowCheck8961 : row8961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8961 := by decide +kernel

theorem rowEval8961 (x : Key → ℝ) : Integer.Sparse.eval row8961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8961, Integer.Sparse.eval_collectBalanced, rawRowCheck8961]

theorem rawRowCheck8962 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form7 = rawRow8962 := by decide +kernel

theorem rowCheck8962 : row8962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8962 := by decide +kernel

theorem rowEval8962 (x : Key → ℝ) : Integer.Sparse.eval row8962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8962, Integer.Sparse.eval_collectBalanced, rawRowCheck8962]

theorem rawRowCheck8963 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form7 = rawRow8963 := by decide +kernel

theorem rowCheck8963 : row8963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8963 := by decide +kernel

theorem rowEval8963 (x : Key → ℝ) : Integer.Sparse.eval row8963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8963, Integer.Sparse.eval_collectBalanced, rawRowCheck8963]

theorem rawRowCheck8964 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form7 = rawRow8964 := by decide +kernel

theorem rowCheck8964 : row8964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8964 := by decide +kernel

theorem rowEval8964 (x : Key → ℝ) : Integer.Sparse.eval row8964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8964, Integer.Sparse.eval_collectBalanced, rawRowCheck8964]

theorem rawRowCheck8965 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form7 = rawRow8965 := by decide +kernel

theorem rowCheck8965 : row8965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8965 := by decide +kernel

theorem rowEval8965 (x : Key → ℝ) : Integer.Sparse.eval row8965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8965, Integer.Sparse.eval_collectBalanced, rawRowCheck8965]

theorem rawRowCheck8966 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow8966 := by decide +kernel

theorem rowCheck8966 : row8966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8966 := by decide +kernel

theorem rowEval8966 (x : Key → ℝ) : Integer.Sparse.eval row8966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8966, Integer.Sparse.eval_collectBalanced, rawRowCheck8966]

theorem rawRowCheck8967 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow8967 := by decide +kernel

theorem rowCheck8967 : row8967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8967 := by decide +kernel

theorem rowEval8967 (x : Key → ℝ) : Integer.Sparse.eval row8967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8967, Integer.Sparse.eval_collectBalanced, rawRowCheck8967]

theorem rawRowCheck8968 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow8968 := by decide +kernel

theorem rowCheck8968 : row8968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8968 := by decide +kernel

theorem rowEval8968 (x : Key → ℝ) : Integer.Sparse.eval row8968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8968, Integer.Sparse.eval_collectBalanced, rawRowCheck8968]

theorem rawRowCheck8969 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form8 = rawRow8969 := by decide +kernel

theorem rowCheck8969 : row8969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8969 := by decide +kernel

theorem rowEval8969 (x : Key → ℝ) : Integer.Sparse.eval row8969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8969, Integer.Sparse.eval_collectBalanced, rawRowCheck8969]

theorem rawRowCheck8970 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form8 = rawRow8970 := by decide +kernel

theorem rowCheck8970 : row8970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8970 := by decide +kernel

theorem rowEval8970 (x : Key → ℝ) : Integer.Sparse.eval row8970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8970, Integer.Sparse.eval_collectBalanced, rawRowCheck8970]

theorem rawRowCheck8971 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form8 = rawRow8971 := by decide +kernel

theorem rowCheck8971 : row8971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8971 := by decide +kernel

theorem rowEval8971 (x : Key → ℝ) : Integer.Sparse.eval row8971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8971, Integer.Sparse.eval_collectBalanced, rawRowCheck8971]

theorem rawRowCheck8972 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8972 := by decide +kernel

theorem rowCheck8972 : row8972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8972 := by decide +kernel

theorem rowEval8972 (x : Key → ℝ) : Integer.Sparse.eval row8972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8972, Integer.Sparse.eval_collectBalanced, rawRowCheck8972]

theorem rawRowCheck8973 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form8 = rawRow8973 := by decide +kernel

theorem rowCheck8973 : row8973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8973 := by decide +kernel

theorem rowEval8973 (x : Key → ℝ) : Integer.Sparse.eval row8973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8973, Integer.Sparse.eval_collectBalanced, rawRowCheck8973]

theorem rawRowCheck8974 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form8 = rawRow8974 := by decide +kernel

theorem rowCheck8974 : row8974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8974 := by decide +kernel

theorem rowEval8974 (x : Key → ℝ) : Integer.Sparse.eval row8974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8974, Integer.Sparse.eval_collectBalanced, rawRowCheck8974]

theorem rawRowCheck8975 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form8 = rawRow8975 := by decide +kernel

theorem rowCheck8975 : row8975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8975 := by decide +kernel

theorem rowEval8975 (x : Key → ℝ) : Integer.Sparse.eval row8975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8975, Integer.Sparse.eval_collectBalanced, rawRowCheck8975]

theorem rawRowCheck8976 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form8 = rawRow8976 := by decide +kernel

theorem rowCheck8976 : row8976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8976 := by decide +kernel

theorem rowEval8976 (x : Key → ℝ) : Integer.Sparse.eval row8976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8976, Integer.Sparse.eval_collectBalanced, rawRowCheck8976]

theorem rawRowCheck8977 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form8 = rawRow8977 := by decide +kernel

theorem rowCheck8977 : row8977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8977 := by decide +kernel

theorem rowEval8977 (x : Key → ℝ) : Integer.Sparse.eval row8977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8977, Integer.Sparse.eval_collectBalanced, rawRowCheck8977]

theorem rawRowCheck8978 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form8 = rawRow8978 := by decide +kernel

theorem rowCheck8978 : row8978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8978 := by decide +kernel

theorem rowEval8978 (x : Key → ℝ) : Integer.Sparse.eval row8978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8978, Integer.Sparse.eval_collectBalanced, rawRowCheck8978]

theorem rawRowCheck8979 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form8 = rawRow8979 := by decide +kernel

theorem rowCheck8979 : row8979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8979 := by decide +kernel

theorem rowEval8979 (x : Key → ℝ) : Integer.Sparse.eval row8979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8979, Integer.Sparse.eval_collectBalanced, rawRowCheck8979]

theorem rawRowCheck8980 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form8 = rawRow8980 := by decide +kernel

theorem rowCheck8980 : row8980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8980 := by decide +kernel

theorem rowEval8980 (x : Key → ℝ) : Integer.Sparse.eval row8980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8980, Integer.Sparse.eval_collectBalanced, rawRowCheck8980]

theorem rawRowCheck8981 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form8 = rawRow8981 := by decide +kernel

theorem rowCheck8981 : row8981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8981 := by decide +kernel

theorem rowEval8981 (x : Key → ℝ) : Integer.Sparse.eval row8981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8981, Integer.Sparse.eval_collectBalanced, rawRowCheck8981]

theorem rawRowCheck8982 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form8 = rawRow8982 := by decide +kernel

theorem rowCheck8982 : row8982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8982 := by decide +kernel

theorem rowEval8982 (x : Key → ℝ) : Integer.Sparse.eval row8982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8982, Integer.Sparse.eval_collectBalanced, rawRowCheck8982]

theorem rawRowCheck8983 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form8 = rawRow8983 := by decide +kernel

theorem rowCheck8983 : row8983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8983 := by decide +kernel

theorem rowEval8983 (x : Key → ℝ) : Integer.Sparse.eval row8983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8983, Integer.Sparse.eval_collectBalanced, rawRowCheck8983]

theorem rawRowCheck8984 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form8 = rawRow8984 := by decide +kernel

theorem rowCheck8984 : row8984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8984 := by decide +kernel

theorem rowEval8984 (x : Key → ℝ) : Integer.Sparse.eval row8984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8984, Integer.Sparse.eval_collectBalanced, rawRowCheck8984]

theorem rawRowCheck9001 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow9001 := by decide +kernel

theorem rowCheck9001 : row9001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9001 := by decide +kernel

theorem rowEval9001 (x : Key → ℝ) : Integer.Sparse.eval row9001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9001, Integer.Sparse.eval_collectBalanced, rawRowCheck9001]

theorem rawRowCheck9002 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow9002 := by decide +kernel

theorem rowCheck9002 : row9002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9002 := by decide +kernel

theorem rowEval9002 (x : Key → ℝ) : Integer.Sparse.eval row9002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9002, Integer.Sparse.eval_collectBalanced, rawRowCheck9002]

theorem rawRowCheck9003 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow9003 := by decide +kernel

theorem rowCheck9003 : row9003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9003 := by decide +kernel

theorem rowEval9003 (x : Key → ℝ) : Integer.Sparse.eval row9003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9003, Integer.Sparse.eval_collectBalanced, rawRowCheck9003]

theorem rawRowCheck9004 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9004 := by decide +kernel

theorem rowCheck9004 : row9004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9004 := by decide +kernel

theorem rowEval9004 (x : Key → ℝ) : Integer.Sparse.eval row9004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9004, Integer.Sparse.eval_collectBalanced, rawRowCheck9004]

theorem rawRowCheck9005 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form10 = rawRow9005 := by decide +kernel

theorem rowCheck9005 : row9005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9005 := by decide +kernel

theorem rowEval9005 (x : Key → ℝ) : Integer.Sparse.eval row9005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9005, Integer.Sparse.eval_collectBalanced, rawRowCheck9005]

theorem rawRowCheck9006 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form10 = rawRow9006 := by decide +kernel

theorem rowCheck9006 : row9006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9006 := by decide +kernel

theorem rowEval9006 (x : Key → ℝ) : Integer.Sparse.eval row9006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9006, Integer.Sparse.eval_collectBalanced, rawRowCheck9006]

theorem rawRowCheck9007 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form10 = rawRow9007 := by decide +kernel

theorem rowCheck9007 : row9007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9007 := by decide +kernel

theorem rowEval9007 (x : Key → ℝ) : Integer.Sparse.eval row9007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9007, Integer.Sparse.eval_collectBalanced, rawRowCheck9007]

theorem rawRowCheck9008 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form10 = rawRow9008 := by decide +kernel

theorem rowCheck9008 : row9008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9008 := by decide +kernel

theorem rowEval9008 (x : Key → ℝ) : Integer.Sparse.eval row9008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9008, Integer.Sparse.eval_collectBalanced, rawRowCheck9008]

theorem rawRowCheck9009 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form10 = rawRow9009 := by decide +kernel

theorem rowCheck9009 : row9009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9009 := by decide +kernel

theorem rowEval9009 (x : Key → ℝ) : Integer.Sparse.eval row9009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9009, Integer.Sparse.eval_collectBalanced, rawRowCheck9009]

theorem rawRowCheck9010 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form10 = rawRow9010 := by decide +kernel

theorem rowCheck9010 : row9010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9010 := by decide +kernel

theorem rowEval9010 (x : Key → ℝ) : Integer.Sparse.eval row9010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9010, Integer.Sparse.eval_collectBalanced, rawRowCheck9010]

theorem rawRowCheck9011 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form10 = rawRow9011 := by decide +kernel

theorem rowCheck9011 : row9011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9011 := by decide +kernel

theorem rowEval9011 (x : Key → ℝ) : Integer.Sparse.eval row9011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9011, Integer.Sparse.eval_collectBalanced, rawRowCheck9011]

theorem rawRowCheck9012 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form10 = rawRow9012 := by decide +kernel

theorem rowCheck9012 : row9012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9012 := by decide +kernel

theorem rowEval9012 (x : Key → ℝ) : Integer.Sparse.eval row9012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9012, Integer.Sparse.eval_collectBalanced, rawRowCheck9012]

theorem rawRowCheck9013 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form10 = rawRow9013 := by decide +kernel

theorem rowCheck9013 : row9013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9013 := by decide +kernel

theorem rowEval9013 (x : Key → ℝ) : Integer.Sparse.eval row9013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9013, Integer.Sparse.eval_collectBalanced, rawRowCheck9013]

theorem rawRowCheck9014 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form10 = rawRow9014 := by decide +kernel

theorem rowCheck9014 : row9014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9014 := by decide +kernel

theorem rowEval9014 (x : Key → ℝ) : Integer.Sparse.eval row9014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9014, Integer.Sparse.eval_collectBalanced, rawRowCheck9014]

theorem rawRowCheck9015 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form10 = rawRow9015 := by decide +kernel

theorem rowCheck9015 : row9015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9015 := by decide +kernel

theorem rowEval9015 (x : Key → ℝ) : Integer.Sparse.eval row9015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9015, Integer.Sparse.eval_collectBalanced, rawRowCheck9015]

theorem rawRowCheck9016 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form10 = rawRow9016 := by decide +kernel

theorem rowCheck9016 : row9016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9016 := by decide +kernel

theorem rowEval9016 (x : Key → ℝ) : Integer.Sparse.eval row9016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9016, Integer.Sparse.eval_collectBalanced, rawRowCheck9016]

theorem rawRowCheck9017 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow9017 := by decide +kernel

theorem rowCheck9017 : row9017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9017 := by decide +kernel

theorem rowEval9017 (x : Key → ℝ) : Integer.Sparse.eval row9017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9017, Integer.Sparse.eval_collectBalanced, rawRowCheck9017]

theorem rawRowCheck9018 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow9018 := by decide +kernel

theorem rowCheck9018 : row9018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9018 := by decide +kernel

theorem rowEval9018 (x : Key → ℝ) : Integer.Sparse.eval row9018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9018, Integer.Sparse.eval_collectBalanced, rawRowCheck9018]

theorem rawRowCheck9019 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow9019 := by decide +kernel

theorem rowCheck9019 : row9019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9019 := by decide +kernel

theorem rowEval9019 (x : Key → ℝ) : Integer.Sparse.eval row9019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9019, Integer.Sparse.eval_collectBalanced, rawRowCheck9019]

theorem rawRowCheck9020 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9020 := by decide +kernel

theorem rowCheck9020 : row9020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9020 := by decide +kernel

theorem rowEval9020 (x : Key → ℝ) : Integer.Sparse.eval row9020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9020, Integer.Sparse.eval_collectBalanced, rawRowCheck9020]

theorem rawRowCheck9021 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form11 = rawRow9021 := by decide +kernel

theorem rowCheck9021 : row9021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9021 := by decide +kernel

theorem rowEval9021 (x : Key → ℝ) : Integer.Sparse.eval row9021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9021, Integer.Sparse.eval_collectBalanced, rawRowCheck9021]

theorem rawRowCheck9022 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form11 = rawRow9022 := by decide +kernel

theorem rowCheck9022 : row9022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9022 := by decide +kernel

theorem rowEval9022 (x : Key → ℝ) : Integer.Sparse.eval row9022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9022, Integer.Sparse.eval_collectBalanced, rawRowCheck9022]

theorem rawRowCheck9023 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form11 = rawRow9023 := by decide +kernel

theorem rowCheck9023 : row9023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9023 := by decide +kernel

theorem rowEval9023 (x : Key → ℝ) : Integer.Sparse.eval row9023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9023, Integer.Sparse.eval_collectBalanced, rawRowCheck9023]

theorem rawRowCheck9024 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form11 = rawRow9024 := by decide +kernel

theorem rowCheck9024 : row9024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9024 := by decide +kernel

theorem rowEval9024 (x : Key → ℝ) : Integer.Sparse.eval row9024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9024, Integer.Sparse.eval_collectBalanced, rawRowCheck9024]

theorem rawRowCheck9025 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form11 = rawRow9025 := by decide +kernel

theorem rowCheck9025 : row9025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9025 := by decide +kernel

theorem rowEval9025 (x : Key → ℝ) : Integer.Sparse.eval row9025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9025, Integer.Sparse.eval_collectBalanced, rawRowCheck9025]

theorem rawRowCheck9026 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form11 = rawRow9026 := by decide +kernel

theorem rowCheck9026 : row9026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9026 := by decide +kernel

theorem rowEval9026 (x : Key → ℝ) : Integer.Sparse.eval row9026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9026, Integer.Sparse.eval_collectBalanced, rawRowCheck9026]

theorem rawRowCheck9027 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form11 = rawRow9027 := by decide +kernel

theorem rowCheck9027 : row9027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9027 := by decide +kernel

theorem rowEval9027 (x : Key → ℝ) : Integer.Sparse.eval row9027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9027, Integer.Sparse.eval_collectBalanced, rawRowCheck9027]

theorem rawRowCheck9028 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form11 = rawRow9028 := by decide +kernel

theorem rowCheck9028 : row9028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9028 := by decide +kernel

theorem rowEval9028 (x : Key → ℝ) : Integer.Sparse.eval row9028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9028, Integer.Sparse.eval_collectBalanced, rawRowCheck9028]

theorem rawRowCheck9029 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form11 = rawRow9029 := by decide +kernel

theorem rowCheck9029 : row9029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9029 := by decide +kernel

theorem rowEval9029 (x : Key → ℝ) : Integer.Sparse.eval row9029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9029, Integer.Sparse.eval_collectBalanced, rawRowCheck9029]

theorem rawRowCheck9030 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form11 = rawRow9030 := by decide +kernel

theorem rowCheck9030 : row9030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9030 := by decide +kernel

theorem rowEval9030 (x : Key → ℝ) : Integer.Sparse.eval row9030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9030, Integer.Sparse.eval_collectBalanced, rawRowCheck9030]

theorem rawRowCheck9031 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form11 = rawRow9031 := by decide +kernel

theorem rowCheck9031 : row9031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9031 := by decide +kernel

theorem rowEval9031 (x : Key → ℝ) : Integer.Sparse.eval row9031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9031, Integer.Sparse.eval_collectBalanced, rawRowCheck9031]

theorem rawRowCheck9032 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form11 = rawRow9032 := by decide +kernel

theorem rowCheck9032 : row9032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9032 := by decide +kernel

theorem rowEval9032 (x : Key → ℝ) : Integer.Sparse.eval row9032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9032, Integer.Sparse.eval_collectBalanced, rawRowCheck9032]

theorem rawRowCheck9033 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow9033 := by decide +kernel

theorem rowCheck9033 : row9033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9033 := by decide +kernel

theorem rowEval9033 (x : Key → ℝ) : Integer.Sparse.eval row9033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9033, Integer.Sparse.eval_collectBalanced, rawRowCheck9033]

theorem rawRowCheck9034 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow9034 := by decide +kernel

theorem rowCheck9034 : row9034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9034 := by decide +kernel

theorem rowEval9034 (x : Key → ℝ) : Integer.Sparse.eval row9034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9034, Integer.Sparse.eval_collectBalanced, rawRowCheck9034]

theorem rawRowCheck9035 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow9035 := by decide +kernel

theorem rowCheck9035 : row9035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9035 := by decide +kernel

theorem rowEval9035 (x : Key → ℝ) : Integer.Sparse.eval row9035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9035, Integer.Sparse.eval_collectBalanced, rawRowCheck9035]

theorem rawRowCheck9036 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9036 := by decide +kernel

theorem rowCheck9036 : row9036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9036 := by decide +kernel

theorem rowEval9036 (x : Key → ℝ) : Integer.Sparse.eval row9036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9036, Integer.Sparse.eval_collectBalanced, rawRowCheck9036]

theorem rawRowCheck9037 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form12 = rawRow9037 := by decide +kernel

theorem rowCheck9037 : row9037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9037 := by decide +kernel

theorem rowEval9037 (x : Key → ℝ) : Integer.Sparse.eval row9037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9037, Integer.Sparse.eval_collectBalanced, rawRowCheck9037]

theorem rawRowCheck9038 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form12 = rawRow9038 := by decide +kernel

theorem rowCheck9038 : row9038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9038 := by decide +kernel

theorem rowEval9038 (x : Key → ℝ) : Integer.Sparse.eval row9038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9038, Integer.Sparse.eval_collectBalanced, rawRowCheck9038]

theorem rawRowCheck9039 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form12 = rawRow9039 := by decide +kernel

theorem rowCheck9039 : row9039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9039 := by decide +kernel

theorem rowEval9039 (x : Key → ℝ) : Integer.Sparse.eval row9039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9039, Integer.Sparse.eval_collectBalanced, rawRowCheck9039]

theorem rawRowCheck9040 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form12 = rawRow9040 := by decide +kernel

theorem rowCheck9040 : row9040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9040 := by decide +kernel

theorem rowEval9040 (x : Key → ℝ) : Integer.Sparse.eval row9040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9040, Integer.Sparse.eval_collectBalanced, rawRowCheck9040]

theorem rawRowCheck9041 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form12 = rawRow9041 := by decide +kernel

theorem rowCheck9041 : row9041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9041 := by decide +kernel

theorem rowEval9041 (x : Key → ℝ) : Integer.Sparse.eval row9041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9041, Integer.Sparse.eval_collectBalanced, rawRowCheck9041]

theorem rawRowCheck9042 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form12 = rawRow9042 := by decide +kernel

theorem rowCheck9042 : row9042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9042 := by decide +kernel

theorem rowEval9042 (x : Key → ℝ) : Integer.Sparse.eval row9042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9042, Integer.Sparse.eval_collectBalanced, rawRowCheck9042]

theorem rawRowCheck9043 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form12 = rawRow9043 := by decide +kernel

theorem rowCheck9043 : row9043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9043 := by decide +kernel

theorem rowEval9043 (x : Key → ℝ) : Integer.Sparse.eval row9043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9043, Integer.Sparse.eval_collectBalanced, rawRowCheck9043]

theorem rawRowCheck9044 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form12 = rawRow9044 := by decide +kernel

theorem rowCheck9044 : row9044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9044 := by decide +kernel

theorem rowEval9044 (x : Key → ℝ) : Integer.Sparse.eval row9044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9044, Integer.Sparse.eval_collectBalanced, rawRowCheck9044]

theorem rawRowCheck9045 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form12 = rawRow9045 := by decide +kernel

theorem rowCheck9045 : row9045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9045 := by decide +kernel

theorem rowEval9045 (x : Key → ℝ) : Integer.Sparse.eval row9045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9045, Integer.Sparse.eval_collectBalanced, rawRowCheck9045]

theorem rawRowCheck9046 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form12 = rawRow9046 := by decide +kernel

theorem rowCheck9046 : row9046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9046 := by decide +kernel

theorem rowEval9046 (x : Key → ℝ) : Integer.Sparse.eval row9046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9046, Integer.Sparse.eval_collectBalanced, rawRowCheck9046]

theorem rawRowCheck9047 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form12 = rawRow9047 := by decide +kernel

theorem rowCheck9047 : row9047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9047 := by decide +kernel

theorem rowEval9047 (x : Key → ℝ) : Integer.Sparse.eval row9047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9047, Integer.Sparse.eval_collectBalanced, rawRowCheck9047]

theorem rawRowCheck9048 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form12 = rawRow9048 := by decide +kernel

theorem rowCheck9048 : row9048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9048 := by decide +kernel

theorem rowEval9048 (x : Key → ℝ) : Integer.Sparse.eval row9048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9048, Integer.Sparse.eval_collectBalanced, rawRowCheck9048]

theorem rawRowCheck9049 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form13 = rawRow9049 := by decide +kernel

theorem rowCheck9049 : row9049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9049 := by decide +kernel

theorem rowEval9049 (x : Key → ℝ) : Integer.Sparse.eval row9049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9049, Integer.Sparse.eval_collectBalanced, rawRowCheck9049]

theorem rawRowCheck9050 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form13 = rawRow9050 := by decide +kernel

theorem rowCheck9050 : row9050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9050 := by decide +kernel

theorem rowEval9050 (x : Key → ℝ) : Integer.Sparse.eval row9050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9050, Integer.Sparse.eval_collectBalanced, rawRowCheck9050]

theorem rawRowCheck9051 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form13 = rawRow9051 := by decide +kernel

theorem rowCheck9051 : row9051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9051 := by decide +kernel

theorem rowEval9051 (x : Key → ℝ) : Integer.Sparse.eval row9051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9051, Integer.Sparse.eval_collectBalanced, rawRowCheck9051]

theorem rawRowCheck9052 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9052 := by decide +kernel

theorem rowCheck9052 : row9052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9052 := by decide +kernel

theorem rowEval9052 (x : Key → ℝ) : Integer.Sparse.eval row9052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9052, Integer.Sparse.eval_collectBalanced, rawRowCheck9052]

theorem rawRowCheck9053 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form13 = rawRow9053 := by decide +kernel

theorem rowCheck9053 : row9053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9053 := by decide +kernel

theorem rowEval9053 (x : Key → ℝ) : Integer.Sparse.eval row9053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9053, Integer.Sparse.eval_collectBalanced, rawRowCheck9053]

theorem rawRowCheck9054 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form13 = rawRow9054 := by decide +kernel

theorem rowCheck9054 : row9054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9054 := by decide +kernel

theorem rowEval9054 (x : Key → ℝ) : Integer.Sparse.eval row9054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9054, Integer.Sparse.eval_collectBalanced, rawRowCheck9054]

theorem rawRowCheck9055 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form13 = rawRow9055 := by decide +kernel

theorem rowCheck9055 : row9055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9055 := by decide +kernel

theorem rowEval9055 (x : Key → ℝ) : Integer.Sparse.eval row9055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9055, Integer.Sparse.eval_collectBalanced, rawRowCheck9055]

theorem rawRowCheck9056 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form13 = rawRow9056 := by decide +kernel

theorem rowCheck9056 : row9056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9056 := by decide +kernel

theorem rowEval9056 (x : Key → ℝ) : Integer.Sparse.eval row9056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9056, Integer.Sparse.eval_collectBalanced, rawRowCheck9056]

theorem rawRowCheck9057 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form13 = rawRow9057 := by decide +kernel

theorem rowCheck9057 : row9057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9057 := by decide +kernel

theorem rowEval9057 (x : Key → ℝ) : Integer.Sparse.eval row9057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9057, Integer.Sparse.eval_collectBalanced, rawRowCheck9057]

theorem rawRowCheck9058 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form13 = rawRow9058 := by decide +kernel

theorem rowCheck9058 : row9058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9058 := by decide +kernel

theorem rowEval9058 (x : Key → ℝ) : Integer.Sparse.eval row9058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9058, Integer.Sparse.eval_collectBalanced, rawRowCheck9058]

theorem rawRowCheck9059 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form13 = rawRow9059 := by decide +kernel

theorem rowCheck9059 : row9059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9059 := by decide +kernel

theorem rowEval9059 (x : Key → ℝ) : Integer.Sparse.eval row9059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9059, Integer.Sparse.eval_collectBalanced, rawRowCheck9059]

theorem rawRowCheck9060 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form13 = rawRow9060 := by decide +kernel

theorem rowCheck9060 : row9060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9060 := by decide +kernel

theorem rowEval9060 (x : Key → ℝ) : Integer.Sparse.eval row9060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9060, Integer.Sparse.eval_collectBalanced, rawRowCheck9060]

theorem rawRowCheck9061 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form13 = rawRow9061 := by decide +kernel

theorem rowCheck9061 : row9061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9061 := by decide +kernel

theorem rowEval9061 (x : Key → ℝ) : Integer.Sparse.eval row9061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9061, Integer.Sparse.eval_collectBalanced, rawRowCheck9061]

theorem rawRowCheck9062 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form13 = rawRow9062 := by decide +kernel

theorem rowCheck9062 : row9062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9062 := by decide +kernel

theorem rowEval9062 (x : Key → ℝ) : Integer.Sparse.eval row9062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9062, Integer.Sparse.eval_collectBalanced, rawRowCheck9062]

theorem rawRowCheck9063 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form13 = rawRow9063 := by decide +kernel

theorem rowCheck9063 : row9063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9063 := by decide +kernel

theorem rowEval9063 (x : Key → ℝ) : Integer.Sparse.eval row9063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9063, Integer.Sparse.eval_collectBalanced, rawRowCheck9063]

theorem rawRowCheck9064 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form13 = rawRow9064 := by decide +kernel

theorem rowCheck9064 : row9064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9064 := by decide +kernel

theorem rowEval9064 (x : Key → ℝ) : Integer.Sparse.eval row9064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9064, Integer.Sparse.eval_collectBalanced, rawRowCheck9064]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck13_0 : entry13_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_0 k)) := by decide +kernel

theorem rowsSound13_0 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8841 x
  · exact rowEval8842 x
  · exact rowEval8843 x
  · exact rowEval8844 x
  · exact rowEval8845 x
  · exact rowEval8846 x
  · exact rowEval8847 x
  · exact rowEval8848 x
  · exact rowEval8849 x
  · exact rowEval8850 x
  · exact rowEval8851 x
  · exact rowEval8852 x
  · exact rowEval8853 x
  · exact rowEval8854 x
  · exact rowEval8855 x
  · exact rowEval8856 x

theorem entryEval13_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_0 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck13_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_0]

theorem entryCheck13_1 : entry13_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_1 k)) := by decide +kernel

theorem rowsSound13_1 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8857 x
  · exact rowEval8858 x
  · exact rowEval8859 x
  · exact rowEval8860 x
  · exact rowEval8861 x
  · exact rowEval8862 x
  · exact rowEval8863 x
  · exact rowEval8864 x
  · exact rowEval8865 x
  · exact rowEval8866 x
  · exact rowEval8867 x
  · exact rowEval8868 x
  · exact rowEval8869 x
  · exact rowEval8870 x
  · exact rowEval8871 x
  · exact rowEval8872 x

theorem entryEval13_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_1 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck13_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_1]

theorem entryCheck13_2 : entry13_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_2 k)) := by decide +kernel

theorem rowsSound13_2 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8873 x
  · exact rowEval8874 x
  · exact rowEval8875 x
  · exact rowEval8876 x
  · exact rowEval8877 x
  · exact rowEval8878 x
  · exact rowEval8879 x
  · exact rowEval8880 x
  · exact rowEval8881 x
  · exact rowEval8882 x
  · exact rowEval8883 x
  · exact rowEval8884 x
  · exact rowEval8885 x
  · exact rowEval8886 x
  · exact rowEval8887 x
  · exact rowEval8888 x

theorem entryEval13_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_2 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck13_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_2]

theorem entryCheck13_3 : entry13_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_3 k)) := by decide +kernel

theorem rowsSound13_3 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8889 x
  · exact rowEval8890 x
  · exact rowEval8891 x
  · exact rowEval8892 x
  · exact rowEval8893 x
  · exact rowEval8894 x
  · exact rowEval8895 x
  · exact rowEval8896 x
  · exact rowEval8897 x
  · exact rowEval8898 x
  · exact rowEval8899 x
  · exact rowEval8900 x
  · exact rowEval8901 x
  · exact rowEval8902 x
  · exact rowEval8903 x
  · exact rowEval8904 x

theorem entryEval13_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_3 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck13_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_3]

theorem entryCheck13_4 : entry13_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_4 k)) := by decide +kernel

theorem rowsSound13_4 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8905 x
  · exact rowEval8906 x
  · exact rowEval8907 x
  · exact rowEval8908 x
  · exact rowEval8909 x
  · exact rowEval8910 x
  · exact rowEval8911 x
  · exact rowEval8912 x
  · exact rowEval8913 x
  · exact rowEval8914 x
  · exact rowEval8915 x
  · exact rowEval8916 x
  · exact rowEval8917 x
  · exact rowEval8918 x
  · exact rowEval8919 x
  · exact rowEval8920 x

theorem entryEval13_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_4 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck13_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_4]

theorem entryCheck13_5 : entry13_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_5 k)) := by decide +kernel

theorem rowsSound13_5 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8921 x
  · exact rowEval8922 x
  · exact rowEval8923 x
  · exact rowEval8924 x
  · exact rowEval8925 x
  · exact rowEval8926 x
  · exact rowEval8927 x
  · exact rowEval8928 x
  · exact rowEval8929 x
  · exact rowEval8930 x
  · exact rowEval8931 x
  · exact rowEval8932 x
  · exact rowEval8933 x
  · exact rowEval8934 x
  · exact rowEval8935 x
  · exact rowEval8936 x

theorem entryEval13_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_5 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck13_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_5]

theorem entryCheck13_6 : entry13_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_6 k)) := by decide +kernel

theorem rowsSound13_6 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8937 x
  · exact rowEval8938 x
  · exact rowEval8939 x
  · exact rowEval8940 x
  · exact rowEval8941 x
  · exact rowEval8942 x
  · exact rowEval8943 x
  · exact rowEval8944 x
  · exact rowEval8945 x
  · exact rowEval8946 x
  · exact rowEval8947 x
  · exact rowEval8948 x
  · exact rowEval8949 x
  · exact rowEval8950 x
  · exact rowEval8951 x
  · exact rowEval8952 x

theorem entryEval13_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_6 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck13_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_6]

theorem entryCheck13_7 : entry13_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_7 k)) := by decide +kernel

theorem rowsSound13_7 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8953 x
  · exact rowEval8954 x
  · exact rowEval8955 x
  · exact rowEval8956 x
  · exact rowEval8957 x
  · exact rowEval8958 x
  · exact rowEval8959 x
  · exact rowEval8960 x
  · exact rowEval8961 x
  · exact rowEval8962 x
  · exact rowEval8963 x
  · exact rowEval8964 x
  · exact rowEval8965 x
  · exact rowEval8966 x
  · exact rowEval8967 x
  · exact rowEval8968 x

theorem entryEval13_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_7 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck13_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_7]

theorem entryCheck13_8 : entry13_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_8 k)) := by decide +kernel

theorem rowsSound13_8 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8969 x
  · exact rowEval8970 x
  · exact rowEval8971 x
  · exact rowEval8972 x
  · exact rowEval8973 x
  · exact rowEval8974 x
  · exact rowEval8975 x
  · exact rowEval8976 x
  · exact rowEval8977 x
  · exact rowEval8978 x
  · exact rowEval8979 x
  · exact rowEval8980 x
  · exact rowEval8981 x
  · exact rowEval8982 x
  · exact rowEval8983 x
  · exact rowEval8984 x

theorem entryEval13_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_8 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck13_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_8]

theorem entryCheck13_10 : entry13_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_10 k)) := by decide +kernel

theorem rowsSound13_10 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9001 x
  · exact rowEval9002 x
  · exact rowEval9003 x
  · exact rowEval9004 x
  · exact rowEval9005 x
  · exact rowEval9006 x
  · exact rowEval9007 x
  · exact rowEval9008 x
  · exact rowEval9009 x
  · exact rowEval9010 x
  · exact rowEval9011 x
  · exact rowEval9012 x
  · exact rowEval9013 x
  · exact rowEval9014 x
  · exact rowEval9015 x
  · exact rowEval9016 x

theorem entryEval13_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_10 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck13_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_10]

theorem entryCheck13_11 : entry13_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_11 k)) := by decide +kernel

theorem rowsSound13_11 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9017 x
  · exact rowEval9018 x
  · exact rowEval9019 x
  · exact rowEval9020 x
  · exact rowEval9021 x
  · exact rowEval9022 x
  · exact rowEval9023 x
  · exact rowEval9024 x
  · exact rowEval9025 x
  · exact rowEval9026 x
  · exact rowEval9027 x
  · exact rowEval9028 x
  · exact rowEval9029 x
  · exact rowEval9030 x
  · exact rowEval9031 x
  · exact rowEval9032 x

theorem entryEval13_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_11 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck13_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_11]

theorem entryCheck13_12 : entry13_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_12 k)) := by decide +kernel

theorem rowsSound13_12 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9033 x
  · exact rowEval9034 x
  · exact rowEval9035 x
  · exact rowEval9036 x
  · exact rowEval9037 x
  · exact rowEval9038 x
  · exact rowEval9039 x
  · exact rowEval9040 x
  · exact rowEval9041 x
  · exact rowEval9042 x
  · exact rowEval9043 x
  · exact rowEval9044 x
  · exact rowEval9045 x
  · exact rowEval9046 x
  · exact rowEval9047 x
  · exact rowEval9048 x

theorem entryEval13_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_12 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck13_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_12]

theorem entryCheck13_13 : entry13_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_13 k)) := by decide +kernel

theorem rowsSound13_13 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9049 x
  · exact rowEval9050 x
  · exact rowEval9051 x
  · exact rowEval9052 x
  · exact rowEval9053 x
  · exact rowEval9054 x
  · exact rowEval9055 x
  · exact rowEval9056 x
  · exact rowEval9057 x
  · exact rowEval9058 x
  · exact rowEval9059 x
  · exact rowEval9060 x
  · exact rowEval9061 x
  · exact rowEval9062 x
  · exact rowEval9063 x
  · exact rowEval9064 x

theorem entryEval13_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_13 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck13_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9157 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form13 = rawRow9157 := by decide +kernel

theorem rowCheck9157 : row9157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9157 := by decide +kernel

theorem rowEval9157 (x : Key → ℝ) : Integer.Sparse.eval row9157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9157, Integer.Sparse.eval_collectBalanced, rawRowCheck9157]

theorem rawRowCheck9158 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form13 = rawRow9158 := by decide +kernel

theorem rowCheck9158 : row9158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9158 := by decide +kernel

theorem rowEval9158 (x : Key → ℝ) : Integer.Sparse.eval row9158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9158, Integer.Sparse.eval_collectBalanced, rawRowCheck9158]

theorem rawRowCheck9159 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form13 = rawRow9159 := by decide +kernel

theorem rowCheck9159 : row9159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9159 := by decide +kernel

theorem rowEval9159 (x : Key → ℝ) : Integer.Sparse.eval row9159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9159, Integer.Sparse.eval_collectBalanced, rawRowCheck9159]

theorem rawRowCheck9160 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9160 := by decide +kernel

theorem rowCheck9160 : row9160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9160 := by decide +kernel

theorem rowEval9160 (x : Key → ℝ) : Integer.Sparse.eval row9160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9160, Integer.Sparse.eval_collectBalanced, rawRowCheck9160]

theorem rawRowCheck9161 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9161 := by decide +kernel

theorem rowCheck9161 : row9161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9161 := by decide +kernel

theorem rowEval9161 (x : Key → ℝ) : Integer.Sparse.eval row9161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9161, Integer.Sparse.eval_collectBalanced, rawRowCheck9161]

theorem rawRowCheck9162 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form13 = rawRow9162 := by decide +kernel

theorem rowCheck9162 : row9162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9162 := by decide +kernel

theorem rowEval9162 (x : Key → ℝ) : Integer.Sparse.eval row9162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9162, Integer.Sparse.eval_collectBalanced, rawRowCheck9162]

theorem rawRowCheck9163 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form13 = rawRow9163 := by decide +kernel

theorem rowCheck9163 : row9163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9163 := by decide +kernel

theorem rowEval9163 (x : Key → ℝ) : Integer.Sparse.eval row9163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9163, Integer.Sparse.eval_collectBalanced, rawRowCheck9163]

theorem rawRowCheck9164 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form13 = rawRow9164 := by decide +kernel

theorem rowCheck9164 : row9164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9164 := by decide +kernel

theorem rowEval9164 (x : Key → ℝ) : Integer.Sparse.eval row9164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9164, Integer.Sparse.eval_collectBalanced, rawRowCheck9164]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck14_13 : entry14_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_13 k)) := by decide +kernel

theorem rowsSound14_13 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9157 x
  · exact rowEval9158 x
  · exact rowEval9159 x
  · exact rowEval9160 x
  · exact rowEval9161 x
  · exact rowEval9162 x
  · exact rowEval9163 x
  · exact rowEval9164 x

theorem entryEval14_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_13 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck14_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9333 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form13 = rawRow9333 := by decide +kernel

theorem rowCheck9333 : row9333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9333 := by decide +kernel

theorem rowEval9333 (x : Key → ℝ) : Integer.Sparse.eval row9333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9333, Integer.Sparse.eval_collectBalanced, rawRowCheck9333]

theorem rawRowCheck9334 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form13 = rawRow9334 := by decide +kernel

theorem rowCheck9334 : row9334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9334 := by decide +kernel

theorem rowEval9334 (x : Key → ℝ) : Integer.Sparse.eval row9334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9334, Integer.Sparse.eval_collectBalanced, rawRowCheck9334]

theorem rawRowCheck9335 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form13 = rawRow9335 := by decide +kernel

theorem rowCheck9335 : row9335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9335 := by decide +kernel

theorem rowEval9335 (x : Key → ℝ) : Integer.Sparse.eval row9335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9335, Integer.Sparse.eval_collectBalanced, rawRowCheck9335]

theorem rawRowCheck9336 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9336 := by decide +kernel

theorem rowCheck9336 : row9336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9336 := by decide +kernel

theorem rowEval9336 (x : Key → ℝ) : Integer.Sparse.eval row9336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9336, Integer.Sparse.eval_collectBalanced, rawRowCheck9336]

theorem rawRowCheck9337 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form13 = rawRow9337 := by decide +kernel

theorem rowCheck9337 : row9337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9337 := by decide +kernel

theorem rowEval9337 (x : Key → ℝ) : Integer.Sparse.eval row9337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9337, Integer.Sparse.eval_collectBalanced, rawRowCheck9337]

theorem rawRowCheck9338 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form13 = rawRow9338 := by decide +kernel

theorem rowCheck9338 : row9338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9338 := by decide +kernel

theorem rowEval9338 (x : Key → ℝ) : Integer.Sparse.eval row9338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9338, Integer.Sparse.eval_collectBalanced, rawRowCheck9338]

theorem rawRowCheck9339 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form13 = rawRow9339 := by decide +kernel

theorem rowCheck9339 : row9339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9339 := by decide +kernel

theorem rowEval9339 (x : Key → ℝ) : Integer.Sparse.eval row9339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9339, Integer.Sparse.eval_collectBalanced, rawRowCheck9339]

theorem rawRowCheck9340 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form13 = rawRow9340 := by decide +kernel

theorem rowCheck9340 : row9340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9340 := by decide +kernel

theorem rowEval9340 (x : Key → ℝ) : Integer.Sparse.eval row9340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9340, Integer.Sparse.eval_collectBalanced, rawRowCheck9340]

theorem rawRowCheck9341 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form13 = rawRow9341 := by decide +kernel

theorem rowCheck9341 : row9341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9341 := by decide +kernel

theorem rowEval9341 (x : Key → ℝ) : Integer.Sparse.eval row9341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9341, Integer.Sparse.eval_collectBalanced, rawRowCheck9341]

theorem rawRowCheck9342 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form13 = rawRow9342 := by decide +kernel

theorem rowCheck9342 : row9342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9342 := by decide +kernel

theorem rowEval9342 (x : Key → ℝ) : Integer.Sparse.eval row9342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9342, Integer.Sparse.eval_collectBalanced, rawRowCheck9342]

theorem rawRowCheck9343 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form13 = rawRow9343 := by decide +kernel

theorem rowCheck9343 : row9343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9343 := by decide +kernel

theorem rowEval9343 (x : Key → ℝ) : Integer.Sparse.eval row9343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9343, Integer.Sparse.eval_collectBalanced, rawRowCheck9343]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9344 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form13 = rawRow9344 := by decide +kernel

theorem rowCheck9344 : row9344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9344 := by decide +kernel

theorem rowEval9344 (x : Key → ℝ) : Integer.Sparse.eval row9344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9344, Integer.Sparse.eval_collectBalanced, rawRowCheck9344]

theorem rawRowCheck9345 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form13 = rawRow9345 := by decide +kernel

theorem rowCheck9345 : row9345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9345 := by decide +kernel

theorem rowEval9345 (x : Key → ℝ) : Integer.Sparse.eval row9345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9345, Integer.Sparse.eval_collectBalanced, rawRowCheck9345]

theorem rawRowCheck9346 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form13 = rawRow9346 := by decide +kernel

theorem rowCheck9346 : row9346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9346 := by decide +kernel

theorem rowEval9346 (x : Key → ℝ) : Integer.Sparse.eval row9346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9346, Integer.Sparse.eval_collectBalanced, rawRowCheck9346]

theorem rawRowCheck9347 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form13 = rawRow9347 := by decide +kernel

theorem rowCheck9347 : row9347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9347 := by decide +kernel

theorem rowEval9347 (x : Key → ℝ) : Integer.Sparse.eval row9347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9347, Integer.Sparse.eval_collectBalanced, rawRowCheck9347]

theorem rawRowCheck9348 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form13 = rawRow9348 := by decide +kernel

theorem rowCheck9348 : row9348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9348 := by decide +kernel

theorem rowEval9348 (x : Key → ℝ) : Integer.Sparse.eval row9348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9348, Integer.Sparse.eval_collectBalanced, rawRowCheck9348]

theorem rawRowCheck9469 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9469 := by decide +kernel

theorem rowCheck9469 : row9469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9469 := by decide +kernel

theorem rowEval9469 (x : Key → ℝ) : Integer.Sparse.eval row9469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9469, Integer.Sparse.eval_collectBalanced, rawRowCheck9469]

theorem rawRowCheck9470 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form13 = rawRow9470 := by decide +kernel

theorem rowCheck9470 : row9470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9470 := by decide +kernel

theorem rowEval9470 (x : Key → ℝ) : Integer.Sparse.eval row9470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9470, Integer.Sparse.eval_collectBalanced, rawRowCheck9470]

theorem rawRowCheck9471 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form13 = rawRow9471 := by decide +kernel

theorem rowCheck9471 : row9471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9471 := by decide +kernel

theorem rowEval9471 (x : Key → ℝ) : Integer.Sparse.eval row9471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9471, Integer.Sparse.eval_collectBalanced, rawRowCheck9471]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck15_13 : entry15_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_13 k)) := by decide +kernel

theorem rowsSound15_13 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9333 x
  · exact rowEval9334 x
  · exact rowEval9335 x
  · exact rowEval9336 x
  · exact rowEval9337 x
  · exact rowEval9338 x
  · exact rowEval9339 x
  · exact rowEval9340 x
  · exact rowEval9341 x
  · exact rowEval9342 x
  · exact rowEval9343 x
  · exact rowEval9344 x
  · exact rowEval9345 x
  · exact rowEval9346 x
  · exact rowEval9347 x
  · exact rowEval9348 x

theorem entryEval15_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_13 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck15_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9472 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form13 = rawRow9472 := by decide +kernel

theorem rowCheck9472 : row9472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9472 := by decide +kernel

theorem rowEval9472 (x : Key → ℝ) : Integer.Sparse.eval row9472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9472, Integer.Sparse.eval_collectBalanced, rawRowCheck9472]

theorem rawRowCheck9473 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9473 := by decide +kernel

theorem rowCheck9473 : row9473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9473 := by decide +kernel

theorem rowEval9473 (x : Key → ℝ) : Integer.Sparse.eval row9473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9473, Integer.Sparse.eval_collectBalanced, rawRowCheck9473]

theorem rawRowCheck9474 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form13 = rawRow9474 := by decide +kernel

theorem rowCheck9474 : row9474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9474 := by decide +kernel

theorem rowEval9474 (x : Key → ℝ) : Integer.Sparse.eval row9474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9474, Integer.Sparse.eval_collectBalanced, rawRowCheck9474]

theorem rawRowCheck9475 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form13 = rawRow9475 := by decide +kernel

theorem rowCheck9475 : row9475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9475 := by decide +kernel

theorem rowEval9475 (x : Key → ℝ) : Integer.Sparse.eval row9475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9475, Integer.Sparse.eval_collectBalanced, rawRowCheck9475]

theorem rawRowCheck9476 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form13 = rawRow9476 := by decide +kernel

theorem rowCheck9476 : row9476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9476 := by decide +kernel

theorem rowEval9476 (x : Key → ℝ) : Integer.Sparse.eval row9476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9476, Integer.Sparse.eval_collectBalanced, rawRowCheck9476]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck16_13 : entry16_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_13 k)) := by decide +kernel

theorem rowsSound16_13 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9469 x
  · exact rowEval9470 x
  · exact rowEval9471 x
  · exact rowEval9472 x
  · exact rowEval9473 x
  · exact rowEval9474 x
  · exact rowEval9475 x
  · exact rowEval9476 x

theorem entryEval16_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_13 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck16_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10519 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form13 = rawRow10519 := by decide +kernel

theorem rowCheck10519 : row10519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10519 := by decide +kernel

theorem rowEval10519 (x : Key → ℝ) : Integer.Sparse.eval row10519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10519, Integer.Sparse.eval_collectBalanced, rawRowCheck10519]

theorem rawRowCheck10520 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form13 = rawRow10520 := by decide +kernel

theorem rowCheck10520 : row10520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10520 := by decide +kernel

theorem rowEval10520 (x : Key → ℝ) : Integer.Sparse.eval row10520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10520, Integer.Sparse.eval_collectBalanced, rawRowCheck10520]

theorem rawRowCheck10521 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form13 = rawRow10521 := by decide +kernel

theorem rowCheck10521 : row10521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10521 := by decide +kernel

theorem rowEval10521 (x : Key → ℝ) : Integer.Sparse.eval row10521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10521, Integer.Sparse.eval_collectBalanced, rawRowCheck10521]

theorem rawRowCheck10522 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form13 = rawRow10522 := by decide +kernel

theorem rowCheck10522 : row10522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10522 := by decide +kernel

theorem rowEval10522 (x : Key → ℝ) : Integer.Sparse.eval row10522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10522, Integer.Sparse.eval_collectBalanced, rawRowCheck10522]

theorem rawRowCheck10523 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form13 = rawRow10523 := by decide +kernel

theorem rowCheck10523 : row10523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10523 := by decide +kernel

theorem rowEval10523 (x : Key → ℝ) : Integer.Sparse.eval row10523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10523, Integer.Sparse.eval_collectBalanced, rawRowCheck10523]

theorem rawRowCheck10524 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form13 = rawRow10524 := by decide +kernel

theorem rowCheck10524 : row10524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10524 := by decide +kernel

theorem rowEval10524 (x : Key → ℝ) : Integer.Sparse.eval row10524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10524, Integer.Sparse.eval_collectBalanced, rawRowCheck10524]

theorem rawRowCheck10525 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form13 = rawRow10525 := by decide +kernel

theorem rowCheck10525 : row10525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10525 := by decide +kernel

theorem rowEval10525 (x : Key → ℝ) : Integer.Sparse.eval row10525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10525, Integer.Sparse.eval_collectBalanced, rawRowCheck10525]

theorem rawRowCheck10526 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form13 = rawRow10526 := by decide +kernel

theorem rowCheck10526 : row10526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10526 := by decide +kernel

theorem rowEval10526 (x : Key → ℝ) : Integer.Sparse.eval row10526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10526, Integer.Sparse.eval_collectBalanced, rawRowCheck10526]

theorem rawRowCheck10527 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form13 = rawRow10527 := by decide +kernel

theorem rowCheck10527 : row10527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10527 := by decide +kernel

theorem rowEval10527 (x : Key → ℝ) : Integer.Sparse.eval row10527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10527, Integer.Sparse.eval_collectBalanced, rawRowCheck10527]

theorem rawRowCheck10528 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form13 = rawRow10528 := by decide +kernel

theorem rowCheck10528 : row10528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10528 := by decide +kernel

theorem rowEval10528 (x : Key → ℝ) : Integer.Sparse.eval row10528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10528, Integer.Sparse.eval_collectBalanced, rawRowCheck10528]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck19_13 : entry19_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_13 k)) := by decide +kernel

theorem rowsSound19_13 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval10519 x
  · exact rowEval10520 x
  · exact rowEval10521 x
  · exact rowEval10522 x
  · exact rowEval10523 x
  · exact rowEval10524 x
  · exact rowEval10525 x
  · exact rowEval10526 x
  · exact rowEval10527 x
  · exact rowEval10528 x

theorem entryEval19_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_13 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck19_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10654 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form13 = rawRow10654 := by decide +kernel

theorem rowCheck10654 : row10654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10654 := by decide +kernel

theorem rowEval10654 (x : Key → ℝ) : Integer.Sparse.eval row10654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck10654, Integer.Sparse.eval_collectBalanced, rawRowCheck10654]

theorem rawRowCheck10655 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form13 = rawRow10655 := by decide +kernel

theorem rowCheck10655 : row10655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10655 := by decide +kernel

theorem rowEval10655 (x : Key → ℝ) : Integer.Sparse.eval row10655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10655, Integer.Sparse.eval_collectBalanced, rawRowCheck10655]

theorem rawRowCheck10656 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form13 = rawRow10656 := by decide +kernel

theorem rowCheck10656 : row10656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10656 := by decide +kernel

theorem rowEval10656 (x : Key → ℝ) : Integer.Sparse.eval row10656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10656, Integer.Sparse.eval_collectBalanced, rawRowCheck10656]

theorem rawRowCheck10657 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow10657 := by decide +kernel

theorem rowCheck10657 : row10657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10657 := by decide +kernel

theorem rowEval10657 (x : Key → ℝ) : Integer.Sparse.eval row10657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10657, Integer.Sparse.eval_collectBalanced, rawRowCheck10657]

theorem rawRowCheck10658 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form13 = rawRow10658 := by decide +kernel

theorem rowCheck10658 : row10658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10658 := by decide +kernel

theorem rowEval10658 (x : Key → ℝ) : Integer.Sparse.eval row10658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10658, Integer.Sparse.eval_collectBalanced, rawRowCheck10658]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck20_13 : entry20_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_13 k)) := by decide +kernel

theorem rowsSound20_13 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval10654 x
  · exact rowEval10655 x
  · exact rowEval10656 x
  · exact rowEval10657 x
  · exact rowEval10658 x

theorem entryEval20_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_13 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck20_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12008 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form13 = rawRow12008 := by decide +kernel

theorem rowCheck12008 : row12008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12008 := by decide +kernel

theorem rowEval12008 (x : Key → ℝ) : Integer.Sparse.eval row12008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12008, Integer.Sparse.eval_collectBalanced, rawRowCheck12008]

theorem rawRowCheck12009 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form13 = rawRow12009 := by decide +kernel

theorem rowCheck12009 : row12009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12009 := by decide +kernel

theorem rowEval12009 (x : Key → ℝ) : Integer.Sparse.eval row12009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12009, Integer.Sparse.eval_collectBalanced, rawRowCheck12009]

theorem rawRowCheck12010 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form13 = rawRow12010 := by decide +kernel

theorem rowCheck12010 : row12010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12010 := by decide +kernel

theorem rowEval12010 (x : Key → ℝ) : Integer.Sparse.eval row12010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12010, Integer.Sparse.eval_collectBalanced, rawRowCheck12010]

theorem rawRowCheck12011 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form13 = rawRow12011 := by decide +kernel

theorem rowCheck12011 : row12011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12011 := by decide +kernel

theorem rowEval12011 (x : Key → ℝ) : Integer.Sparse.eval row12011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12011, Integer.Sparse.eval_collectBalanced, rawRowCheck12011]

theorem rawRowCheck12012 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form13 = rawRow12012 := by decide +kernel

theorem rowCheck12012 : row12012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12012 := by decide +kernel

theorem rowEval12012 (x : Key → ℝ) : Integer.Sparse.eval row12012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12012, Integer.Sparse.eval_collectBalanced, rawRowCheck12012]

theorem rawRowCheck12013 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form13 = rawRow12013 := by decide +kernel

theorem rowCheck12013 : row12013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12013 := by decide +kernel

theorem rowEval12013 (x : Key → ℝ) : Integer.Sparse.eval row12013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12013, Integer.Sparse.eval_collectBalanced, rawRowCheck12013]

theorem rawRowCheck12014 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form13 = rawRow12014 := by decide +kernel

theorem rowCheck12014 : row12014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12014 := by decide +kernel

theorem rowEval12014 (x : Key → ℝ) : Integer.Sparse.eval row12014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12014, Integer.Sparse.eval_collectBalanced, rawRowCheck12014]

theorem rawRowCheck12015 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form13 = rawRow12015 := by decide +kernel

theorem rowCheck12015 : row12015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12015 := by decide +kernel

theorem rowEval12015 (x : Key → ℝ) : Integer.Sparse.eval row12015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12015, Integer.Sparse.eval_collectBalanced, rawRowCheck12015]

theorem rawRowCheck12016 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form13 = rawRow12016 := by decide +kernel

theorem rowCheck12016 : row12016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12016 := by decide +kernel

theorem rowEval12016 (x : Key → ℝ) : Integer.Sparse.eval row12016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12016, Integer.Sparse.eval_collectBalanced, rawRowCheck12016]

theorem rawRowCheck12017 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form13 = rawRow12017 := by decide +kernel

theorem rowCheck12017 : row12017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12017 := by decide +kernel

theorem rowEval12017 (x : Key → ℝ) : Integer.Sparse.eval row12017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12017, Integer.Sparse.eval_collectBalanced, rawRowCheck12017]

theorem rawRowCheck12018 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form13 = rawRow12018 := by decide +kernel

theorem rowCheck12018 : row12018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12018 := by decide +kernel

theorem rowEval12018 (x : Key → ℝ) : Integer.Sparse.eval row12018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12018, Integer.Sparse.eval_collectBalanced, rawRowCheck12018]

theorem rawRowCheck12019 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form13 = rawRow12019 := by decide +kernel

theorem rowCheck12019 : row12019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12019 := by decide +kernel

theorem rowEval12019 (x : Key → ℝ) : Integer.Sparse.eval row12019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck12019, Integer.Sparse.eval_collectBalanced, rawRowCheck12019]

theorem rawRowCheck12020 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form13 = rawRow12020 := by decide +kernel

theorem rowCheck12020 : row12020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12020 := by decide +kernel

theorem rowEval12020 (x : Key → ℝ) : Integer.Sparse.eval row12020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12020, Integer.Sparse.eval_collectBalanced, rawRowCheck12020]

theorem rawRowCheck12021 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form13 = rawRow12021 := by decide +kernel

theorem rowCheck12021 : row12021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12021 := by decide +kernel

theorem rowEval12021 (x : Key → ℝ) : Integer.Sparse.eval row12021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12021, Integer.Sparse.eval_collectBalanced, rawRowCheck12021]

theorem rawRowCheck12022 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form13 = rawRow12022 := by decide +kernel

theorem rowCheck12022 : row12022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12022 := by decide +kernel

theorem rowEval12022 (x : Key → ℝ) : Integer.Sparse.eval row12022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12022, Integer.Sparse.eval_collectBalanced, rawRowCheck12022]

theorem rawRowCheck12023 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form13 = rawRow12023 := by decide +kernel

theorem rowCheck12023 : row12023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12023 := by decide +kernel

theorem rowEval12023 (x : Key → ℝ) : Integer.Sparse.eval row12023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck12023, Integer.Sparse.eval_collectBalanced, rawRowCheck12023]

theorem rawRowCheck12024 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form13 = rawRow12024 := by decide +kernel

theorem rowCheck12024 : row12024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12024 := by decide +kernel

theorem rowEval12024 (x : Key → ℝ) : Integer.Sparse.eval row12024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12024, Integer.Sparse.eval_collectBalanced, rawRowCheck12024]

theorem rawRowCheck12025 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form13 = rawRow12025 := by decide +kernel

theorem rowCheck12025 : row12025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12025 := by decide +kernel

theorem rowEval12025 (x : Key → ℝ) : Integer.Sparse.eval row12025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck12025, Integer.Sparse.eval_collectBalanced, rawRowCheck12025]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12271 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form13 = rawRow12271 := by decide +kernel

theorem rowCheck12271 : row12271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12271 := by decide +kernel

theorem rowEval12271 (x : Key → ℝ) : Integer.Sparse.eval row12271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12271, Integer.Sparse.eval_collectBalanced, rawRowCheck12271]

theorem rawRowCheck12272 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow12272 := by decide +kernel

theorem rowCheck12272 : row12272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12272 := by decide +kernel

theorem rowEval12272 (x : Key → ℝ) : Integer.Sparse.eval row12272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12272, Integer.Sparse.eval_collectBalanced, rawRowCheck12272]

theorem rawRowCheck12273 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form13 = rawRow12273 := by decide +kernel

theorem rowCheck12273 : row12273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12273 := by decide +kernel

theorem rowEval12273 (x : Key → ℝ) : Integer.Sparse.eval row12273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12273, Integer.Sparse.eval_collectBalanced, rawRowCheck12273]

theorem rawRowCheck12274 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form13 = rawRow12274 := by decide +kernel

theorem rowCheck12274 : row12274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12274 := by decide +kernel

theorem rowEval12274 (x : Key → ℝ) : Integer.Sparse.eval row12274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12274, Integer.Sparse.eval_collectBalanced, rawRowCheck12274]

theorem rawRowCheck12275 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form13 = rawRow12275 := by decide +kernel

theorem rowCheck12275 : row12275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12275 := by decide +kernel

theorem rowEval12275 (x : Key → ℝ) : Integer.Sparse.eval row12275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12275, Integer.Sparse.eval_collectBalanced, rawRowCheck12275]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck23_13 : entry23_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_13 k)) := by decide +kernel

theorem rowsSound23_13 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12008 x
  · exact rowEval12009 x
  · exact rowEval12010 x
  · exact rowEval12011 x
  · exact rowEval12012 x
  · exact rowEval12013 x
  · exact rowEval12014 x
  · exact rowEval12015 x
  · exact rowEval12016 x
  · exact rowEval12017 x
  · exact rowEval12018 x
  · exact rowEval12019 x
  · exact rowEval12020 x
  · exact rowEval12021 x
  · exact rowEval12022 x
  · exact rowEval12023 x
  · exact rowEval12024 x
  · exact rowEval12025 x

theorem entryEval23_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_13 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck23_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck24_13 : entry24_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_13 k)) := by decide +kernel

theorem rowsSound24_13 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12271 x
  · exact rowEval12272 x
  · exact rowEval12273 x
  · exact rowEval12274 x
  · exact rowEval12275 x

theorem entryEval24_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_13 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck24_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12435 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form13 = rawRow12435 := by decide +kernel

theorem rowCheck12435 : row12435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12435 := by decide +kernel

theorem rowEval12435 (x : Key → ℝ) : Integer.Sparse.eval row12435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12435, Integer.Sparse.eval_collectBalanced, rawRowCheck12435]

theorem rawRowCheck12436 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form13 = rawRow12436 := by decide +kernel

theorem rowCheck12436 : row12436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12436 := by decide +kernel

theorem rowEval12436 (x : Key → ℝ) : Integer.Sparse.eval row12436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12436, Integer.Sparse.eval_collectBalanced, rawRowCheck12436]

theorem rawRowCheck12437 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form13 = rawRow12437 := by decide +kernel

theorem rowCheck12437 : row12437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12437 := by decide +kernel

theorem rowEval12437 (x : Key → ℝ) : Integer.Sparse.eval row12437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12437, Integer.Sparse.eval_collectBalanced, rawRowCheck12437]

theorem rawRowCheck12438 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form13 = rawRow12438 := by decide +kernel

theorem rowCheck12438 : row12438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12438 := by decide +kernel

theorem rowEval12438 (x : Key → ℝ) : Integer.Sparse.eval row12438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12438, Integer.Sparse.eval_collectBalanced, rawRowCheck12438]

theorem rawRowCheck12439 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form13 = rawRow12439 := by decide +kernel

theorem rowCheck12439 : row12439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12439 := by decide +kernel

theorem rowEval12439 (x : Key → ℝ) : Integer.Sparse.eval row12439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12439, Integer.Sparse.eval_collectBalanced, rawRowCheck12439]

theorem rawRowCheck12440 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form13 = rawRow12440 := by decide +kernel

theorem rowCheck12440 : row12440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12440 := by decide +kernel

theorem rowEval12440 (x : Key → ℝ) : Integer.Sparse.eval row12440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12440, Integer.Sparse.eval_collectBalanced, rawRowCheck12440]

theorem rawRowCheck12441 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form13 = rawRow12441 := by decide +kernel

theorem rowCheck12441 : row12441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12441 := by decide +kernel

theorem rowEval12441 (x : Key → ℝ) : Integer.Sparse.eval row12441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12441, Integer.Sparse.eval_collectBalanced, rawRowCheck12441]

theorem rawRowCheck12442 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form13 = rawRow12442 := by decide +kernel

theorem rowCheck12442 : row12442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12442 := by decide +kernel

theorem rowEval12442 (x : Key → ℝ) : Integer.Sparse.eval row12442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12442, Integer.Sparse.eval_collectBalanced, rawRowCheck12442]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck25_13 : entry25_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_13 k)) := by decide +kernel

theorem rowsSound25_13 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12435 x
  · exact rowEval12436 x
  · exact rowEval12437 x
  · exact rowEval12438 x
  · exact rowEval12439 x
  · exact rowEval12440 x
  · exact rowEval12441 x
  · exact rowEval12442 x

theorem entryEval25_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_13 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck25_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12851 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form13 = rawRow12851 := by decide +kernel

theorem rowCheck12851 : row12851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12851 := by decide +kernel

theorem rowEval12851 (x : Key → ℝ) : Integer.Sparse.eval row12851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12851, Integer.Sparse.eval_collectBalanced, rawRowCheck12851]

theorem rawRowCheck12852 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form13 = rawRow12852 := by decide +kernel

theorem rowCheck12852 : row12852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12852 := by decide +kernel

theorem rowEval12852 (x : Key → ℝ) : Integer.Sparse.eval row12852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12852, Integer.Sparse.eval_collectBalanced, rawRowCheck12852]

theorem rawRowCheck12853 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form13 = rawRow12853 := by decide +kernel

theorem rowCheck12853 : row12853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12853 := by decide +kernel

theorem rowEval12853 (x : Key → ℝ) : Integer.Sparse.eval row12853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12853, Integer.Sparse.eval_collectBalanced, rawRowCheck12853]

theorem rawRowCheck12854 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form13 = rawRow12854 := by decide +kernel

theorem rowCheck12854 : row12854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12854 := by decide +kernel

theorem rowEval12854 (x : Key → ℝ) : Integer.Sparse.eval row12854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12854, Integer.Sparse.eval_collectBalanced, rawRowCheck12854]

theorem rawRowCheck12855 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form13 = rawRow12855 := by decide +kernel

theorem rowCheck12855 : row12855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12855 := by decide +kernel

theorem rowEval12855 (x : Key → ℝ) : Integer.Sparse.eval row12855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12855, Integer.Sparse.eval_collectBalanced, rawRowCheck12855]

theorem rawRowCheck12856 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form13 = rawRow12856 := by decide +kernel

theorem rowCheck12856 : row12856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12856 := by decide +kernel

theorem rowEval12856 (x : Key → ℝ) : Integer.Sparse.eval row12856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12856, Integer.Sparse.eval_collectBalanced, rawRowCheck12856]

theorem rawRowCheck12857 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form13 = rawRow12857 := by decide +kernel

theorem rowCheck12857 : row12857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12857 := by decide +kernel

theorem rowEval12857 (x : Key → ℝ) : Integer.Sparse.eval row12857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12857, Integer.Sparse.eval_collectBalanced, rawRowCheck12857]

theorem rawRowCheck12858 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form13 = rawRow12858 := by decide +kernel

theorem rowCheck12858 : row12858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12858 := by decide +kernel

theorem rowEval12858 (x : Key → ℝ) : Integer.Sparse.eval row12858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12858, Integer.Sparse.eval_collectBalanced, rawRowCheck12858]

theorem rawRowCheck12859 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form13 = rawRow12859 := by decide +kernel

theorem rowCheck12859 : row12859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12859 := by decide +kernel

theorem rowEval12859 (x : Key → ℝ) : Integer.Sparse.eval row12859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12859, Integer.Sparse.eval_collectBalanced, rawRowCheck12859]

theorem rawRowCheck12860 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form13 = rawRow12860 := by decide +kernel

theorem rowCheck12860 : row12860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12860 := by decide +kernel

theorem rowEval12860 (x : Key → ℝ) : Integer.Sparse.eval row12860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12860, Integer.Sparse.eval_collectBalanced, rawRowCheck12860]

theorem rawRowCheck12861 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form13 = rawRow12861 := by decide +kernel

theorem rowCheck12861 : row12861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12861 := by decide +kernel

theorem rowEval12861 (x : Key → ℝ) : Integer.Sparse.eval row12861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12861, Integer.Sparse.eval_collectBalanced, rawRowCheck12861]

theorem rawRowCheck12862 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form13 = rawRow12862 := by decide +kernel

theorem rowCheck12862 : row12862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12862 := by decide +kernel

theorem rowEval12862 (x : Key → ℝ) : Integer.Sparse.eval row12862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12862, Integer.Sparse.eval_collectBalanced, rawRowCheck12862]

theorem rawRowCheck12863 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form13 = rawRow12863 := by decide +kernel

theorem rowCheck12863 : row12863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12863 := by decide +kernel

theorem rowEval12863 (x : Key → ℝ) : Integer.Sparse.eval row12863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12863, Integer.Sparse.eval_collectBalanced, rawRowCheck12863]

theorem rawRowCheck12864 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form13 = rawRow12864 := by decide +kernel

theorem rowCheck12864 : row12864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12864 := by decide +kernel

theorem rowEval12864 (x : Key → ℝ) : Integer.Sparse.eval row12864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12864, Integer.Sparse.eval_collectBalanced, rawRowCheck12864]

theorem rawRowCheck12865 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form13 = rawRow12865 := by decide +kernel

theorem rowCheck12865 : row12865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12865 := by decide +kernel

theorem rowEval12865 (x : Key → ℝ) : Integer.Sparse.eval row12865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12865, Integer.Sparse.eval_collectBalanced, rawRowCheck12865]

theorem rawRowCheck12866 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form13 = rawRow12866 := by decide +kernel

theorem rowCheck12866 : row12866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12866 := by decide +kernel

theorem rowEval12866 (x : Key → ℝ) : Integer.Sparse.eval row12866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12866, Integer.Sparse.eval_collectBalanced, rawRowCheck12866]

theorem rawRowCheck12867 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form13 = rawRow12867 := by decide +kernel

theorem rowCheck12867 : row12867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12867 := by decide +kernel

theorem rowEval12867 (x : Key → ℝ) : Integer.Sparse.eval row12867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12867, Integer.Sparse.eval_collectBalanced, rawRowCheck12867]

theorem rawRowCheck12868 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form13 = rawRow12868 := by decide +kernel

theorem rowCheck12868 : row12868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12868 := by decide +kernel

theorem rowEval12868 (x : Key → ℝ) : Integer.Sparse.eval row12868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12868, Integer.Sparse.eval_collectBalanced, rawRowCheck12868]

theorem rawRowCheck12869 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form13 = rawRow12869 := by decide +kernel

theorem rowCheck12869 : row12869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12869 := by decide +kernel

theorem rowEval12869 (x : Key → ℝ) : Integer.Sparse.eval row12869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12869, Integer.Sparse.eval_collectBalanced, rawRowCheck12869]

theorem rawRowCheck12870 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form13 = rawRow12870 := by decide +kernel

theorem rowCheck12870 : row12870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12870 := by decide +kernel

theorem rowEval12870 (x : Key → ℝ) : Integer.Sparse.eval row12870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12870, Integer.Sparse.eval_collectBalanced, rawRowCheck12870]

theorem rawRowCheck12871 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form13 = rawRow12871 := by decide +kernel

theorem rowCheck12871 : row12871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12871 := by decide +kernel

theorem rowEval12871 (x : Key → ℝ) : Integer.Sparse.eval row12871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12871, Integer.Sparse.eval_collectBalanced, rawRowCheck12871]

theorem rawRowCheck12872 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form13 = rawRow12872 := by decide +kernel

theorem rowCheck12872 : row12872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12872 := by decide +kernel

theorem rowEval12872 (x : Key → ℝ) : Integer.Sparse.eval row12872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12872, Integer.Sparse.eval_collectBalanced, rawRowCheck12872]

theorem rawRowCheck12873 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form13 = rawRow12873 := by decide +kernel

theorem rowCheck12873 : row12873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12873 := by decide +kernel

theorem rowEval12873 (x : Key → ℝ) : Integer.Sparse.eval row12873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12873, Integer.Sparse.eval_collectBalanced, rawRowCheck12873]

theorem rawRowCheck12874 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form13 = rawRow12874 := by decide +kernel

theorem rowCheck12874 : row12874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12874 := by decide +kernel

theorem rowEval12874 (x : Key → ℝ) : Integer.Sparse.eval row12874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12874, Integer.Sparse.eval_collectBalanced, rawRowCheck12874]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck26_13 : entry26_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_13 k)) := by decide +kernel

theorem rowsSound26_13 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12851 x
  · exact rowEval12852 x
  · exact rowEval12853 x
  · exact rowEval12854 x
  · exact rowEval12855 x
  · exact rowEval12856 x
  · exact rowEval12857 x
  · exact rowEval12858 x
  · exact rowEval12859 x
  · exact rowEval12860 x
  · exact rowEval12861 x
  · exact rowEval12862 x
  · exact rowEval12863 x
  · exact rowEval12864 x
  · exact rowEval12865 x
  · exact rowEval12866 x
  · exact rowEval12867 x
  · exact rowEval12868 x
  · exact rowEval12869 x
  · exact rowEval12870 x
  · exact rowEval12871 x
  · exact rowEval12872 x
  · exact rowEval12873 x
  · exact rowEval12874 x

theorem entryEval26_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_13 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck26_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

theorem entryEvalRow13_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 13 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 13).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval13_0 B hB
  · exact entryEval13_1 B hB
  · exact entryEval13_2 B hB
  · exact entryEval13_3 B hB
  · exact entryEval13_4 B hB
  · exact entryEval13_5 B hB
  · exact entryEval13_6 B hB
  · exact entryEval13_7 B hB
  · exact entryEval13_8 B hB
  · exact entryEval13_9_e B hB
  · exact entryEval13_10 B hB
  · exact entryEval13_11 B hB
  · exact entryEval13_12 B hB
  · exact entryEval13_13 B hB
  · exact (entryEval14_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_13_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_13_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_13_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_13_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e_oai
