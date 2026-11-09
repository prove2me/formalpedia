-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:13:18.148637+00:00
-- url     : https://prove2.me/submissions/f8fe7226-22cd-4298-b6a1-712972e4eb53

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval15_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval15_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval15_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_15_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8661 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form0 = rawRow8661 := by decide +kernel

theorem rowCheck8661 : row8661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8661 := by decide +kernel

theorem rowEval8661 (x : Key → ℝ) : Integer.Sparse.eval row8661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8661, Integer.Sparse.eval_collectBalanced, rawRowCheck8661]

theorem rawRowCheck8662 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form0 = rawRow8662 := by decide +kernel

theorem rowCheck8662 : row8662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8662 := by decide +kernel

theorem rowEval8662 (x : Key → ℝ) : Integer.Sparse.eval row8662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8662, Integer.Sparse.eval_collectBalanced, rawRowCheck8662]

theorem rawRowCheck8663 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form0 = rawRow8663 := by decide +kernel

theorem rowCheck8663 : row8663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8663 := by decide +kernel

theorem rowEval8663 (x : Key → ℝ) : Integer.Sparse.eval row8663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8663, Integer.Sparse.eval_collectBalanced, rawRowCheck8663]

theorem rawRowCheck8664 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8664 := by decide +kernel

theorem rowCheck8664 : row8664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8664 := by decide +kernel

theorem rowEval8664 (x : Key → ℝ) : Integer.Sparse.eval row8664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8664, Integer.Sparse.eval_collectBalanced, rawRowCheck8664]

theorem rawRowCheck8669 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form1 = rawRow8669 := by decide +kernel

theorem rowCheck8669 : row8669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8669 := by decide +kernel

theorem rowEval8669 (x : Key → ℝ) : Integer.Sparse.eval row8669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8669, Integer.Sparse.eval_collectBalanced, rawRowCheck8669]

theorem rawRowCheck8670 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form1 = rawRow8670 := by decide +kernel

theorem rowCheck8670 : row8670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8670 := by decide +kernel

theorem rowEval8670 (x : Key → ℝ) : Integer.Sparse.eval row8670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8670, Integer.Sparse.eval_collectBalanced, rawRowCheck8670]

theorem rawRowCheck8671 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form1 = rawRow8671 := by decide +kernel

theorem rowCheck8671 : row8671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8671 := by decide +kernel

theorem rowEval8671 (x : Key → ℝ) : Integer.Sparse.eval row8671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8671, Integer.Sparse.eval_collectBalanced, rawRowCheck8671]

theorem rawRowCheck8672 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8672 := by decide +kernel

theorem rowCheck8672 : row8672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8672 := by decide +kernel

theorem rowEval8672 (x : Key → ℝ) : Integer.Sparse.eval row8672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8672, Integer.Sparse.eval_collectBalanced, rawRowCheck8672]

theorem rawRowCheck8677 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form2 = rawRow8677 := by decide +kernel

theorem rowCheck8677 : row8677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8677 := by decide +kernel

theorem rowEval8677 (x : Key → ℝ) : Integer.Sparse.eval row8677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8677, Integer.Sparse.eval_collectBalanced, rawRowCheck8677]

theorem rawRowCheck8678 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form2 = rawRow8678 := by decide +kernel

theorem rowCheck8678 : row8678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8678 := by decide +kernel

theorem rowEval8678 (x : Key → ℝ) : Integer.Sparse.eval row8678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8678, Integer.Sparse.eval_collectBalanced, rawRowCheck8678]

theorem rawRowCheck8679 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form2 = rawRow8679 := by decide +kernel

theorem rowCheck8679 : row8679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8679 := by decide +kernel

theorem rowEval8679 (x : Key → ℝ) : Integer.Sparse.eval row8679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8679, Integer.Sparse.eval_collectBalanced, rawRowCheck8679]

theorem rawRowCheck8680 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8680 := by decide +kernel

theorem rowCheck8680 : row8680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8680 := by decide +kernel

theorem rowEval8680 (x : Key → ℝ) : Integer.Sparse.eval row8680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8680, Integer.Sparse.eval_collectBalanced, rawRowCheck8680]

theorem rawRowCheck8685 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form3 = rawRow8685 := by decide +kernel

theorem rowCheck8685 : row8685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8685 := by decide +kernel

theorem rowEval8685 (x : Key → ℝ) : Integer.Sparse.eval row8685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8685, Integer.Sparse.eval_collectBalanced, rawRowCheck8685]

theorem rawRowCheck8686 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form3 = rawRow8686 := by decide +kernel

theorem rowCheck8686 : row8686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8686 := by decide +kernel

theorem rowEval8686 (x : Key → ℝ) : Integer.Sparse.eval row8686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8686, Integer.Sparse.eval_collectBalanced, rawRowCheck8686]

theorem rawRowCheck8687 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form3 = rawRow8687 := by decide +kernel

theorem rowCheck8687 : row8687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8687 := by decide +kernel

theorem rowEval8687 (x : Key → ℝ) : Integer.Sparse.eval row8687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8687, Integer.Sparse.eval_collectBalanced, rawRowCheck8687]

theorem rawRowCheck8688 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8688 := by decide +kernel

theorem rowCheck8688 : row8688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8688 := by decide +kernel

theorem rowEval8688 (x : Key → ℝ) : Integer.Sparse.eval row8688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8688, Integer.Sparse.eval_collectBalanced, rawRowCheck8688]

theorem rawRowCheck8693 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form4 = rawRow8693 := by decide +kernel

theorem rowCheck8693 : row8693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8693 := by decide +kernel

theorem rowEval8693 (x : Key → ℝ) : Integer.Sparse.eval row8693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8693, Integer.Sparse.eval_collectBalanced, rawRowCheck8693]

theorem rawRowCheck8694 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form4 = rawRow8694 := by decide +kernel

theorem rowCheck8694 : row8694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8694 := by decide +kernel

theorem rowEval8694 (x : Key → ℝ) : Integer.Sparse.eval row8694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8694, Integer.Sparse.eval_collectBalanced, rawRowCheck8694]

theorem rawRowCheck8695 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form4 = rawRow8695 := by decide +kernel

theorem rowCheck8695 : row8695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8695 := by decide +kernel

theorem rowEval8695 (x : Key → ℝ) : Integer.Sparse.eval row8695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8695, Integer.Sparse.eval_collectBalanced, rawRowCheck8695]

theorem rawRowCheck8696 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8696 := by decide +kernel

theorem rowCheck8696 : row8696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8696 := by decide +kernel

theorem rowEval8696 (x : Key → ℝ) : Integer.Sparse.eval row8696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8696, Integer.Sparse.eval_collectBalanced, rawRowCheck8696]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8709 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form6 = rawRow8709 := by decide +kernel

theorem rowCheck8709 : row8709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8709 := by decide +kernel

theorem rowEval8709 (x : Key → ℝ) : Integer.Sparse.eval row8709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8709, Integer.Sparse.eval_collectBalanced, rawRowCheck8709]

theorem rawRowCheck8710 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form6 = rawRow8710 := by decide +kernel

theorem rowCheck8710 : row8710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8710 := by decide +kernel

theorem rowEval8710 (x : Key → ℝ) : Integer.Sparse.eval row8710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8710, Integer.Sparse.eval_collectBalanced, rawRowCheck8710]

theorem rawRowCheck8711 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form6 = rawRow8711 := by decide +kernel

theorem rowCheck8711 : row8711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8711 := by decide +kernel

theorem rowEval8711 (x : Key → ℝ) : Integer.Sparse.eval row8711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8711, Integer.Sparse.eval_collectBalanced, rawRowCheck8711]

theorem rawRowCheck8712 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8712 := by decide +kernel

theorem rowCheck8712 : row8712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8712 := by decide +kernel

theorem rowEval8712 (x : Key → ℝ) : Integer.Sparse.eval row8712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8712, Integer.Sparse.eval_collectBalanced, rawRowCheck8712]

theorem rawRowCheck8717 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form7 = rawRow8717 := by decide +kernel

theorem rowCheck8717 : row8717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8717 := by decide +kernel

theorem rowEval8717 (x : Key → ℝ) : Integer.Sparse.eval row8717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8717, Integer.Sparse.eval_collectBalanced, rawRowCheck8717]

theorem rawRowCheck8718 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form7 = rawRow8718 := by decide +kernel

theorem rowCheck8718 : row8718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8718 := by decide +kernel

theorem rowEval8718 (x : Key → ℝ) : Integer.Sparse.eval row8718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8718, Integer.Sparse.eval_collectBalanced, rawRowCheck8718]

theorem rawRowCheck8719 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form7 = rawRow8719 := by decide +kernel

theorem rowCheck8719 : row8719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8719 := by decide +kernel

theorem rowEval8719 (x : Key → ℝ) : Integer.Sparse.eval row8719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8719, Integer.Sparse.eval_collectBalanced, rawRowCheck8719]

theorem rawRowCheck8720 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8720 := by decide +kernel

theorem rowCheck8720 : row8720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8720 := by decide +kernel

theorem rowEval8720 (x : Key → ℝ) : Integer.Sparse.eval row8720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8720, Integer.Sparse.eval_collectBalanced, rawRowCheck8720]

theorem rawRowCheck8741 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form10 = rawRow8741 := by decide +kernel

theorem rowCheck8741 : row8741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8741 := by decide +kernel

theorem rowEval8741 (x : Key → ℝ) : Integer.Sparse.eval row8741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8741, Integer.Sparse.eval_collectBalanced, rawRowCheck8741]

theorem rawRowCheck8742 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form10 = rawRow8742 := by decide +kernel

theorem rowCheck8742 : row8742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8742 := by decide +kernel

theorem rowEval8742 (x : Key → ℝ) : Integer.Sparse.eval row8742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8742, Integer.Sparse.eval_collectBalanced, rawRowCheck8742]

theorem rawRowCheck8743 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form10 = rawRow8743 := by decide +kernel

theorem rowCheck8743 : row8743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8743 := by decide +kernel

theorem rowEval8743 (x : Key → ℝ) : Integer.Sparse.eval row8743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8743, Integer.Sparse.eval_collectBalanced, rawRowCheck8743]

theorem rawRowCheck8744 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8744 := by decide +kernel

theorem rowCheck8744 : row8744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8744 := by decide +kernel

theorem rowEval8744 (x : Key → ℝ) : Integer.Sparse.eval row8744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8744, Integer.Sparse.eval_collectBalanced, rawRowCheck8744]

theorem rawRowCheck8749 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form11 = rawRow8749 := by decide +kernel

theorem rowCheck8749 : row8749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8749 := by decide +kernel

theorem rowEval8749 (x : Key → ℝ) : Integer.Sparse.eval row8749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck8749, Integer.Sparse.eval_collectBalanced, rawRowCheck8749]

theorem rawRowCheck8750 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form11 = rawRow8750 := by decide +kernel

theorem rowCheck8750 : row8750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8750 := by decide +kernel

theorem rowEval8750 (x : Key → ℝ) : Integer.Sparse.eval row8750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8750, Integer.Sparse.eval_collectBalanced, rawRowCheck8750]

theorem rawRowCheck8751 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form11 = rawRow8751 := by decide +kernel

theorem rowCheck8751 : row8751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8751 := by decide +kernel

theorem rowEval8751 (x : Key → ℝ) : Integer.Sparse.eval row8751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8751, Integer.Sparse.eval_collectBalanced, rawRowCheck8751]

theorem rawRowCheck8752 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8752 := by decide +kernel

theorem rowCheck8752 : row8752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8752 := by decide +kernel

theorem rowEval8752 (x : Key → ℝ) : Integer.Sparse.eval row8752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8752, Integer.Sparse.eval_collectBalanced, rawRowCheck8752]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck9173 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form0 = rawRow9173 := by decide +kernel

theorem rowCheck9173 : row9173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9173 := by decide +kernel

theorem rowEval9173 (x : Key → ℝ) : Integer.Sparse.eval row9173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9173, Integer.Sparse.eval_collectBalanced, rawRowCheck9173]

theorem rawRowCheck9174 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form0 = rawRow9174 := by decide +kernel

theorem rowCheck9174 : row9174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9174 := by decide +kernel

theorem rowEval9174 (x : Key → ℝ) : Integer.Sparse.eval row9174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9174, Integer.Sparse.eval_collectBalanced, rawRowCheck9174]

theorem rawRowCheck9175 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form0 = rawRow9175 := by decide +kernel

theorem rowCheck9175 : row9175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9175 := by decide +kernel

theorem rowEval9175 (x : Key → ℝ) : Integer.Sparse.eval row9175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9175, Integer.Sparse.eval_collectBalanced, rawRowCheck9175]

theorem rawRowCheck9176 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form0 = rawRow9176 := by decide +kernel

theorem rowCheck9176 : row9176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9176 := by decide +kernel

theorem rowEval9176 (x : Key → ℝ) : Integer.Sparse.eval row9176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9176, Integer.Sparse.eval_collectBalanced, rawRowCheck9176]

theorem rawRowCheck9177 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form0 = rawRow9177 := by decide +kernel

theorem rowCheck9177 : row9177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9177 := by decide +kernel

theorem rowEval9177 (x : Key → ℝ) : Integer.Sparse.eval row9177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9177, Integer.Sparse.eval_collectBalanced, rawRowCheck9177]

theorem rawRowCheck9178 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form0 = rawRow9178 := by decide +kernel

theorem rowCheck9178 : row9178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9178 := by decide +kernel

theorem rowEval9178 (x : Key → ℝ) : Integer.Sparse.eval row9178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9178, Integer.Sparse.eval_collectBalanced, rawRowCheck9178]

theorem rawRowCheck9179 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form0 = rawRow9179 := by decide +kernel

theorem rowCheck9179 : row9179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9179 := by decide +kernel

theorem rowEval9179 (x : Key → ℝ) : Integer.Sparse.eval row9179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9179, Integer.Sparse.eval_collectBalanced, rawRowCheck9179]

theorem rawRowCheck9180 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form0 = rawRow9180 := by decide +kernel

theorem rowCheck9180 : row9180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9180 := by decide +kernel

theorem rowEval9180 (x : Key → ℝ) : Integer.Sparse.eval row9180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9180, Integer.Sparse.eval_collectBalanced, rawRowCheck9180]

theorem rawRowCheck9181 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form0 = rawRow9181 := by decide +kernel

theorem rowCheck9181 : row9181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9181 := by decide +kernel

theorem rowEval9181 (x : Key → ℝ) : Integer.Sparse.eval row9181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9181, Integer.Sparse.eval_collectBalanced, rawRowCheck9181]

theorem rawRowCheck9182 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form0 = rawRow9182 := by decide +kernel

theorem rowCheck9182 : row9182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9182 := by decide +kernel

theorem rowEval9182 (x : Key → ℝ) : Integer.Sparse.eval row9182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9182, Integer.Sparse.eval_collectBalanced, rawRowCheck9182]

theorem rawRowCheck9183 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form0 = rawRow9183 := by decide +kernel

theorem rowCheck9183 : row9183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9183 := by decide +kernel

theorem rowEval9183 (x : Key → ℝ) : Integer.Sparse.eval row9183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9183, Integer.Sparse.eval_collectBalanced, rawRowCheck9183]

theorem rawRowCheck9184 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form0 = rawRow9184 := by decide +kernel

theorem rowCheck9184 : row9184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9184 := by decide +kernel

theorem rowEval9184 (x : Key → ℝ) : Integer.Sparse.eval row9184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9184, Integer.Sparse.eval_collectBalanced, rawRowCheck9184]

theorem rawRowCheck9185 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form1 = rawRow9185 := by decide +kernel

theorem rowCheck9185 : row9185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9185 := by decide +kernel

theorem rowEval9185 (x : Key → ℝ) : Integer.Sparse.eval row9185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9185, Integer.Sparse.eval_collectBalanced, rawRowCheck9185]

theorem rawRowCheck9186 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form1 = rawRow9186 := by decide +kernel

theorem rowCheck9186 : row9186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9186 := by decide +kernel

theorem rowEval9186 (x : Key → ℝ) : Integer.Sparse.eval row9186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9186, Integer.Sparse.eval_collectBalanced, rawRowCheck9186]

theorem rawRowCheck9187 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form1 = rawRow9187 := by decide +kernel

theorem rowCheck9187 : row9187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9187 := by decide +kernel

theorem rowEval9187 (x : Key → ℝ) : Integer.Sparse.eval row9187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9187, Integer.Sparse.eval_collectBalanced, rawRowCheck9187]

theorem rawRowCheck9188 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9188 := by decide +kernel

theorem rowCheck9188 : row9188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9188 := by decide +kernel

theorem rowEval9188 (x : Key → ℝ) : Integer.Sparse.eval row9188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9188, Integer.Sparse.eval_collectBalanced, rawRowCheck9188]

theorem rawRowCheck9189 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9189 := by decide +kernel

theorem rowCheck9189 : row9189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9189 := by decide +kernel

theorem rowEval9189 (x : Key → ℝ) : Integer.Sparse.eval row9189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9189, Integer.Sparse.eval_collectBalanced, rawRowCheck9189]

theorem rawRowCheck9190 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9190 := by decide +kernel

theorem rowCheck9190 : row9190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9190 := by decide +kernel

theorem rowEval9190 (x : Key → ℝ) : Integer.Sparse.eval row9190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9190, Integer.Sparse.eval_collectBalanced, rawRowCheck9190]

theorem rawRowCheck9191 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9191 := by decide +kernel

theorem rowCheck9191 : row9191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9191 := by decide +kernel

theorem rowEval9191 (x : Key → ℝ) : Integer.Sparse.eval row9191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9191, Integer.Sparse.eval_collectBalanced, rawRowCheck9191]

theorem rawRowCheck9192 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9192 := by decide +kernel

theorem rowCheck9192 : row9192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9192 := by decide +kernel

theorem rowEval9192 (x : Key → ℝ) : Integer.Sparse.eval row9192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9192, Integer.Sparse.eval_collectBalanced, rawRowCheck9192]

theorem rawRowCheck9193 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9193 := by decide +kernel

theorem rowCheck9193 : row9193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9193 := by decide +kernel

theorem rowEval9193 (x : Key → ℝ) : Integer.Sparse.eval row9193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9193, Integer.Sparse.eval_collectBalanced, rawRowCheck9193]

theorem rawRowCheck9194 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9194 := by decide +kernel

theorem rowCheck9194 : row9194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9194 := by decide +kernel

theorem rowEval9194 (x : Key → ℝ) : Integer.Sparse.eval row9194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9194, Integer.Sparse.eval_collectBalanced, rawRowCheck9194]

theorem rawRowCheck9195 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9195 := by decide +kernel

theorem rowCheck9195 : row9195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9195 := by decide +kernel

theorem rowEval9195 (x : Key → ℝ) : Integer.Sparse.eval row9195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9195, Integer.Sparse.eval_collectBalanced, rawRowCheck9195]

theorem rawRowCheck9196 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9196 := by decide +kernel

theorem rowCheck9196 : row9196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9196 := by decide +kernel

theorem rowEval9196 (x : Key → ℝ) : Integer.Sparse.eval row9196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9196, Integer.Sparse.eval_collectBalanced, rawRowCheck9196]

theorem rawRowCheck9197 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form2 = rawRow9197 := by decide +kernel

theorem rowCheck9197 : row9197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9197 := by decide +kernel

theorem rowEval9197 (x : Key → ℝ) : Integer.Sparse.eval row9197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9197, Integer.Sparse.eval_collectBalanced, rawRowCheck9197]

theorem rawRowCheck9198 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form2 = rawRow9198 := by decide +kernel

theorem rowCheck9198 : row9198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9198 := by decide +kernel

theorem rowEval9198 (x : Key → ℝ) : Integer.Sparse.eval row9198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9198, Integer.Sparse.eval_collectBalanced, rawRowCheck9198]

theorem rawRowCheck9199 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form2 = rawRow9199 := by decide +kernel

theorem rowCheck9199 : row9199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9199 := by decide +kernel

theorem rowEval9199 (x : Key → ℝ) : Integer.Sparse.eval row9199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9199, Integer.Sparse.eval_collectBalanced, rawRowCheck9199]

theorem rawRowCheck9200 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9200 := by decide +kernel

theorem rowCheck9200 : row9200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9200 := by decide +kernel

theorem rowEval9200 (x : Key → ℝ) : Integer.Sparse.eval row9200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9200, Integer.Sparse.eval_collectBalanced, rawRowCheck9200]

theorem rawRowCheck9201 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9201 := by decide +kernel

theorem rowCheck9201 : row9201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9201 := by decide +kernel

theorem rowEval9201 (x : Key → ℝ) : Integer.Sparse.eval row9201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9201, Integer.Sparse.eval_collectBalanced, rawRowCheck9201]

theorem rawRowCheck9202 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9202 := by decide +kernel

theorem rowCheck9202 : row9202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9202 := by decide +kernel

theorem rowEval9202 (x : Key → ℝ) : Integer.Sparse.eval row9202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9202, Integer.Sparse.eval_collectBalanced, rawRowCheck9202]

theorem rawRowCheck9203 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9203 := by decide +kernel

theorem rowCheck9203 : row9203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9203 := by decide +kernel

theorem rowEval9203 (x : Key → ℝ) : Integer.Sparse.eval row9203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9203, Integer.Sparse.eval_collectBalanced, rawRowCheck9203]

theorem rawRowCheck9204 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form2 = rawRow9204 := by decide +kernel

theorem rowCheck9204 : row9204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9204 := by decide +kernel

theorem rowEval9204 (x : Key → ℝ) : Integer.Sparse.eval row9204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9204, Integer.Sparse.eval_collectBalanced, rawRowCheck9204]

theorem rawRowCheck9205 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form2 = rawRow9205 := by decide +kernel

theorem rowCheck9205 : row9205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9205 := by decide +kernel

theorem rowEval9205 (x : Key → ℝ) : Integer.Sparse.eval row9205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9205, Integer.Sparse.eval_collectBalanced, rawRowCheck9205]

theorem rawRowCheck9206 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form2 = rawRow9206 := by decide +kernel

theorem rowCheck9206 : row9206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9206 := by decide +kernel

theorem rowEval9206 (x : Key → ℝ) : Integer.Sparse.eval row9206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9206, Integer.Sparse.eval_collectBalanced, rawRowCheck9206]

theorem rawRowCheck9207 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form2 = rawRow9207 := by decide +kernel

theorem rowCheck9207 : row9207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9207 := by decide +kernel

theorem rowEval9207 (x : Key → ℝ) : Integer.Sparse.eval row9207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9207, Integer.Sparse.eval_collectBalanced, rawRowCheck9207]

theorem rawRowCheck9208 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form2 = rawRow9208 := by decide +kernel

theorem rowCheck9208 : row9208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9208 := by decide +kernel

theorem rowEval9208 (x : Key → ℝ) : Integer.Sparse.eval row9208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9208, Integer.Sparse.eval_collectBalanced, rawRowCheck9208]

theorem rawRowCheck9209 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form3 = rawRow9209 := by decide +kernel

theorem rowCheck9209 : row9209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9209 := by decide +kernel

theorem rowEval9209 (x : Key → ℝ) : Integer.Sparse.eval row9209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9209, Integer.Sparse.eval_collectBalanced, rawRowCheck9209]

theorem rawRowCheck9210 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form3 = rawRow9210 := by decide +kernel

theorem rowCheck9210 : row9210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9210 := by decide +kernel

theorem rowEval9210 (x : Key → ℝ) : Integer.Sparse.eval row9210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9210, Integer.Sparse.eval_collectBalanced, rawRowCheck9210]

theorem rawRowCheck9211 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form3 = rawRow9211 := by decide +kernel

theorem rowCheck9211 : row9211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9211 := by decide +kernel

theorem rowEval9211 (x : Key → ℝ) : Integer.Sparse.eval row9211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9211, Integer.Sparse.eval_collectBalanced, rawRowCheck9211]

theorem rawRowCheck9212 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form3 = rawRow9212 := by decide +kernel

theorem rowCheck9212 : row9212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9212 := by decide +kernel

theorem rowEval9212 (x : Key → ℝ) : Integer.Sparse.eval row9212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9212, Integer.Sparse.eval_collectBalanced, rawRowCheck9212]

theorem rawRowCheck9213 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form3 = rawRow9213 := by decide +kernel

theorem rowCheck9213 : row9213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9213 := by decide +kernel

theorem rowEval9213 (x : Key → ℝ) : Integer.Sparse.eval row9213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9213, Integer.Sparse.eval_collectBalanced, rawRowCheck9213]

theorem rawRowCheck9214 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form3 = rawRow9214 := by decide +kernel

theorem rowCheck9214 : row9214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9214 := by decide +kernel

theorem rowEval9214 (x : Key → ℝ) : Integer.Sparse.eval row9214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9214, Integer.Sparse.eval_collectBalanced, rawRowCheck9214]

theorem rawRowCheck9215 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form3 = rawRow9215 := by decide +kernel

theorem rowCheck9215 : row9215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9215 := by decide +kernel

theorem rowEval9215 (x : Key → ℝ) : Integer.Sparse.eval row9215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9215, Integer.Sparse.eval_collectBalanced, rawRowCheck9215]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck9216 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form3 = rawRow9216 := by decide +kernel

theorem rowCheck9216 : row9216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9216 := by decide +kernel

theorem rowEval9216 (x : Key → ℝ) : Integer.Sparse.eval row9216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9216, Integer.Sparse.eval_collectBalanced, rawRowCheck9216]

theorem rawRowCheck9217 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form3 = rawRow9217 := by decide +kernel

theorem rowCheck9217 : row9217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9217 := by decide +kernel

theorem rowEval9217 (x : Key → ℝ) : Integer.Sparse.eval row9217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9217, Integer.Sparse.eval_collectBalanced, rawRowCheck9217]

theorem rawRowCheck9218 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form3 = rawRow9218 := by decide +kernel

theorem rowCheck9218 : row9218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9218 := by decide +kernel

theorem rowEval9218 (x : Key → ℝ) : Integer.Sparse.eval row9218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9218, Integer.Sparse.eval_collectBalanced, rawRowCheck9218]

theorem rawRowCheck9219 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form3 = rawRow9219 := by decide +kernel

theorem rowCheck9219 : row9219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9219 := by decide +kernel

theorem rowEval9219 (x : Key → ℝ) : Integer.Sparse.eval row9219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9219, Integer.Sparse.eval_collectBalanced, rawRowCheck9219]

theorem rawRowCheck9220 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form3 = rawRow9220 := by decide +kernel

theorem rowCheck9220 : row9220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9220 := by decide +kernel

theorem rowEval9220 (x : Key → ℝ) : Integer.Sparse.eval row9220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9220, Integer.Sparse.eval_collectBalanced, rawRowCheck9220]

theorem rawRowCheck9221 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form4 = rawRow9221 := by decide +kernel

theorem rowCheck9221 : row9221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9221 := by decide +kernel

theorem rowEval9221 (x : Key → ℝ) : Integer.Sparse.eval row9221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9221, Integer.Sparse.eval_collectBalanced, rawRowCheck9221]

theorem rawRowCheck9222 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form4 = rawRow9222 := by decide +kernel

theorem rowCheck9222 : row9222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9222 := by decide +kernel

theorem rowEval9222 (x : Key → ℝ) : Integer.Sparse.eval row9222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9222, Integer.Sparse.eval_collectBalanced, rawRowCheck9222]

theorem rawRowCheck9223 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form4 = rawRow9223 := by decide +kernel

theorem rowCheck9223 : row9223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9223 := by decide +kernel

theorem rowEval9223 (x : Key → ℝ) : Integer.Sparse.eval row9223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9223, Integer.Sparse.eval_collectBalanced, rawRowCheck9223]

theorem rawRowCheck9224 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form4 = rawRow9224 := by decide +kernel

theorem rowCheck9224 : row9224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9224 := by decide +kernel

theorem rowEval9224 (x : Key → ℝ) : Integer.Sparse.eval row9224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9224, Integer.Sparse.eval_collectBalanced, rawRowCheck9224]

theorem rawRowCheck9225 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form4 = rawRow9225 := by decide +kernel

theorem rowCheck9225 : row9225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9225 := by decide +kernel

theorem rowEval9225 (x : Key → ℝ) : Integer.Sparse.eval row9225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9225, Integer.Sparse.eval_collectBalanced, rawRowCheck9225]

theorem rawRowCheck9226 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form4 = rawRow9226 := by decide +kernel

theorem rowCheck9226 : row9226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9226 := by decide +kernel

theorem rowEval9226 (x : Key → ℝ) : Integer.Sparse.eval row9226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9226, Integer.Sparse.eval_collectBalanced, rawRowCheck9226]

theorem rawRowCheck9227 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form4 = rawRow9227 := by decide +kernel

theorem rowCheck9227 : row9227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9227 := by decide +kernel

theorem rowEval9227 (x : Key → ℝ) : Integer.Sparse.eval row9227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9227, Integer.Sparse.eval_collectBalanced, rawRowCheck9227]

theorem rawRowCheck9228 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form4 = rawRow9228 := by decide +kernel

theorem rowCheck9228 : row9228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9228 := by decide +kernel

theorem rowEval9228 (x : Key → ℝ) : Integer.Sparse.eval row9228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9228, Integer.Sparse.eval_collectBalanced, rawRowCheck9228]

theorem rawRowCheck9229 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form4 = rawRow9229 := by decide +kernel

theorem rowCheck9229 : row9229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9229 := by decide +kernel

theorem rowEval9229 (x : Key → ℝ) : Integer.Sparse.eval row9229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9229, Integer.Sparse.eval_collectBalanced, rawRowCheck9229]

theorem rawRowCheck9230 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form4 = rawRow9230 := by decide +kernel

theorem rowCheck9230 : row9230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9230 := by decide +kernel

theorem rowEval9230 (x : Key → ℝ) : Integer.Sparse.eval row9230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9230, Integer.Sparse.eval_collectBalanced, rawRowCheck9230]

theorem rawRowCheck9231 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form4 = rawRow9231 := by decide +kernel

theorem rowCheck9231 : row9231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9231 := by decide +kernel

theorem rowEval9231 (x : Key → ℝ) : Integer.Sparse.eval row9231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9231, Integer.Sparse.eval_collectBalanced, rawRowCheck9231]

theorem rawRowCheck9232 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form4 = rawRow9232 := by decide +kernel

theorem rowCheck9232 : row9232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9232 := by decide +kernel

theorem rowEval9232 (x : Key → ℝ) : Integer.Sparse.eval row9232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9232, Integer.Sparse.eval_collectBalanced, rawRowCheck9232]

theorem rawRowCheck9245 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form6 = rawRow9245 := by decide +kernel

theorem rowCheck9245 : row9245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9245 := by decide +kernel

theorem rowEval9245 (x : Key → ℝ) : Integer.Sparse.eval row9245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9245, Integer.Sparse.eval_collectBalanced, rawRowCheck9245]

theorem rawRowCheck9246 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form6 = rawRow9246 := by decide +kernel

theorem rowCheck9246 : row9246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9246 := by decide +kernel

theorem rowEval9246 (x : Key → ℝ) : Integer.Sparse.eval row9246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9246, Integer.Sparse.eval_collectBalanced, rawRowCheck9246]

theorem rawRowCheck9247 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form6 = rawRow9247 := by decide +kernel

theorem rowCheck9247 : row9247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9247 := by decide +kernel

theorem rowEval9247 (x : Key → ℝ) : Integer.Sparse.eval row9247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9247, Integer.Sparse.eval_collectBalanced, rawRowCheck9247]

theorem rawRowCheck9248 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form6 = rawRow9248 := by decide +kernel

theorem rowCheck9248 : row9248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9248 := by decide +kernel

theorem rowEval9248 (x : Key → ℝ) : Integer.Sparse.eval row9248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9248, Integer.Sparse.eval_collectBalanced, rawRowCheck9248]

theorem rawRowCheck9249 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form6 = rawRow9249 := by decide +kernel

theorem rowCheck9249 : row9249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9249 := by decide +kernel

theorem rowEval9249 (x : Key → ℝ) : Integer.Sparse.eval row9249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9249, Integer.Sparse.eval_collectBalanced, rawRowCheck9249]

theorem rawRowCheck9250 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form6 = rawRow9250 := by decide +kernel

theorem rowCheck9250 : row9250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9250 := by decide +kernel

theorem rowEval9250 (x : Key → ℝ) : Integer.Sparse.eval row9250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9250, Integer.Sparse.eval_collectBalanced, rawRowCheck9250]

theorem rawRowCheck9251 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form6 = rawRow9251 := by decide +kernel

theorem rowCheck9251 : row9251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9251 := by decide +kernel

theorem rowEval9251 (x : Key → ℝ) : Integer.Sparse.eval row9251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9251, Integer.Sparse.eval_collectBalanced, rawRowCheck9251]

theorem rawRowCheck9252 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form6 = rawRow9252 := by decide +kernel

theorem rowCheck9252 : row9252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9252 := by decide +kernel

theorem rowEval9252 (x : Key → ℝ) : Integer.Sparse.eval row9252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9252, Integer.Sparse.eval_collectBalanced, rawRowCheck9252]

theorem rawRowCheck9253 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form6 = rawRow9253 := by decide +kernel

theorem rowCheck9253 : row9253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9253 := by decide +kernel

theorem rowEval9253 (x : Key → ℝ) : Integer.Sparse.eval row9253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9253, Integer.Sparse.eval_collectBalanced, rawRowCheck9253]

theorem rawRowCheck9254 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form6 = rawRow9254 := by decide +kernel

theorem rowCheck9254 : row9254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9254 := by decide +kernel

theorem rowEval9254 (x : Key → ℝ) : Integer.Sparse.eval row9254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9254, Integer.Sparse.eval_collectBalanced, rawRowCheck9254]

theorem rawRowCheck9255 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form6 = rawRow9255 := by decide +kernel

theorem rowCheck9255 : row9255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9255 := by decide +kernel

theorem rowEval9255 (x : Key → ℝ) : Integer.Sparse.eval row9255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9255, Integer.Sparse.eval_collectBalanced, rawRowCheck9255]

theorem rawRowCheck9256 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form6 = rawRow9256 := by decide +kernel

theorem rowCheck9256 : row9256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9256 := by decide +kernel

theorem rowEval9256 (x : Key → ℝ) : Integer.Sparse.eval row9256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9256, Integer.Sparse.eval_collectBalanced, rawRowCheck9256]

theorem rawRowCheck9257 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form7 = rawRow9257 := by decide +kernel

theorem rowCheck9257 : row9257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9257 := by decide +kernel

theorem rowEval9257 (x : Key → ℝ) : Integer.Sparse.eval row9257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9257, Integer.Sparse.eval_collectBalanced, rawRowCheck9257]

theorem rawRowCheck9258 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form7 = rawRow9258 := by decide +kernel

theorem rowCheck9258 : row9258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9258 := by decide +kernel

theorem rowEval9258 (x : Key → ℝ) : Integer.Sparse.eval row9258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9258, Integer.Sparse.eval_collectBalanced, rawRowCheck9258]

theorem rawRowCheck9259 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form7 = rawRow9259 := by decide +kernel

theorem rowCheck9259 : row9259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9259 := by decide +kernel

theorem rowEval9259 (x : Key → ℝ) : Integer.Sparse.eval row9259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9259, Integer.Sparse.eval_collectBalanced, rawRowCheck9259]

theorem rawRowCheck9260 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form7 = rawRow9260 := by decide +kernel

theorem rowCheck9260 : row9260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9260 := by decide +kernel

theorem rowEval9260 (x : Key → ℝ) : Integer.Sparse.eval row9260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9260, Integer.Sparse.eval_collectBalanced, rawRowCheck9260]

theorem rawRowCheck9261 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form7 = rawRow9261 := by decide +kernel

theorem rowCheck9261 : row9261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9261 := by decide +kernel

theorem rowEval9261 (x : Key → ℝ) : Integer.Sparse.eval row9261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9261, Integer.Sparse.eval_collectBalanced, rawRowCheck9261]

theorem rawRowCheck9262 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form7 = rawRow9262 := by decide +kernel

theorem rowCheck9262 : row9262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9262 := by decide +kernel

theorem rowEval9262 (x : Key → ℝ) : Integer.Sparse.eval row9262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9262, Integer.Sparse.eval_collectBalanced, rawRowCheck9262]

theorem rawRowCheck9263 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form7 = rawRow9263 := by decide +kernel

theorem rowCheck9263 : row9263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9263 := by decide +kernel

theorem rowEval9263 (x : Key → ℝ) : Integer.Sparse.eval row9263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9263, Integer.Sparse.eval_collectBalanced, rawRowCheck9263]

theorem rawRowCheck9264 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form7 = rawRow9264 := by decide +kernel

theorem rowCheck9264 : row9264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9264 := by decide +kernel

theorem rowEval9264 (x : Key → ℝ) : Integer.Sparse.eval row9264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9264, Integer.Sparse.eval_collectBalanced, rawRowCheck9264]

theorem rawRowCheck9265 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form7 = rawRow9265 := by decide +kernel

theorem rowCheck9265 : row9265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9265 := by decide +kernel

theorem rowEval9265 (x : Key → ℝ) : Integer.Sparse.eval row9265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9265, Integer.Sparse.eval_collectBalanced, rawRowCheck9265]

theorem rawRowCheck9266 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form7 = rawRow9266 := by decide +kernel

theorem rowCheck9266 : row9266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9266 := by decide +kernel

theorem rowEval9266 (x : Key → ℝ) : Integer.Sparse.eval row9266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9266, Integer.Sparse.eval_collectBalanced, rawRowCheck9266]

theorem rawRowCheck9267 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form7 = rawRow9267 := by decide +kernel

theorem rowCheck9267 : row9267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9267 := by decide +kernel

theorem rowEval9267 (x : Key → ℝ) : Integer.Sparse.eval row9267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9267, Integer.Sparse.eval_collectBalanced, rawRowCheck9267]

theorem rawRowCheck9268 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form7 = rawRow9268 := by decide +kernel

theorem rowCheck9268 : row9268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9268 := by decide +kernel

theorem rowEval9268 (x : Key → ℝ) : Integer.Sparse.eval row9268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9268, Integer.Sparse.eval_collectBalanced, rawRowCheck9268]

theorem rawRowCheck9293 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form10 = rawRow9293 := by decide +kernel

theorem rowCheck9293 : row9293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9293 := by decide +kernel

theorem rowEval9293 (x : Key → ℝ) : Integer.Sparse.eval row9293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9293, Integer.Sparse.eval_collectBalanced, rawRowCheck9293]

theorem rawRowCheck9294 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form10 = rawRow9294 := by decide +kernel

theorem rowCheck9294 : row9294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9294 := by decide +kernel

theorem rowEval9294 (x : Key → ℝ) : Integer.Sparse.eval row9294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9294, Integer.Sparse.eval_collectBalanced, rawRowCheck9294]

theorem rawRowCheck9295 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form10 = rawRow9295 := by decide +kernel

theorem rowCheck9295 : row9295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9295 := by decide +kernel

theorem rowEval9295 (x : Key → ℝ) : Integer.Sparse.eval row9295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9295, Integer.Sparse.eval_collectBalanced, rawRowCheck9295]

theorem rawRowCheck9296 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form10 = rawRow9296 := by decide +kernel

theorem rowCheck9296 : row9296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9296 := by decide +kernel

theorem rowEval9296 (x : Key → ℝ) : Integer.Sparse.eval row9296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9296, Integer.Sparse.eval_collectBalanced, rawRowCheck9296]

theorem rawRowCheck9297 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form10 = rawRow9297 := by decide +kernel

theorem rowCheck9297 : row9297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9297 := by decide +kernel

theorem rowEval9297 (x : Key → ℝ) : Integer.Sparse.eval row9297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9297, Integer.Sparse.eval_collectBalanced, rawRowCheck9297]

theorem rawRowCheck9298 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form10 = rawRow9298 := by decide +kernel

theorem rowCheck9298 : row9298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9298 := by decide +kernel

theorem rowEval9298 (x : Key → ℝ) : Integer.Sparse.eval row9298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9298, Integer.Sparse.eval_collectBalanced, rawRowCheck9298]

theorem rawRowCheck9299 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form10 = rawRow9299 := by decide +kernel

theorem rowCheck9299 : row9299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9299 := by decide +kernel

theorem rowEval9299 (x : Key → ℝ) : Integer.Sparse.eval row9299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9299, Integer.Sparse.eval_collectBalanced, rawRowCheck9299]

theorem rawRowCheck9300 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form10 = rawRow9300 := by decide +kernel

theorem rowCheck9300 : row9300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9300 := by decide +kernel

theorem rowEval9300 (x : Key → ℝ) : Integer.Sparse.eval row9300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9300, Integer.Sparse.eval_collectBalanced, rawRowCheck9300]

theorem rawRowCheck9301 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form10 = rawRow9301 := by decide +kernel

theorem rowCheck9301 : row9301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9301 := by decide +kernel

theorem rowEval9301 (x : Key → ℝ) : Integer.Sparse.eval row9301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9301, Integer.Sparse.eval_collectBalanced, rawRowCheck9301]

theorem rawRowCheck9302 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form10 = rawRow9302 := by decide +kernel

theorem rowCheck9302 : row9302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9302 := by decide +kernel

theorem rowEval9302 (x : Key → ℝ) : Integer.Sparse.eval row9302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9302, Integer.Sparse.eval_collectBalanced, rawRowCheck9302]

theorem rawRowCheck9303 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form10 = rawRow9303 := by decide +kernel

theorem rowCheck9303 : row9303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9303 := by decide +kernel

theorem rowEval9303 (x : Key → ℝ) : Integer.Sparse.eval row9303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9303, Integer.Sparse.eval_collectBalanced, rawRowCheck9303]

theorem rawRowCheck9304 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form10 = rawRow9304 := by decide +kernel

theorem rowCheck9304 : row9304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9304 := by decide +kernel

theorem rowEval9304 (x : Key → ℝ) : Integer.Sparse.eval row9304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9304, Integer.Sparse.eval_collectBalanced, rawRowCheck9304]

theorem rawRowCheck9305 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form11 = rawRow9305 := by decide +kernel

theorem rowCheck9305 : row9305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9305 := by decide +kernel

theorem rowEval9305 (x : Key → ℝ) : Integer.Sparse.eval row9305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9305, Integer.Sparse.eval_collectBalanced, rawRowCheck9305]

theorem rawRowCheck9306 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form11 = rawRow9306 := by decide +kernel

theorem rowCheck9306 : row9306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9306 := by decide +kernel

theorem rowEval9306 (x : Key → ℝ) : Integer.Sparse.eval row9306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9306, Integer.Sparse.eval_collectBalanced, rawRowCheck9306]

theorem rawRowCheck9307 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form11 = rawRow9307 := by decide +kernel

theorem rowCheck9307 : row9307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9307 := by decide +kernel

theorem rowEval9307 (x : Key → ℝ) : Integer.Sparse.eval row9307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9307, Integer.Sparse.eval_collectBalanced, rawRowCheck9307]

theorem rawRowCheck9308 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form11 = rawRow9308 := by decide +kernel

theorem rowCheck9308 : row9308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9308 := by decide +kernel

theorem rowEval9308 (x : Key → ℝ) : Integer.Sparse.eval row9308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9308, Integer.Sparse.eval_collectBalanced, rawRowCheck9308]

theorem rawRowCheck9309 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form11 = rawRow9309 := by decide +kernel

theorem rowCheck9309 : row9309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9309 := by decide +kernel

theorem rowEval9309 (x : Key → ℝ) : Integer.Sparse.eval row9309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9309, Integer.Sparse.eval_collectBalanced, rawRowCheck9309]

theorem rawRowCheck9310 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form11 = rawRow9310 := by decide +kernel

theorem rowCheck9310 : row9310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9310 := by decide +kernel

theorem rowEval9310 (x : Key → ℝ) : Integer.Sparse.eval row9310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9310, Integer.Sparse.eval_collectBalanced, rawRowCheck9310]

theorem rawRowCheck9311 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form11 = rawRow9311 := by decide +kernel

theorem rowCheck9311 : row9311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9311 := by decide +kernel

theorem rowEval9311 (x : Key → ℝ) : Integer.Sparse.eval row9311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9311, Integer.Sparse.eval_collectBalanced, rawRowCheck9311]

theorem rawRowCheck9312 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form11 = rawRow9312 := by decide +kernel

theorem rowCheck9312 : row9312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9312 := by decide +kernel

theorem rowEval9312 (x : Key → ℝ) : Integer.Sparse.eval row9312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9312, Integer.Sparse.eval_collectBalanced, rawRowCheck9312]

theorem rawRowCheck9313 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form11 = rawRow9313 := by decide +kernel

theorem rowCheck9313 : row9313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9313 := by decide +kernel

theorem rowEval9313 (x : Key → ℝ) : Integer.Sparse.eval row9313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9313, Integer.Sparse.eval_collectBalanced, rawRowCheck9313]

theorem rawRowCheck9314 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form11 = rawRow9314 := by decide +kernel

theorem rowCheck9314 : row9314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9314 := by decide +kernel

theorem rowEval9314 (x : Key → ℝ) : Integer.Sparse.eval row9314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9314, Integer.Sparse.eval_collectBalanced, rawRowCheck9314]

theorem rawRowCheck9315 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form11 = rawRow9315 := by decide +kernel

theorem rowCheck9315 : row9315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9315 := by decide +kernel

theorem rowEval9315 (x : Key → ℝ) : Integer.Sparse.eval row9315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9315, Integer.Sparse.eval_collectBalanced, rawRowCheck9315]

theorem rawRowCheck9316 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form11 = rawRow9316 := by decide +kernel

theorem rowCheck9316 : row9316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9316 := by decide +kernel

theorem rowEval9316 (x : Key → ℝ) : Integer.Sparse.eval row9316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9316, Integer.Sparse.eval_collectBalanced, rawRowCheck9316]

theorem rawRowCheck9317 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form12 = rawRow9317 := by decide +kernel

theorem rowCheck9317 : row9317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9317 := by decide +kernel

theorem rowEval9317 (x : Key → ℝ) : Integer.Sparse.eval row9317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9317, Integer.Sparse.eval_collectBalanced, rawRowCheck9317]

theorem rawRowCheck9318 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form12 = rawRow9318 := by decide +kernel

theorem rowCheck9318 : row9318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9318 := by decide +kernel

theorem rowEval9318 (x : Key → ℝ) : Integer.Sparse.eval row9318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9318, Integer.Sparse.eval_collectBalanced, rawRowCheck9318]

theorem rawRowCheck9319 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form12 = rawRow9319 := by decide +kernel

theorem rowCheck9319 : row9319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9319 := by decide +kernel

theorem rowEval9319 (x : Key → ℝ) : Integer.Sparse.eval row9319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9319, Integer.Sparse.eval_collectBalanced, rawRowCheck9319]

theorem rawRowCheck9320 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9320 := by decide +kernel

theorem rowCheck9320 : row9320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9320 := by decide +kernel

theorem rowEval9320 (x : Key → ℝ) : Integer.Sparse.eval row9320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9320, Integer.Sparse.eval_collectBalanced, rawRowCheck9320]

theorem rawRowCheck9321 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form12 = rawRow9321 := by decide +kernel

theorem rowCheck9321 : row9321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9321 := by decide +kernel

theorem rowEval9321 (x : Key → ℝ) : Integer.Sparse.eval row9321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9321, Integer.Sparse.eval_collectBalanced, rawRowCheck9321]

theorem rawRowCheck9322 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form12 = rawRow9322 := by decide +kernel

theorem rowCheck9322 : row9322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9322 := by decide +kernel

theorem rowEval9322 (x : Key → ℝ) : Integer.Sparse.eval row9322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9322, Integer.Sparse.eval_collectBalanced, rawRowCheck9322]

theorem rawRowCheck9323 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form12 = rawRow9323 := by decide +kernel

theorem rowCheck9323 : row9323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9323 := by decide +kernel

theorem rowEval9323 (x : Key → ℝ) : Integer.Sparse.eval row9323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9323, Integer.Sparse.eval_collectBalanced, rawRowCheck9323]

theorem rawRowCheck9324 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form12 = rawRow9324 := by decide +kernel

theorem rowCheck9324 : row9324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9324 := by decide +kernel

theorem rowEval9324 (x : Key → ℝ) : Integer.Sparse.eval row9324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9324, Integer.Sparse.eval_collectBalanced, rawRowCheck9324]

theorem rawRowCheck9325 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form12 = rawRow9325 := by decide +kernel

theorem rowCheck9325 : row9325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9325 := by decide +kernel

theorem rowEval9325 (x : Key → ℝ) : Integer.Sparse.eval row9325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9325, Integer.Sparse.eval_collectBalanced, rawRowCheck9325]

theorem rawRowCheck9326 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form12 = rawRow9326 := by decide +kernel

theorem rowCheck9326 : row9326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9326 := by decide +kernel

theorem rowEval9326 (x : Key → ℝ) : Integer.Sparse.eval row9326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9326, Integer.Sparse.eval_collectBalanced, rawRowCheck9326]

theorem rawRowCheck9327 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form12 = rawRow9327 := by decide +kernel

theorem rowCheck9327 : row9327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9327 := by decide +kernel

theorem rowEval9327 (x : Key → ℝ) : Integer.Sparse.eval row9327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9327, Integer.Sparse.eval_collectBalanced, rawRowCheck9327]

theorem rawRowCheck9328 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form12 = rawRow9328 := by decide +kernel

theorem rowCheck9328 : row9328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9328 := by decide +kernel

theorem rowEval9328 (x : Key → ℝ) : Integer.Sparse.eval row9328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9328, Integer.Sparse.eval_collectBalanced, rawRowCheck9328]

theorem rawRowCheck9329 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form12 = rawRow9329 := by decide +kernel

theorem rowCheck9329 : row9329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9329 := by decide +kernel

theorem rowEval9329 (x : Key → ℝ) : Integer.Sparse.eval row9329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9329, Integer.Sparse.eval_collectBalanced, rawRowCheck9329]

theorem rawRowCheck9330 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form12 = rawRow9330 := by decide +kernel

theorem rowCheck9330 : row9330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9330 := by decide +kernel

theorem rowEval9330 (x : Key → ℝ) : Integer.Sparse.eval row9330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9330, Integer.Sparse.eval_collectBalanced, rawRowCheck9330]

theorem rawRowCheck9331 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form12 = rawRow9331 := by decide +kernel

theorem rowCheck9331 : row9331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9331 := by decide +kernel

theorem rowEval9331 (x : Key → ℝ) : Integer.Sparse.eval row9331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9331, Integer.Sparse.eval_collectBalanced, rawRowCheck9331]

theorem rawRowCheck9332 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form12 = rawRow9332 := by decide +kernel

theorem rowCheck9332 : row9332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9332 := by decide +kernel

theorem rowEval9332 (x : Key → ℝ) : Integer.Sparse.eval row9332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9332, Integer.Sparse.eval_collectBalanced, rawRowCheck9332]

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

theorem rawRowCheck9349 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form14 = rawRow9349 := by decide +kernel

theorem rowCheck9349 : row9349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9349 := by decide +kernel

theorem rowEval9349 (x : Key → ℝ) : Integer.Sparse.eval row9349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9349, Integer.Sparse.eval_collectBalanced, rawRowCheck9349]

theorem rawRowCheck9350 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form14 = rawRow9350 := by decide +kernel

theorem rowCheck9350 : row9350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9350 := by decide +kernel

theorem rowEval9350 (x : Key → ℝ) : Integer.Sparse.eval row9350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9350, Integer.Sparse.eval_collectBalanced, rawRowCheck9350]

theorem rawRowCheck9351 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form14 = rawRow9351 := by decide +kernel

theorem rowCheck9351 : row9351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9351 := by decide +kernel

theorem rowEval9351 (x : Key → ℝ) : Integer.Sparse.eval row9351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9351, Integer.Sparse.eval_collectBalanced, rawRowCheck9351]

theorem rawRowCheck9352 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9352 := by decide +kernel

theorem rowCheck9352 : row9352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9352 := by decide +kernel

theorem rowEval9352 (x : Key → ℝ) : Integer.Sparse.eval row9352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9352, Integer.Sparse.eval_collectBalanced, rawRowCheck9352]

theorem rawRowCheck9353 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form14 = rawRow9353 := by decide +kernel

theorem rowCheck9353 : row9353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9353 := by decide +kernel

theorem rowEval9353 (x : Key → ℝ) : Integer.Sparse.eval row9353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9353, Integer.Sparse.eval_collectBalanced, rawRowCheck9353]

theorem rawRowCheck9354 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form14 = rawRow9354 := by decide +kernel

theorem rowCheck9354 : row9354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9354 := by decide +kernel

theorem rowEval9354 (x : Key → ℝ) : Integer.Sparse.eval row9354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9354, Integer.Sparse.eval_collectBalanced, rawRowCheck9354]

theorem rawRowCheck9355 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form14 = rawRow9355 := by decide +kernel

theorem rowCheck9355 : row9355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9355 := by decide +kernel

theorem rowEval9355 (x : Key → ℝ) : Integer.Sparse.eval row9355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9355, Integer.Sparse.eval_collectBalanced, rawRowCheck9355]

theorem rawRowCheck9356 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form14 = rawRow9356 := by decide +kernel

theorem rowCheck9356 : row9356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9356 := by decide +kernel

theorem rowEval9356 (x : Key → ℝ) : Integer.Sparse.eval row9356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9356, Integer.Sparse.eval_collectBalanced, rawRowCheck9356]

theorem rawRowCheck9357 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form14 = rawRow9357 := by decide +kernel

theorem rowCheck9357 : row9357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9357 := by decide +kernel

theorem rowEval9357 (x : Key → ℝ) : Integer.Sparse.eval row9357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9357, Integer.Sparse.eval_collectBalanced, rawRowCheck9357]

theorem rawRowCheck9358 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form14 = rawRow9358 := by decide +kernel

theorem rowCheck9358 : row9358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9358 := by decide +kernel

theorem rowEval9358 (x : Key → ℝ) : Integer.Sparse.eval row9358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9358, Integer.Sparse.eval_collectBalanced, rawRowCheck9358]

theorem rawRowCheck9359 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form14 = rawRow9359 := by decide +kernel

theorem rowCheck9359 : row9359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9359 := by decide +kernel

theorem rowEval9359 (x : Key → ℝ) : Integer.Sparse.eval row9359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9359, Integer.Sparse.eval_collectBalanced, rawRowCheck9359]

theorem rawRowCheck9360 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form14 = rawRow9360 := by decide +kernel

theorem rowCheck9360 : row9360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9360 := by decide +kernel

theorem rowEval9360 (x : Key → ℝ) : Integer.Sparse.eval row9360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9360, Integer.Sparse.eval_collectBalanced, rawRowCheck9360]

theorem rawRowCheck9361 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form14 = rawRow9361 := by decide +kernel

theorem rowCheck9361 : row9361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9361 := by decide +kernel

theorem rowEval9361 (x : Key → ℝ) : Integer.Sparse.eval row9361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9361, Integer.Sparse.eval_collectBalanced, rawRowCheck9361]

theorem rawRowCheck9362 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form14 = rawRow9362 := by decide +kernel

theorem rowCheck9362 : row9362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9362 := by decide +kernel

theorem rowEval9362 (x : Key → ℝ) : Integer.Sparse.eval row9362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9362, Integer.Sparse.eval_collectBalanced, rawRowCheck9362]

theorem rawRowCheck9363 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form14 = rawRow9363 := by decide +kernel

theorem rowCheck9363 : row9363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9363 := by decide +kernel

theorem rowEval9363 (x : Key → ℝ) : Integer.Sparse.eval row9363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9363, Integer.Sparse.eval_collectBalanced, rawRowCheck9363]

theorem rawRowCheck9364 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form14 = rawRow9364 := by decide +kernel

theorem rowCheck9364 : row9364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9364 := by decide +kernel

theorem rowEval9364 (x : Key → ℝ) : Integer.Sparse.eval row9364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9364, Integer.Sparse.eval_collectBalanced, rawRowCheck9364]

theorem rawRowCheck9365 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form15 = rawRow9365 := by decide +kernel

theorem rowCheck9365 : row9365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9365 := by decide +kernel

theorem rowEval9365 (x : Key → ℝ) : Integer.Sparse.eval row9365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9365, Integer.Sparse.eval_collectBalanced, rawRowCheck9365]

theorem rawRowCheck9366 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form15 = rawRow9366 := by decide +kernel

theorem rowCheck9366 : row9366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9366 := by decide +kernel

theorem rowEval9366 (x : Key → ℝ) : Integer.Sparse.eval row9366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9366, Integer.Sparse.eval_collectBalanced, rawRowCheck9366]

theorem rawRowCheck9367 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form15 = rawRow9367 := by decide +kernel

theorem rowCheck9367 : row9367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9367 := by decide +kernel

theorem rowEval9367 (x : Key → ℝ) : Integer.Sparse.eval row9367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9367, Integer.Sparse.eval_collectBalanced, rawRowCheck9367]

theorem rawRowCheck9368 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form15 = rawRow9368 := by decide +kernel

theorem rowCheck9368 : row9368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9368 := by decide +kernel

theorem rowEval9368 (x : Key → ℝ) : Integer.Sparse.eval row9368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9368, Integer.Sparse.eval_collectBalanced, rawRowCheck9368]

theorem rawRowCheck9369 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form15 = rawRow9369 := by decide +kernel

theorem rowCheck9369 : row9369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9369 := by decide +kernel

theorem rowEval9369 (x : Key → ℝ) : Integer.Sparse.eval row9369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9369, Integer.Sparse.eval_collectBalanced, rawRowCheck9369]

theorem rawRowCheck9370 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form15 = rawRow9370 := by decide +kernel

theorem rowCheck9370 : row9370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9370 := by decide +kernel

theorem rowEval9370 (x : Key → ℝ) : Integer.Sparse.eval row9370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9370, Integer.Sparse.eval_collectBalanced, rawRowCheck9370]

theorem rawRowCheck9371 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form15 = rawRow9371 := by decide +kernel

theorem rowCheck9371 : row9371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9371 := by decide +kernel

theorem rowEval9371 (x : Key → ℝ) : Integer.Sparse.eval row9371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9371, Integer.Sparse.eval_collectBalanced, rawRowCheck9371]

theorem rawRowCheck9372 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form15 = rawRow9372 := by decide +kernel

theorem rowCheck9372 : row9372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9372 := by decide +kernel

theorem rowEval9372 (x : Key → ℝ) : Integer.Sparse.eval row9372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9372, Integer.Sparse.eval_collectBalanced, rawRowCheck9372]

theorem rawRowCheck9373 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form15 = rawRow9373 := by decide +kernel

theorem rowCheck9373 : row9373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9373 := by decide +kernel

theorem rowEval9373 (x : Key → ℝ) : Integer.Sparse.eval row9373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9373, Integer.Sparse.eval_collectBalanced, rawRowCheck9373]

theorem rawRowCheck9374 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form15 = rawRow9374 := by decide +kernel

theorem rowCheck9374 : row9374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9374 := by decide +kernel

theorem rowEval9374 (x : Key → ℝ) : Integer.Sparse.eval row9374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9374, Integer.Sparse.eval_collectBalanced, rawRowCheck9374]

theorem rawRowCheck9375 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form15 = rawRow9375 := by decide +kernel

theorem rowCheck9375 : row9375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9375 := by decide +kernel

theorem rowEval9375 (x : Key → ℝ) : Integer.Sparse.eval row9375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck9375, Integer.Sparse.eval_collectBalanced, rawRowCheck9375]

theorem rawRowCheck9376 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form15 = rawRow9376 := by decide +kernel

theorem rowCheck9376 : row9376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9376 := by decide +kernel

theorem rowEval9376 (x : Key → ℝ) : Integer.Sparse.eval row9376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9376, Integer.Sparse.eval_collectBalanced, rawRowCheck9376]

theorem rawRowCheck9377 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form15 = rawRow9377 := by decide +kernel

theorem rowCheck9377 : row9377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9377 := by decide +kernel

theorem rowEval9377 (x : Key → ℝ) : Integer.Sparse.eval row9377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck9377, Integer.Sparse.eval_collectBalanced, rawRowCheck9377]

theorem rawRowCheck9378 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form15 = rawRow9378 := by decide +kernel

theorem rowCheck9378 : row9378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9378 := by decide +kernel

theorem rowEval9378 (x : Key → ℝ) : Integer.Sparse.eval row9378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9378, Integer.Sparse.eval_collectBalanced, rawRowCheck9378]

theorem rawRowCheck9379 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form15 = rawRow9379 := by decide +kernel

theorem rowCheck9379 : row9379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9379 := by decide +kernel

theorem rowEval9379 (x : Key → ℝ) : Integer.Sparse.eval row9379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9379, Integer.Sparse.eval_collectBalanced, rawRowCheck9379]

theorem rawRowCheck9380 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form15 = rawRow9380 := by decide +kernel

theorem rowCheck9380 : row9380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9380 := by decide +kernel

theorem rowEval9380 (x : Key → ℝ) : Integer.Sparse.eval row9380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck9380, Integer.Sparse.eval_collectBalanced, rawRowCheck9380]

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

theorem entryCheck15_0 : entry15_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_0 k)) := by decide +kernel

theorem rowsSound15_0 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8661 x
  · exact rowEval8662 x
  · exact rowEval8663 x
  · exact rowEval8664 x
  · exact rowEval9173 x
  · exact rowEval9174 x
  · exact rowEval9175 x
  · exact rowEval9176 x
  · exact rowEval9177 x
  · exact rowEval9178 x
  · exact rowEval9179 x
  · exact rowEval9180 x
  · exact rowEval9181 x
  · exact rowEval9182 x
  · exact rowEval9183 x
  · exact rowEval9184 x

theorem entryEval15_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_0 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck15_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_0]

theorem entryCheck15_1 : entry15_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_1 k)) := by decide +kernel

theorem rowsSound15_1 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8669 x
  · exact rowEval8670 x
  · exact rowEval8671 x
  · exact rowEval8672 x
  · exact rowEval9185 x
  · exact rowEval9186 x
  · exact rowEval9187 x
  · exact rowEval9188 x
  · exact rowEval9189 x
  · exact rowEval9190 x
  · exact rowEval9191 x
  · exact rowEval9192 x
  · exact rowEval9193 x
  · exact rowEval9194 x
  · exact rowEval9195 x
  · exact rowEval9196 x

theorem entryEval15_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_1 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck15_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_1]

theorem entryCheck15_2 : entry15_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_2 k)) := by decide +kernel

theorem rowsSound15_2 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8677 x
  · exact rowEval8678 x
  · exact rowEval8679 x
  · exact rowEval8680 x
  · exact rowEval9197 x
  · exact rowEval9198 x
  · exact rowEval9199 x
  · exact rowEval9200 x
  · exact rowEval9201 x
  · exact rowEval9202 x
  · exact rowEval9203 x
  · exact rowEval9204 x
  · exact rowEval9205 x
  · exact rowEval9206 x
  · exact rowEval9207 x
  · exact rowEval9208 x

theorem entryEval15_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_2 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck15_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_2]

theorem entryCheck15_3 : entry15_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_3 k)) := by decide +kernel

theorem rowsSound15_3 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8685 x
  · exact rowEval8686 x
  · exact rowEval8687 x
  · exact rowEval8688 x
  · exact rowEval9209 x
  · exact rowEval9210 x
  · exact rowEval9211 x
  · exact rowEval9212 x
  · exact rowEval9213 x
  · exact rowEval9214 x
  · exact rowEval9215 x
  · exact rowEval9216 x
  · exact rowEval9217 x
  · exact rowEval9218 x
  · exact rowEval9219 x
  · exact rowEval9220 x

theorem entryEval15_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_3 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck15_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_3]

theorem entryCheck15_4 : entry15_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_4 k)) := by decide +kernel

theorem rowsSound15_4 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8693 x
  · exact rowEval8694 x
  · exact rowEval8695 x
  · exact rowEval8696 x
  · exact rowEval9221 x
  · exact rowEval9222 x
  · exact rowEval9223 x
  · exact rowEval9224 x
  · exact rowEval9225 x
  · exact rowEval9226 x
  · exact rowEval9227 x
  · exact rowEval9228 x
  · exact rowEval9229 x
  · exact rowEval9230 x
  · exact rowEval9231 x
  · exact rowEval9232 x

theorem entryEval15_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_4 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck15_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_4]

theorem entryCheck15_6 : entry15_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_6 k)) := by decide +kernel

theorem rowsSound15_6 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8709 x
  · exact rowEval8710 x
  · exact rowEval8711 x
  · exact rowEval8712 x
  · exact rowEval9245 x
  · exact rowEval9246 x
  · exact rowEval9247 x
  · exact rowEval9248 x
  · exact rowEval9249 x
  · exact rowEval9250 x
  · exact rowEval9251 x
  · exact rowEval9252 x
  · exact rowEval9253 x
  · exact rowEval9254 x
  · exact rowEval9255 x
  · exact rowEval9256 x

theorem entryEval15_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_6 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck15_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_6]

theorem entryCheck15_7 : entry15_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_7 k)) := by decide +kernel

theorem rowsSound15_7 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8717 x
  · exact rowEval8718 x
  · exact rowEval8719 x
  · exact rowEval8720 x
  · exact rowEval9257 x
  · exact rowEval9258 x
  · exact rowEval9259 x
  · exact rowEval9260 x
  · exact rowEval9261 x
  · exact rowEval9262 x
  · exact rowEval9263 x
  · exact rowEval9264 x
  · exact rowEval9265 x
  · exact rowEval9266 x
  · exact rowEval9267 x
  · exact rowEval9268 x

theorem entryEval15_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_7 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck15_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_7]

theorem entryCheck15_10 : entry15_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_10 k)) := by decide +kernel

theorem rowsSound15_10 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8741 x
  · exact rowEval8742 x
  · exact rowEval8743 x
  · exact rowEval8744 x
  · exact rowEval9293 x
  · exact rowEval9294 x
  · exact rowEval9295 x
  · exact rowEval9296 x
  · exact rowEval9297 x
  · exact rowEval9298 x
  · exact rowEval9299 x
  · exact rowEval9300 x
  · exact rowEval9301 x
  · exact rowEval9302 x
  · exact rowEval9303 x
  · exact rowEval9304 x

theorem entryEval15_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_10 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck15_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_10]

theorem entryCheck15_11 : entry15_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_11 k)) := by decide +kernel

theorem rowsSound15_11 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval8749 x
  · exact rowEval8750 x
  · exact rowEval8751 x
  · exact rowEval8752 x
  · exact rowEval9305 x
  · exact rowEval9306 x
  · exact rowEval9307 x
  · exact rowEval9308 x
  · exact rowEval9309 x
  · exact rowEval9310 x
  · exact rowEval9311 x
  · exact rowEval9312 x
  · exact rowEval9313 x
  · exact rowEval9314 x
  · exact rowEval9315 x
  · exact rowEval9316 x

theorem entryEval15_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_11 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck15_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_11]

theorem entryCheck15_12 : entry15_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_12 k)) := by decide +kernel

theorem rowsSound15_12 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9317 x
  · exact rowEval9318 x
  · exact rowEval9319 x
  · exact rowEval9320 x
  · exact rowEval9321 x
  · exact rowEval9322 x
  · exact rowEval9323 x
  · exact rowEval9324 x
  · exact rowEval9325 x
  · exact rowEval9326 x
  · exact rowEval9327 x
  · exact rowEval9328 x
  · exact rowEval9329 x
  · exact rowEval9330 x
  · exact rowEval9331 x
  · exact rowEval9332 x

theorem entryEval15_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_12 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck15_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_12]

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

theorem entryCheck15_14 : entry15_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_14 k)) := by decide +kernel

theorem rowsSound15_14 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9349 x
  · exact rowEval9350 x
  · exact rowEval9351 x
  · exact rowEval9352 x
  · exact rowEval9353 x
  · exact rowEval9354 x
  · exact rowEval9355 x
  · exact rowEval9356 x
  · exact rowEval9357 x
  · exact rowEval9358 x
  · exact rowEval9359 x
  · exact rowEval9360 x
  · exact rowEval9361 x
  · exact rowEval9362 x
  · exact rowEval9363 x
  · exact rowEval9364 x

theorem entryEval15_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_14 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck15_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_14]

theorem entryCheck15_15 : entry15_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_15 k)) := by decide +kernel

theorem rowsSound15_15 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval9365 x
  · exact rowEval9366 x
  · exact rowEval9367 x
  · exact rowEval9368 x
  · exact rowEval9369 x
  · exact rowEval9370 x
  · exact rowEval9371 x
  · exact rowEval9372 x
  · exact rowEval9373 x
  · exact rowEval9374 x
  · exact rowEval9375 x
  · exact rowEval9376 x
  · exact rowEval9377 x
  · exact rowEval9378 x
  · exact rowEval9379 x
  · exact rowEval9380 x

theorem entryEval15_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_15 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck15_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_15]

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

theorem rawRowCheck9485 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form15 = rawRow9485 := by decide +kernel

theorem rowCheck9485 : row9485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9485 := by decide +kernel

theorem rowEval9485 (x : Key → ℝ) : Integer.Sparse.eval row9485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9485, Integer.Sparse.eval_collectBalanced, rawRowCheck9485]

theorem rawRowCheck9486 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form15 = rawRow9486 := by decide +kernel

theorem rowCheck9486 : row9486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9486 := by decide +kernel

theorem rowEval9486 (x : Key → ℝ) : Integer.Sparse.eval row9486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9486, Integer.Sparse.eval_collectBalanced, rawRowCheck9486]

theorem rawRowCheck9487 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form15 = rawRow9487 := by decide +kernel

theorem rowCheck9487 : row9487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9487 := by decide +kernel

theorem rowEval9487 (x : Key → ℝ) : Integer.Sparse.eval row9487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9487, Integer.Sparse.eval_collectBalanced, rawRowCheck9487]

theorem rawRowCheck9488 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form15 = rawRow9488 := by decide +kernel

theorem rowCheck9488 : row9488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9488 := by decide +kernel

theorem rowEval9488 (x : Key → ℝ) : Integer.Sparse.eval row9488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9488, Integer.Sparse.eval_collectBalanced, rawRowCheck9488]

theorem rawRowCheck9489 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow9489 := by decide +kernel

theorem rowCheck9489 : row9489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9489 := by decide +kernel

theorem rowEval9489 (x : Key → ℝ) : Integer.Sparse.eval row9489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9489, Integer.Sparse.eval_collectBalanced, rawRowCheck9489]

theorem rawRowCheck9490 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form15 = rawRow9490 := by decide +kernel

theorem rowCheck9490 : row9490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9490 := by decide +kernel

theorem rowEval9490 (x : Key → ℝ) : Integer.Sparse.eval row9490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9490, Integer.Sparse.eval_collectBalanced, rawRowCheck9490]

theorem rawRowCheck9491 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form15 = rawRow9491 := by decide +kernel

theorem rowCheck9491 : row9491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9491 := by decide +kernel

theorem rowEval9491 (x : Key → ℝ) : Integer.Sparse.eval row9491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9491, Integer.Sparse.eval_collectBalanced, rawRowCheck9491]

theorem rawRowCheck9492 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form15 = rawRow9492 := by decide +kernel

theorem rowCheck9492 : row9492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9492 := by decide +kernel

theorem rowEval9492 (x : Key → ℝ) : Integer.Sparse.eval row9492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9492, Integer.Sparse.eval_collectBalanced, rawRowCheck9492]

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

theorem entryCheck16_15 : entry16_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_15 k)) := by decide +kernel

theorem rowsSound16_15 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval9485 x
  · exact rowEval9486 x
  · exact rowEval9487 x
  · exact rowEval9488 x
  · exact rowEval9489 x
  · exact rowEval9490 x
  · exact rowEval9491 x
  · exact rowEval9492 x

theorem entryEval16_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_15 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck16_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_15]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10293 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15 = rawRow10293 := by decide +kernel

theorem rowCheck10293 : row10293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10293 := by decide +kernel

theorem rowEval10293 (x : Key → ℝ) : Integer.Sparse.eval row10293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10293, Integer.Sparse.eval_collectBalanced, rawRowCheck10293]

theorem rawRowCheck10294 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15 = rawRow10294 := by decide +kernel

theorem rowCheck10294 : row10294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10294 := by decide +kernel

theorem rowEval10294 (x : Key → ℝ) : Integer.Sparse.eval row10294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10294, Integer.Sparse.eval_collectBalanced, rawRowCheck10294]

theorem rawRowCheck10295 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15 = rawRow10295 := by decide +kernel

theorem rowCheck10295 : row10295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10295 := by decide +kernel

theorem rowEval10295 (x : Key → ℝ) : Integer.Sparse.eval row10295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10295, Integer.Sparse.eval_collectBalanced, rawRowCheck10295]

theorem rawRowCheck10296 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15 = rawRow10296 := by decide +kernel

theorem rowCheck10296 : row10296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10296 := by decide +kernel

theorem rowEval10296 (x : Key → ℝ) : Integer.Sparse.eval row10296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10296, Integer.Sparse.eval_collectBalanced, rawRowCheck10296]

theorem rawRowCheck10297 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15 = rawRow10297 := by decide +kernel

theorem rowCheck10297 : row10297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10297 := by decide +kernel

theorem rowEval10297 (x : Key → ℝ) : Integer.Sparse.eval row10297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10297, Integer.Sparse.eval_collectBalanced, rawRowCheck10297]

theorem rawRowCheck10298 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15 = rawRow10298 := by decide +kernel

theorem rowCheck10298 : row10298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10298 := by decide +kernel

theorem rowEval10298 (x : Key → ℝ) : Integer.Sparse.eval row10298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10298, Integer.Sparse.eval_collectBalanced, rawRowCheck10298]

theorem rawRowCheck10299 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15 = rawRow10299 := by decide +kernel

theorem rowCheck10299 : row10299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10299 := by decide +kernel

theorem rowEval10299 (x : Key → ℝ) : Integer.Sparse.eval row10299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10299, Integer.Sparse.eval_collectBalanced, rawRowCheck10299]

theorem rawRowCheck10300 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15 = rawRow10300 := by decide +kernel

theorem rowCheck10300 : row10300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10300 := by decide +kernel

theorem rowEval10300 (x : Key → ℝ) : Integer.Sparse.eval row10300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10300, Integer.Sparse.eval_collectBalanced, rawRowCheck10300]

theorem rawRowCheck10301 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15 = rawRow10301 := by decide +kernel

theorem rowCheck10301 : row10301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10301 := by decide +kernel

theorem rowEval10301 (x : Key → ℝ) : Integer.Sparse.eval row10301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10301, Integer.Sparse.eval_collectBalanced, rawRowCheck10301]

theorem rawRowCheck10302 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15 = rawRow10302 := by decide +kernel

theorem rowCheck10302 : row10302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10302 := by decide +kernel

theorem rowEval10302 (x : Key → ℝ) : Integer.Sparse.eval row10302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10302, Integer.Sparse.eval_collectBalanced, rawRowCheck10302]

theorem rawRowCheck10303 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15 = rawRow10303 := by decide +kernel

theorem rowCheck10303 : row10303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10303 := by decide +kernel

theorem rowEval10303 (x : Key → ℝ) : Integer.Sparse.eval row10303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10303, Integer.Sparse.eval_collectBalanced, rawRowCheck10303]

theorem rawRowCheck10304 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15 = rawRow10304 := by decide +kernel

theorem rowCheck10304 : row10304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10304 := by decide +kernel

theorem rowEval10304 (x : Key → ℝ) : Integer.Sparse.eval row10304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10304, Integer.Sparse.eval_collectBalanced, rawRowCheck10304]

theorem rawRowCheck10305 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form15 = rawRow10305 := by decide +kernel

theorem rowCheck10305 : row10305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10305 := by decide +kernel

theorem rowEval10305 (x : Key → ℝ) : Integer.Sparse.eval row10305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10305, Integer.Sparse.eval_collectBalanced, rawRowCheck10305]

theorem rawRowCheck10306 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form15 = rawRow10306 := by decide +kernel

theorem rowCheck10306 : row10306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10306 := by decide +kernel

theorem rowEval10306 (x : Key → ℝ) : Integer.Sparse.eval row10306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10306, Integer.Sparse.eval_collectBalanced, rawRowCheck10306]

theorem rawRowCheck10307 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form15 = rawRow10307 := by decide +kernel

theorem rowCheck10307 : row10307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10307 := by decide +kernel

theorem rowEval10307 (x : Key → ℝ) : Integer.Sparse.eval row10307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10307, Integer.Sparse.eval_collectBalanced, rawRowCheck10307]

theorem rawRowCheck10308 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form15 = rawRow10308 := by decide +kernel

theorem rowCheck10308 : row10308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10308 := by decide +kernel

theorem rowEval10308 (x : Key → ℝ) : Integer.Sparse.eval row10308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10308, Integer.Sparse.eval_collectBalanced, rawRowCheck10308]

theorem rawRowCheck10309 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form15 = rawRow10309 := by decide +kernel

theorem rowCheck10309 : row10309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10309 := by decide +kernel

theorem rowEval10309 (x : Key → ℝ) : Integer.Sparse.eval row10309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10309, Integer.Sparse.eval_collectBalanced, rawRowCheck10309]

theorem rawRowCheck10310 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form15 = rawRow10310 := by decide +kernel

theorem rowCheck10310 : row10310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10310 := by decide +kernel

theorem rowEval10310 (x : Key → ℝ) : Integer.Sparse.eval row10310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10310, Integer.Sparse.eval_collectBalanced, rawRowCheck10310]

theorem rawRowCheck10311 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form15 = rawRow10311 := by decide +kernel

theorem rowCheck10311 : row10311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10311 := by decide +kernel

theorem rowEval10311 (x : Key → ℝ) : Integer.Sparse.eval row10311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10311, Integer.Sparse.eval_collectBalanced, rawRowCheck10311]

theorem rawRowCheck10312 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form15 = rawRow10312 := by decide +kernel

theorem rowCheck10312 : row10312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10312 := by decide +kernel

theorem rowEval10312 (x : Key → ℝ) : Integer.Sparse.eval row10312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10312, Integer.Sparse.eval_collectBalanced, rawRowCheck10312]

theorem rawRowCheck10313 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form15 = rawRow10313 := by decide +kernel

theorem rowCheck10313 : row10313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10313 := by decide +kernel

theorem rowEval10313 (x : Key → ℝ) : Integer.Sparse.eval row10313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10313, Integer.Sparse.eval_collectBalanced, rawRowCheck10313]

theorem rawRowCheck10314 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form15 = rawRow10314 := by decide +kernel

theorem rowCheck10314 : row10314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10314 := by decide +kernel

theorem rowEval10314 (x : Key → ℝ) : Integer.Sparse.eval row10314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10314, Integer.Sparse.eval_collectBalanced, rawRowCheck10314]

theorem rawRowCheck10315 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form15 = rawRow10315 := by decide +kernel

theorem rowCheck10315 : row10315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10315 := by decide +kernel

theorem rowEval10315 (x : Key → ℝ) : Integer.Sparse.eval row10315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10315, Integer.Sparse.eval_collectBalanced, rawRowCheck10315]

theorem rawRowCheck10316 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form15 = rawRow10316 := by decide +kernel

theorem rowCheck10316 : row10316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10316 := by decide +kernel

theorem rowEval10316 (x : Key → ℝ) : Integer.Sparse.eval row10316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10316, Integer.Sparse.eval_collectBalanced, rawRowCheck10316]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck18_15 : entry18_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_15 k)) := by decide +kernel

theorem rowsSound18_15 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10293 x
  · exact rowEval10294 x
  · exact rowEval10295 x
  · exact rowEval10296 x
  · exact rowEval10297 x
  · exact rowEval10298 x
  · exact rowEval10299 x
  · exact rowEval10300 x
  · exact rowEval10301 x
  · exact rowEval10302 x
  · exact rowEval10303 x
  · exact rowEval10304 x
  · exact rowEval10305 x
  · exact rowEval10306 x
  · exact rowEval10307 x
  · exact rowEval10308 x
  · exact rowEval10309 x
  · exact rowEval10310 x
  · exact rowEval10311 x
  · exact rowEval10312 x
  · exact rowEval10313 x
  · exact rowEval10314 x
  · exact rowEval10315 x
  · exact rowEval10316 x

theorem entryEval18_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_15 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck18_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_15]

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

theorem rawRowCheck10539 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form15 = rawRow10539 := by decide +kernel

theorem rowCheck10539 : row10539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10539 := by decide +kernel

theorem rowEval10539 (x : Key → ℝ) : Integer.Sparse.eval row10539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10539, Integer.Sparse.eval_collectBalanced, rawRowCheck10539]

theorem rawRowCheck10540 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form15 = rawRow10540 := by decide +kernel

theorem rowCheck10540 : row10540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10540 := by decide +kernel

theorem rowEval10540 (x : Key → ℝ) : Integer.Sparse.eval row10540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10540, Integer.Sparse.eval_collectBalanced, rawRowCheck10540]

theorem rawRowCheck10541 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form15 = rawRow10541 := by decide +kernel

theorem rowCheck10541 : row10541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10541 := by decide +kernel

theorem rowEval10541 (x : Key → ℝ) : Integer.Sparse.eval row10541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10541, Integer.Sparse.eval_collectBalanced, rawRowCheck10541]

theorem rawRowCheck10542 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form15 = rawRow10542 := by decide +kernel

theorem rowCheck10542 : row10542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10542 := by decide +kernel

theorem rowEval10542 (x : Key → ℝ) : Integer.Sparse.eval row10542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10542, Integer.Sparse.eval_collectBalanced, rawRowCheck10542]

theorem rawRowCheck10543 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form15 = rawRow10543 := by decide +kernel

theorem rowCheck10543 : row10543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10543 := by decide +kernel

theorem rowEval10543 (x : Key → ℝ) : Integer.Sparse.eval row10543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10543, Integer.Sparse.eval_collectBalanced, rawRowCheck10543]

theorem rawRowCheck10544 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form15 = rawRow10544 := by decide +kernel

theorem rowCheck10544 : row10544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10544 := by decide +kernel

theorem rowEval10544 (x : Key → ℝ) : Integer.Sparse.eval row10544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10544, Integer.Sparse.eval_collectBalanced, rawRowCheck10544]

theorem rawRowCheck10545 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form15 = rawRow10545 := by decide +kernel

theorem rowCheck10545 : row10545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10545 := by decide +kernel

theorem rowEval10545 (x : Key → ℝ) : Integer.Sparse.eval row10545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10545, Integer.Sparse.eval_collectBalanced, rawRowCheck10545]

theorem rawRowCheck10546 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form15 = rawRow10546 := by decide +kernel

theorem rowCheck10546 : row10546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10546 := by decide +kernel

theorem rowEval10546 (x : Key → ℝ) : Integer.Sparse.eval row10546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10546, Integer.Sparse.eval_collectBalanced, rawRowCheck10546]

theorem rawRowCheck10547 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form15 = rawRow10547 := by decide +kernel

theorem rowCheck10547 : row10547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10547 := by decide +kernel

theorem rowEval10547 (x : Key → ℝ) : Integer.Sparse.eval row10547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10547, Integer.Sparse.eval_collectBalanced, rawRowCheck10547]

theorem rawRowCheck10548 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form15 = rawRow10548 := by decide +kernel

theorem rowCheck10548 : row10548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10548 := by decide +kernel

theorem rowEval10548 (x : Key → ℝ) : Integer.Sparse.eval row10548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10548, Integer.Sparse.eval_collectBalanced, rawRowCheck10548]

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

theorem entryCheck19_15 : entry19_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_15 k)) := by decide +kernel

theorem rowsSound19_15 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10539 x
  · exact rowEval10540 x
  · exact rowEval10541 x
  · exact rowEval10542 x
  · exact rowEval10543 x
  · exact rowEval10544 x
  · exact rowEval10545 x
  · exact rowEval10546 x
  · exact rowEval10547 x
  · exact rowEval10548 x

theorem entryEval19_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_15 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck19_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_15]

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

theorem rawRowCheck10664 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form15 = rawRow10664 := by decide +kernel

theorem rowCheck10664 : row10664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10664 := by decide +kernel

theorem rowEval10664 (x : Key → ℝ) : Integer.Sparse.eval row10664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form15) x := by
  rw [rowCheck10664, Integer.Sparse.eval_collectBalanced, rawRowCheck10664]

theorem rawRowCheck10665 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form15 = rawRow10665 := by decide +kernel

theorem rowCheck10665 : row10665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10665 := by decide +kernel

theorem rowEval10665 (x : Key → ℝ) : Integer.Sparse.eval row10665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10665, Integer.Sparse.eval_collectBalanced, rawRowCheck10665]

theorem rawRowCheck10666 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form15 = rawRow10666 := by decide +kernel

theorem rowCheck10666 : row10666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10666 := by decide +kernel

theorem rowEval10666 (x : Key → ℝ) : Integer.Sparse.eval row10666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10666, Integer.Sparse.eval_collectBalanced, rawRowCheck10666]

theorem rawRowCheck10667 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow10667 := by decide +kernel

theorem rowCheck10667 : row10667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10667 := by decide +kernel

theorem rowEval10667 (x : Key → ℝ) : Integer.Sparse.eval row10667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10667, Integer.Sparse.eval_collectBalanced, rawRowCheck10667]

theorem rawRowCheck10668 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form15 = rawRow10668 := by decide +kernel

theorem rowCheck10668 : row10668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10668 := by decide +kernel

theorem rowEval10668 (x : Key → ℝ) : Integer.Sparse.eval row10668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10668, Integer.Sparse.eval_collectBalanced, rawRowCheck10668]

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

theorem entryCheck20_15 : entry20_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_15 k)) := by decide +kernel

theorem rowsSound20_15 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10664 x
  · exact rowEval10665 x
  · exact rowEval10666 x
  · exact rowEval10667 x
  · exact rowEval10668 x

theorem entryEval20_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_15 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck20_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_15]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12044 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form15 = rawRow12044 := by decide +kernel

theorem rowCheck12044 : row12044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12044 := by decide +kernel

theorem rowEval12044 (x : Key → ℝ) : Integer.Sparse.eval row12044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12044, Integer.Sparse.eval_collectBalanced, rawRowCheck12044]

theorem rawRowCheck12045 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form15 = rawRow12045 := by decide +kernel

theorem rowCheck12045 : row12045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12045 := by decide +kernel

theorem rowEval12045 (x : Key → ℝ) : Integer.Sparse.eval row12045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12045, Integer.Sparse.eval_collectBalanced, rawRowCheck12045]

theorem rawRowCheck12046 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form15 = rawRow12046 := by decide +kernel

theorem rowCheck12046 : row12046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12046 := by decide +kernel

theorem rowEval12046 (x : Key → ℝ) : Integer.Sparse.eval row12046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12046, Integer.Sparse.eval_collectBalanced, rawRowCheck12046]

theorem rawRowCheck12047 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form15 = rawRow12047 := by decide +kernel

theorem rowCheck12047 : row12047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12047 := by decide +kernel

theorem rowEval12047 (x : Key → ℝ) : Integer.Sparse.eval row12047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12047, Integer.Sparse.eval_collectBalanced, rawRowCheck12047]

theorem rawRowCheck12048 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form15 = rawRow12048 := by decide +kernel

theorem rowCheck12048 : row12048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12048 := by decide +kernel

theorem rowEval12048 (x : Key → ℝ) : Integer.Sparse.eval row12048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12048, Integer.Sparse.eval_collectBalanced, rawRowCheck12048]

theorem rawRowCheck12049 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form15 = rawRow12049 := by decide +kernel

theorem rowCheck12049 : row12049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12049 := by decide +kernel

theorem rowEval12049 (x : Key → ℝ) : Integer.Sparse.eval row12049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12049, Integer.Sparse.eval_collectBalanced, rawRowCheck12049]

theorem rawRowCheck12050 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15 = rawRow12050 := by decide +kernel

theorem rowCheck12050 : row12050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12050 := by decide +kernel

theorem rowEval12050 (x : Key → ℝ) : Integer.Sparse.eval row12050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12050, Integer.Sparse.eval_collectBalanced, rawRowCheck12050]

theorem rawRowCheck12051 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15 = rawRow12051 := by decide +kernel

theorem rowCheck12051 : row12051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12051 := by decide +kernel

theorem rowEval12051 (x : Key → ℝ) : Integer.Sparse.eval row12051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12051, Integer.Sparse.eval_collectBalanced, rawRowCheck12051]

theorem rawRowCheck12052 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15 = rawRow12052 := by decide +kernel

theorem rowCheck12052 : row12052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12052 := by decide +kernel

theorem rowEval12052 (x : Key → ℝ) : Integer.Sparse.eval row12052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12052, Integer.Sparse.eval_collectBalanced, rawRowCheck12052]

theorem rawRowCheck12053 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15 = rawRow12053 := by decide +kernel

theorem rowCheck12053 : row12053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12053 := by decide +kernel

theorem rowEval12053 (x : Key → ℝ) : Integer.Sparse.eval row12053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12053, Integer.Sparse.eval_collectBalanced, rawRowCheck12053]

theorem rawRowCheck12054 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15 = rawRow12054 := by decide +kernel

theorem rowCheck12054 : row12054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12054 := by decide +kernel

theorem rowEval12054 (x : Key → ℝ) : Integer.Sparse.eval row12054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12054, Integer.Sparse.eval_collectBalanced, rawRowCheck12054]

theorem rawRowCheck12055 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15 = rawRow12055 := by decide +kernel

theorem rowCheck12055 : row12055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12055 := by decide +kernel

theorem rowEval12055 (x : Key → ℝ) : Integer.Sparse.eval row12055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck12055, Integer.Sparse.eval_collectBalanced, rawRowCheck12055]

theorem rawRowCheck12056 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15 = rawRow12056 := by decide +kernel

theorem rowCheck12056 : row12056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12056 := by decide +kernel

theorem rowEval12056 (x : Key → ℝ) : Integer.Sparse.eval row12056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12056, Integer.Sparse.eval_collectBalanced, rawRowCheck12056]

theorem rawRowCheck12057 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15 = rawRow12057 := by decide +kernel

theorem rowCheck12057 : row12057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12057 := by decide +kernel

theorem rowEval12057 (x : Key → ℝ) : Integer.Sparse.eval row12057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12057, Integer.Sparse.eval_collectBalanced, rawRowCheck12057]

theorem rawRowCheck12058 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15 = rawRow12058 := by decide +kernel

theorem rowCheck12058 : row12058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12058 := by decide +kernel

theorem rowEval12058 (x : Key → ℝ) : Integer.Sparse.eval row12058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12058, Integer.Sparse.eval_collectBalanced, rawRowCheck12058]

theorem rawRowCheck12059 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15 = rawRow12059 := by decide +kernel

theorem rowCheck12059 : row12059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12059 := by decide +kernel

theorem rowEval12059 (x : Key → ℝ) : Integer.Sparse.eval row12059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck12059, Integer.Sparse.eval_collectBalanced, rawRowCheck12059]

theorem rawRowCheck12060 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15 = rawRow12060 := by decide +kernel

theorem rowCheck12060 : row12060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12060 := by decide +kernel

theorem rowEval12060 (x : Key → ℝ) : Integer.Sparse.eval row12060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12060, Integer.Sparse.eval_collectBalanced, rawRowCheck12060]

theorem rawRowCheck12061 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15 = rawRow12061 := by decide +kernel

theorem rowCheck12061 : row12061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12061 := by decide +kernel

theorem rowEval12061 (x : Key → ℝ) : Integer.Sparse.eval row12061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck12061, Integer.Sparse.eval_collectBalanced, rawRowCheck12061]

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

theorem rawRowCheck12281 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form15 = rawRow12281 := by decide +kernel

theorem rowCheck12281 : row12281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12281 := by decide +kernel

theorem rowEval12281 (x : Key → ℝ) : Integer.Sparse.eval row12281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12281, Integer.Sparse.eval_collectBalanced, rawRowCheck12281]

theorem rawRowCheck12282 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow12282 := by decide +kernel

theorem rowCheck12282 : row12282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12282 := by decide +kernel

theorem rowEval12282 (x : Key → ℝ) : Integer.Sparse.eval row12282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12282, Integer.Sparse.eval_collectBalanced, rawRowCheck12282]

theorem rawRowCheck12283 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form15 = rawRow12283 := by decide +kernel

theorem rowCheck12283 : row12283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12283 := by decide +kernel

theorem rowEval12283 (x : Key → ℝ) : Integer.Sparse.eval row12283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12283, Integer.Sparse.eval_collectBalanced, rawRowCheck12283]

theorem rawRowCheck12284 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form15 = rawRow12284 := by decide +kernel

theorem rowCheck12284 : row12284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12284 := by decide +kernel

theorem rowEval12284 (x : Key → ℝ) : Integer.Sparse.eval row12284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12284, Integer.Sparse.eval_collectBalanced, rawRowCheck12284]

theorem rawRowCheck12285 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form15 = rawRow12285 := by decide +kernel

theorem rowCheck12285 : row12285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12285 := by decide +kernel

theorem rowEval12285 (x : Key → ℝ) : Integer.Sparse.eval row12285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12285, Integer.Sparse.eval_collectBalanced, rawRowCheck12285]

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

theorem entryCheck23_15 : entry23_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_15 k)) := by decide +kernel

theorem rowsSound23_15 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12044 x
  · exact rowEval12045 x
  · exact rowEval12046 x
  · exact rowEval12047 x
  · exact rowEval12048 x
  · exact rowEval12049 x
  · exact rowEval12050 x
  · exact rowEval12051 x
  · exact rowEval12052 x
  · exact rowEval12053 x
  · exact rowEval12054 x
  · exact rowEval12055 x
  · exact rowEval12056 x
  · exact rowEval12057 x
  · exact rowEval12058 x
  · exact rowEval12059 x
  · exact rowEval12060 x
  · exact rowEval12061 x

theorem entryEval23_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_15 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck23_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_15]

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

theorem entryCheck24_15 : entry24_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_15 k)) := by decide +kernel

theorem rowsSound24_15 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12281 x
  · exact rowEval12282 x
  · exact rowEval12283 x
  · exact rowEval12284 x
  · exact rowEval12285 x

theorem entryEval24_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_15 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck24_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_15]

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

theorem rawRowCheck12451 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form15 = rawRow12451 := by decide +kernel

theorem rowCheck12451 : row12451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12451 := by decide +kernel

theorem rowEval12451 (x : Key → ℝ) : Integer.Sparse.eval row12451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12451, Integer.Sparse.eval_collectBalanced, rawRowCheck12451]

theorem rawRowCheck12452 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form15 = rawRow12452 := by decide +kernel

theorem rowCheck12452 : row12452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12452 := by decide +kernel

theorem rowEval12452 (x : Key → ℝ) : Integer.Sparse.eval row12452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12452, Integer.Sparse.eval_collectBalanced, rawRowCheck12452]

theorem rawRowCheck12453 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form15 = rawRow12453 := by decide +kernel

theorem rowCheck12453 : row12453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12453 := by decide +kernel

theorem rowEval12453 (x : Key → ℝ) : Integer.Sparse.eval row12453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12453, Integer.Sparse.eval_collectBalanced, rawRowCheck12453]

theorem rawRowCheck12454 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form15 = rawRow12454 := by decide +kernel

theorem rowCheck12454 : row12454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12454 := by decide +kernel

theorem rowEval12454 (x : Key → ℝ) : Integer.Sparse.eval row12454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12454, Integer.Sparse.eval_collectBalanced, rawRowCheck12454]

theorem rawRowCheck12455 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form15 = rawRow12455 := by decide +kernel

theorem rowCheck12455 : row12455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12455 := by decide +kernel

theorem rowEval12455 (x : Key → ℝ) : Integer.Sparse.eval row12455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12455, Integer.Sparse.eval_collectBalanced, rawRowCheck12455]

theorem rawRowCheck12456 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form15 = rawRow12456 := by decide +kernel

theorem rowCheck12456 : row12456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12456 := by decide +kernel

theorem rowEval12456 (x : Key → ℝ) : Integer.Sparse.eval row12456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12456, Integer.Sparse.eval_collectBalanced, rawRowCheck12456]

theorem rawRowCheck12457 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form15 = rawRow12457 := by decide +kernel

theorem rowCheck12457 : row12457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12457 := by decide +kernel

theorem rowEval12457 (x : Key → ℝ) : Integer.Sparse.eval row12457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12457, Integer.Sparse.eval_collectBalanced, rawRowCheck12457]

theorem rawRowCheck12458 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form15 = rawRow12458 := by decide +kernel

theorem rowCheck12458 : row12458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12458 := by decide +kernel

theorem rowEval12458 (x : Key → ℝ) : Integer.Sparse.eval row12458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12458, Integer.Sparse.eval_collectBalanced, rawRowCheck12458]

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

theorem entryCheck25_15 : entry25_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_15 k)) := by decide +kernel

theorem rowsSound25_15 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12451 x
  · exact rowEval12452 x
  · exact rowEval12453 x
  · exact rowEval12454 x
  · exact rowEval12455 x
  · exact rowEval12456 x
  · exact rowEval12457 x
  · exact rowEval12458 x

theorem entryEval25_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_15 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck25_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_15]

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

theorem rawRowCheck12899 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form15 = rawRow12899 := by decide +kernel

theorem rowCheck12899 : row12899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12899 := by decide +kernel

theorem rowEval12899 (x : Key → ℝ) : Integer.Sparse.eval row12899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12899, Integer.Sparse.eval_collectBalanced, rawRowCheck12899]

theorem rawRowCheck12900 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form15 = rawRow12900 := by decide +kernel

theorem rowCheck12900 : row12900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12900 := by decide +kernel

theorem rowEval12900 (x : Key → ℝ) : Integer.Sparse.eval row12900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12900, Integer.Sparse.eval_collectBalanced, rawRowCheck12900]

theorem rawRowCheck12901 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form15 = rawRow12901 := by decide +kernel

theorem rowCheck12901 : row12901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12901 := by decide +kernel

theorem rowEval12901 (x : Key → ℝ) : Integer.Sparse.eval row12901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12901, Integer.Sparse.eval_collectBalanced, rawRowCheck12901]

theorem rawRowCheck12902 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form15 = rawRow12902 := by decide +kernel

theorem rowCheck12902 : row12902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12902 := by decide +kernel

theorem rowEval12902 (x : Key → ℝ) : Integer.Sparse.eval row12902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12902, Integer.Sparse.eval_collectBalanced, rawRowCheck12902]

theorem rawRowCheck12903 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form15 = rawRow12903 := by decide +kernel

theorem rowCheck12903 : row12903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12903 := by decide +kernel

theorem rowEval12903 (x : Key → ℝ) : Integer.Sparse.eval row12903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12903, Integer.Sparse.eval_collectBalanced, rawRowCheck12903]

theorem rawRowCheck12904 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form15 = rawRow12904 := by decide +kernel

theorem rowCheck12904 : row12904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12904 := by decide +kernel

theorem rowEval12904 (x : Key → ℝ) : Integer.Sparse.eval row12904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12904, Integer.Sparse.eval_collectBalanced, rawRowCheck12904]

theorem rawRowCheck12905 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form15 = rawRow12905 := by decide +kernel

theorem rowCheck12905 : row12905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12905 := by decide +kernel

theorem rowEval12905 (x : Key → ℝ) : Integer.Sparse.eval row12905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12905, Integer.Sparse.eval_collectBalanced, rawRowCheck12905]

theorem rawRowCheck12906 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form15 = rawRow12906 := by decide +kernel

theorem rowCheck12906 : row12906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12906 := by decide +kernel

theorem rowEval12906 (x : Key → ℝ) : Integer.Sparse.eval row12906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12906, Integer.Sparse.eval_collectBalanced, rawRowCheck12906]

theorem rawRowCheck12907 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form15 = rawRow12907 := by decide +kernel

theorem rowCheck12907 : row12907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12907 := by decide +kernel

theorem rowEval12907 (x : Key → ℝ) : Integer.Sparse.eval row12907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12907, Integer.Sparse.eval_collectBalanced, rawRowCheck12907]

theorem rawRowCheck12908 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form15 = rawRow12908 := by decide +kernel

theorem rowCheck12908 : row12908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12908 := by decide +kernel

theorem rowEval12908 (x : Key → ℝ) : Integer.Sparse.eval row12908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12908, Integer.Sparse.eval_collectBalanced, rawRowCheck12908]

theorem rawRowCheck12909 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form15 = rawRow12909 := by decide +kernel

theorem rowCheck12909 : row12909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12909 := by decide +kernel

theorem rowEval12909 (x : Key → ℝ) : Integer.Sparse.eval row12909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12909, Integer.Sparse.eval_collectBalanced, rawRowCheck12909]

theorem rawRowCheck12910 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form15 = rawRow12910 := by decide +kernel

theorem rowCheck12910 : row12910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12910 := by decide +kernel

theorem rowEval12910 (x : Key → ℝ) : Integer.Sparse.eval row12910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12910, Integer.Sparse.eval_collectBalanced, rawRowCheck12910]

theorem rawRowCheck12911 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form15 = rawRow12911 := by decide +kernel

theorem rowCheck12911 : row12911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12911 := by decide +kernel

theorem rowEval12911 (x : Key → ℝ) : Integer.Sparse.eval row12911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12911, Integer.Sparse.eval_collectBalanced, rawRowCheck12911]

theorem rawRowCheck12912 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form15 = rawRow12912 := by decide +kernel

theorem rowCheck12912 : row12912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12912 := by decide +kernel

theorem rowEval12912 (x : Key → ℝ) : Integer.Sparse.eval row12912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12912, Integer.Sparse.eval_collectBalanced, rawRowCheck12912]

theorem rawRowCheck12913 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form15 = rawRow12913 := by decide +kernel

theorem rowCheck12913 : row12913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12913 := by decide +kernel

theorem rowEval12913 (x : Key → ℝ) : Integer.Sparse.eval row12913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12913, Integer.Sparse.eval_collectBalanced, rawRowCheck12913]

theorem rawRowCheck12914 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form15 = rawRow12914 := by decide +kernel

theorem rowCheck12914 : row12914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12914 := by decide +kernel

theorem rowEval12914 (x : Key → ℝ) : Integer.Sparse.eval row12914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12914, Integer.Sparse.eval_collectBalanced, rawRowCheck12914]

theorem rawRowCheck12915 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form15 = rawRow12915 := by decide +kernel

theorem rowCheck12915 : row12915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12915 := by decide +kernel

theorem rowEval12915 (x : Key → ℝ) : Integer.Sparse.eval row12915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12915, Integer.Sparse.eval_collectBalanced, rawRowCheck12915]

theorem rawRowCheck12916 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form15 = rawRow12916 := by decide +kernel

theorem rowCheck12916 : row12916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12916 := by decide +kernel

theorem rowEval12916 (x : Key → ℝ) : Integer.Sparse.eval row12916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12916, Integer.Sparse.eval_collectBalanced, rawRowCheck12916]

theorem rawRowCheck12917 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form15 = rawRow12917 := by decide +kernel

theorem rowCheck12917 : row12917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12917 := by decide +kernel

theorem rowEval12917 (x : Key → ℝ) : Integer.Sparse.eval row12917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12917, Integer.Sparse.eval_collectBalanced, rawRowCheck12917]

theorem rawRowCheck12918 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form15 = rawRow12918 := by decide +kernel

theorem rowCheck12918 : row12918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12918 := by decide +kernel

theorem rowEval12918 (x : Key → ℝ) : Integer.Sparse.eval row12918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12918, Integer.Sparse.eval_collectBalanced, rawRowCheck12918]

theorem rawRowCheck12919 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form15 = rawRow12919 := by decide +kernel

theorem rowCheck12919 : row12919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12919 := by decide +kernel

theorem rowEval12919 (x : Key → ℝ) : Integer.Sparse.eval row12919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12919, Integer.Sparse.eval_collectBalanced, rawRowCheck12919]

theorem rawRowCheck12920 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form15 = rawRow12920 := by decide +kernel

theorem rowCheck12920 : row12920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12920 := by decide +kernel

theorem rowEval12920 (x : Key → ℝ) : Integer.Sparse.eval row12920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12920, Integer.Sparse.eval_collectBalanced, rawRowCheck12920]

theorem rawRowCheck12921 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form15 = rawRow12921 := by decide +kernel

theorem rowCheck12921 : row12921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12921 := by decide +kernel

theorem rowEval12921 (x : Key → ℝ) : Integer.Sparse.eval row12921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12921, Integer.Sparse.eval_collectBalanced, rawRowCheck12921]

theorem rawRowCheck12922 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form15 = rawRow12922 := by decide +kernel

theorem rowCheck12922 : row12922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12922 := by decide +kernel

theorem rowEval12922 (x : Key → ℝ) : Integer.Sparse.eval row12922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12922, Integer.Sparse.eval_collectBalanced, rawRowCheck12922]

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

theorem entryCheck26_15 : entry26_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_15 k)) := by decide +kernel

theorem rowsSound26_15 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12899 x
  · exact rowEval12900 x
  · exact rowEval12901 x
  · exact rowEval12902 x
  · exact rowEval12903 x
  · exact rowEval12904 x
  · exact rowEval12905 x
  · exact rowEval12906 x
  · exact rowEval12907 x
  · exact rowEval12908 x
  · exact rowEval12909 x
  · exact rowEval12910 x
  · exact rowEval12911 x
  · exact rowEval12912 x
  · exact rowEval12913 x
  · exact rowEval12914 x
  · exact rowEval12915 x
  · exact rowEval12916 x
  · exact rowEval12917 x
  · exact rowEval12918 x
  · exact rowEval12919 x
  · exact rowEval12920 x
  · exact rowEval12921 x
  · exact rowEval12922 x

theorem entryEval26_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_15 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck26_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_15]

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

theorem entryEvalRow15_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 15 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 15).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval15_0 B hB
  · exact entryEval15_1 B hB
  · exact entryEval15_2 B hB
  · exact entryEval15_3 B hB
  · exact entryEval15_4 B hB
  · exact entryEval15_5_e B hB
  · exact entryEval15_6 B hB
  · exact entryEval15_7 B hB
  · exact entryEval15_8_e B hB
  · exact entryEval15_9_e B hB
  · exact entryEval15_10 B hB
  · exact entryEval15_11 B hB
  · exact entryEval15_12 B hB
  · exact entryEval15_13 B hB
  · exact entryEval15_14 B hB
  · exact entryEval15_15 B hB
  · exact (entryEval16_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_15_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_15_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_15_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_15 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e_oai
