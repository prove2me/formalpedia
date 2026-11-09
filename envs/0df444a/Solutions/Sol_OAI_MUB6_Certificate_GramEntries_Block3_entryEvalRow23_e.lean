-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:16:35.954046+00:00
-- url     : https://prove2.me/submissions/15108230-393f-43f0-b860-790b29dd7814

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_23_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11792 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form1 = rawRow11792 := by decide +kernel

theorem rowCheck11792 : row11792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11792 := by decide +kernel

theorem rowEval11792 (x : Key → ℝ) : Integer.Sparse.eval row11792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11792, Integer.Sparse.eval_collectBalanced, rawRowCheck11792]

theorem rawRowCheck11793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form1 = rawRow11793 := by decide +kernel

theorem rowCheck11793 : row11793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11793 := by decide +kernel

theorem rowEval11793 (x : Key → ℝ) : Integer.Sparse.eval row11793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11793, Integer.Sparse.eval_collectBalanced, rawRowCheck11793]

theorem rawRowCheck11794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form1 = rawRow11794 := by decide +kernel

theorem rowCheck11794 : row11794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11794 := by decide +kernel

theorem rowEval11794 (x : Key → ℝ) : Integer.Sparse.eval row11794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11794, Integer.Sparse.eval_collectBalanced, rawRowCheck11794]

theorem rawRowCheck11795 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form1 = rawRow11795 := by decide +kernel

theorem rowCheck11795 : row11795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11795 := by decide +kernel

theorem rowEval11795 (x : Key → ℝ) : Integer.Sparse.eval row11795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11795, Integer.Sparse.eval_collectBalanced, rawRowCheck11795]

theorem rawRowCheck11796 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form1 = rawRow11796 := by decide +kernel

theorem rowCheck11796 : row11796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11796 := by decide +kernel

theorem rowEval11796 (x : Key → ℝ) : Integer.Sparse.eval row11796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11796, Integer.Sparse.eval_collectBalanced, rawRowCheck11796]

theorem rawRowCheck11797 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form1 = rawRow11797 := by decide +kernel

theorem rowCheck11797 : row11797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11797 := by decide +kernel

theorem rowEval11797 (x : Key → ℝ) : Integer.Sparse.eval row11797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11797, Integer.Sparse.eval_collectBalanced, rawRowCheck11797]

theorem rawRowCheck11798 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1 = rawRow11798 := by decide +kernel

theorem rowCheck11798 : row11798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11798 := by decide +kernel

theorem rowEval11798 (x : Key → ℝ) : Integer.Sparse.eval row11798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11798, Integer.Sparse.eval_collectBalanced, rawRowCheck11798]

theorem rawRowCheck11799 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1 = rawRow11799 := by decide +kernel

theorem rowCheck11799 : row11799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11799 := by decide +kernel

theorem rowEval11799 (x : Key → ℝ) : Integer.Sparse.eval row11799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11799, Integer.Sparse.eval_collectBalanced, rawRowCheck11799]

theorem rawRowCheck11800 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1 = rawRow11800 := by decide +kernel

theorem rowCheck11800 : row11800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11800 := by decide +kernel

theorem rowEval11800 (x : Key → ℝ) : Integer.Sparse.eval row11800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11800, Integer.Sparse.eval_collectBalanced, rawRowCheck11800]

theorem rawRowCheck11801 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1 = rawRow11801 := by decide +kernel

theorem rowCheck11801 : row11801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11801 := by decide +kernel

theorem rowEval11801 (x : Key → ℝ) : Integer.Sparse.eval row11801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11801, Integer.Sparse.eval_collectBalanced, rawRowCheck11801]

theorem rawRowCheck11802 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1 = rawRow11802 := by decide +kernel

theorem rowCheck11802 : row11802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11802 := by decide +kernel

theorem rowEval11802 (x : Key → ℝ) : Integer.Sparse.eval row11802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11802, Integer.Sparse.eval_collectBalanced, rawRowCheck11802]

theorem rawRowCheck11803 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1 = rawRow11803 := by decide +kernel

theorem rowCheck11803 : row11803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11803 := by decide +kernel

theorem rowEval11803 (x : Key → ℝ) : Integer.Sparse.eval row11803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11803, Integer.Sparse.eval_collectBalanced, rawRowCheck11803]

theorem rawRowCheck11804 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1 = rawRow11804 := by decide +kernel

theorem rowCheck11804 : row11804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11804 := by decide +kernel

theorem rowEval11804 (x : Key → ℝ) : Integer.Sparse.eval row11804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11804, Integer.Sparse.eval_collectBalanced, rawRowCheck11804]

theorem rawRowCheck11805 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1 = rawRow11805 := by decide +kernel

theorem rowCheck11805 : row11805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11805 := by decide +kernel

theorem rowEval11805 (x : Key → ℝ) : Integer.Sparse.eval row11805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11805, Integer.Sparse.eval_collectBalanced, rawRowCheck11805]

theorem rawRowCheck11806 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1 = rawRow11806 := by decide +kernel

theorem rowCheck11806 : row11806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11806 := by decide +kernel

theorem rowEval11806 (x : Key → ℝ) : Integer.Sparse.eval row11806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11806, Integer.Sparse.eval_collectBalanced, rawRowCheck11806]

theorem rawRowCheck11807 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1 = rawRow11807 := by decide +kernel

theorem rowCheck11807 : row11807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11807 := by decide +kernel

theorem rowEval11807 (x : Key → ℝ) : Integer.Sparse.eval row11807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11807, Integer.Sparse.eval_collectBalanced, rawRowCheck11807]

theorem rawRowCheck11808 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1 = rawRow11808 := by decide +kernel

theorem rowCheck11808 : row11808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11808 := by decide +kernel

theorem rowEval11808 (x : Key → ℝ) : Integer.Sparse.eval row11808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11808, Integer.Sparse.eval_collectBalanced, rawRowCheck11808]

theorem rawRowCheck11809 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1 = rawRow11809 := by decide +kernel

theorem rowCheck11809 : row11809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11809 := by decide +kernel

theorem rowEval11809 (x : Key → ℝ) : Integer.Sparse.eval row11809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11809, Integer.Sparse.eval_collectBalanced, rawRowCheck11809]

theorem rawRowCheck11810 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form2 = rawRow11810 := by decide +kernel

theorem rowCheck11810 : row11810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11810 := by decide +kernel

theorem rowEval11810 (x : Key → ℝ) : Integer.Sparse.eval row11810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11810, Integer.Sparse.eval_collectBalanced, rawRowCheck11810]

theorem rawRowCheck11811 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form2 = rawRow11811 := by decide +kernel

theorem rowCheck11811 : row11811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11811 := by decide +kernel

theorem rowEval11811 (x : Key → ℝ) : Integer.Sparse.eval row11811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11811, Integer.Sparse.eval_collectBalanced, rawRowCheck11811]

theorem rawRowCheck11812 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form2 = rawRow11812 := by decide +kernel

theorem rowCheck11812 : row11812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11812 := by decide +kernel

theorem rowEval11812 (x : Key → ℝ) : Integer.Sparse.eval row11812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11812, Integer.Sparse.eval_collectBalanced, rawRowCheck11812]

theorem rawRowCheck11813 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form2 = rawRow11813 := by decide +kernel

theorem rowCheck11813 : row11813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11813 := by decide +kernel

theorem rowEval11813 (x : Key → ℝ) : Integer.Sparse.eval row11813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11813, Integer.Sparse.eval_collectBalanced, rawRowCheck11813]

theorem rawRowCheck11814 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form2 = rawRow11814 := by decide +kernel

theorem rowCheck11814 : row11814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11814 := by decide +kernel

theorem rowEval11814 (x : Key → ℝ) : Integer.Sparse.eval row11814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11814, Integer.Sparse.eval_collectBalanced, rawRowCheck11814]

theorem rawRowCheck11815 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form2 = rawRow11815 := by decide +kernel

theorem rowCheck11815 : row11815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11815 := by decide +kernel

theorem rowEval11815 (x : Key → ℝ) : Integer.Sparse.eval row11815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11815, Integer.Sparse.eval_collectBalanced, rawRowCheck11815]

theorem rawRowCheck11816 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2 = rawRow11816 := by decide +kernel

theorem rowCheck11816 : row11816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11816 := by decide +kernel

theorem rowEval11816 (x : Key → ℝ) : Integer.Sparse.eval row11816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11816, Integer.Sparse.eval_collectBalanced, rawRowCheck11816]

theorem rawRowCheck11817 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2 = rawRow11817 := by decide +kernel

theorem rowCheck11817 : row11817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11817 := by decide +kernel

theorem rowEval11817 (x : Key → ℝ) : Integer.Sparse.eval row11817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11817, Integer.Sparse.eval_collectBalanced, rawRowCheck11817]

theorem rawRowCheck11818 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2 = rawRow11818 := by decide +kernel

theorem rowCheck11818 : row11818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11818 := by decide +kernel

theorem rowEval11818 (x : Key → ℝ) : Integer.Sparse.eval row11818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11818, Integer.Sparse.eval_collectBalanced, rawRowCheck11818]

theorem rawRowCheck11819 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2 = rawRow11819 := by decide +kernel

theorem rowCheck11819 : row11819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11819 := by decide +kernel

theorem rowEval11819 (x : Key → ℝ) : Integer.Sparse.eval row11819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11819, Integer.Sparse.eval_collectBalanced, rawRowCheck11819]

theorem rawRowCheck11820 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2 = rawRow11820 := by decide +kernel

theorem rowCheck11820 : row11820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11820 := by decide +kernel

theorem rowEval11820 (x : Key → ℝ) : Integer.Sparse.eval row11820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11820, Integer.Sparse.eval_collectBalanced, rawRowCheck11820]

theorem rawRowCheck11821 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2 = rawRow11821 := by decide +kernel

theorem rowCheck11821 : row11821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11821 := by decide +kernel

theorem rowEval11821 (x : Key → ℝ) : Integer.Sparse.eval row11821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11821, Integer.Sparse.eval_collectBalanced, rawRowCheck11821]

theorem rawRowCheck11822 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2 = rawRow11822 := by decide +kernel

theorem rowCheck11822 : row11822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11822 := by decide +kernel

theorem rowEval11822 (x : Key → ℝ) : Integer.Sparse.eval row11822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11822, Integer.Sparse.eval_collectBalanced, rawRowCheck11822]

theorem rawRowCheck11823 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2 = rawRow11823 := by decide +kernel

theorem rowCheck11823 : row11823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11823 := by decide +kernel

theorem rowEval11823 (x : Key → ℝ) : Integer.Sparse.eval row11823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11823, Integer.Sparse.eval_collectBalanced, rawRowCheck11823]

theorem rawRowCheck11824 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2 = rawRow11824 := by decide +kernel

theorem rowCheck11824 : row11824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11824 := by decide +kernel

theorem rowEval11824 (x : Key → ℝ) : Integer.Sparse.eval row11824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11824, Integer.Sparse.eval_collectBalanced, rawRowCheck11824]

theorem rawRowCheck11825 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2 = rawRow11825 := by decide +kernel

theorem rowCheck11825 : row11825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11825 := by decide +kernel

theorem rowEval11825 (x : Key → ℝ) : Integer.Sparse.eval row11825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11825, Integer.Sparse.eval_collectBalanced, rawRowCheck11825]

theorem rawRowCheck11826 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2 = rawRow11826 := by decide +kernel

theorem rowCheck11826 : row11826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11826 := by decide +kernel

theorem rowEval11826 (x : Key → ℝ) : Integer.Sparse.eval row11826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11826, Integer.Sparse.eval_collectBalanced, rawRowCheck11826]

theorem rawRowCheck11827 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2 = rawRow11827 := by decide +kernel

theorem rowCheck11827 : row11827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11827 := by decide +kernel

theorem rowEval11827 (x : Key → ℝ) : Integer.Sparse.eval row11827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11827, Integer.Sparse.eval_collectBalanced, rawRowCheck11827]

theorem rawRowCheck11828 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form3 = rawRow11828 := by decide +kernel

theorem rowCheck11828 : row11828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11828 := by decide +kernel

theorem rowEval11828 (x : Key → ℝ) : Integer.Sparse.eval row11828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11828, Integer.Sparse.eval_collectBalanced, rawRowCheck11828]

theorem rawRowCheck11829 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form3 = rawRow11829 := by decide +kernel

theorem rowCheck11829 : row11829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11829 := by decide +kernel

theorem rowEval11829 (x : Key → ℝ) : Integer.Sparse.eval row11829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11829, Integer.Sparse.eval_collectBalanced, rawRowCheck11829]

theorem rawRowCheck11830 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form3 = rawRow11830 := by decide +kernel

theorem rowCheck11830 : row11830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11830 := by decide +kernel

theorem rowEval11830 (x : Key → ℝ) : Integer.Sparse.eval row11830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11830, Integer.Sparse.eval_collectBalanced, rawRowCheck11830]

theorem rawRowCheck11831 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form3 = rawRow11831 := by decide +kernel

theorem rowCheck11831 : row11831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11831 := by decide +kernel

theorem rowEval11831 (x : Key → ℝ) : Integer.Sparse.eval row11831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11831, Integer.Sparse.eval_collectBalanced, rawRowCheck11831]

theorem rawRowCheck11832 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form3 = rawRow11832 := by decide +kernel

theorem rowCheck11832 : row11832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11832 := by decide +kernel

theorem rowEval11832 (x : Key → ℝ) : Integer.Sparse.eval row11832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11832, Integer.Sparse.eval_collectBalanced, rawRowCheck11832]

theorem rawRowCheck11833 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form3 = rawRow11833 := by decide +kernel

theorem rowCheck11833 : row11833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11833 := by decide +kernel

theorem rowEval11833 (x : Key → ℝ) : Integer.Sparse.eval row11833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11833, Integer.Sparse.eval_collectBalanced, rawRowCheck11833]

theorem rawRowCheck11834 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form3 = rawRow11834 := by decide +kernel

theorem rowCheck11834 : row11834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11834 := by decide +kernel

theorem rowEval11834 (x : Key → ℝ) : Integer.Sparse.eval row11834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11834, Integer.Sparse.eval_collectBalanced, rawRowCheck11834]

theorem rawRowCheck11835 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form3 = rawRow11835 := by decide +kernel

theorem rowCheck11835 : row11835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11835 := by decide +kernel

theorem rowEval11835 (x : Key → ℝ) : Integer.Sparse.eval row11835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11835, Integer.Sparse.eval_collectBalanced, rawRowCheck11835]

theorem rawRowCheck11836 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form3 = rawRow11836 := by decide +kernel

theorem rowCheck11836 : row11836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11836 := by decide +kernel

theorem rowEval11836 (x : Key → ℝ) : Integer.Sparse.eval row11836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11836, Integer.Sparse.eval_collectBalanced, rawRowCheck11836]

theorem rawRowCheck11837 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form3 = rawRow11837 := by decide +kernel

theorem rowCheck11837 : row11837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11837 := by decide +kernel

theorem rowEval11837 (x : Key → ℝ) : Integer.Sparse.eval row11837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11837, Integer.Sparse.eval_collectBalanced, rawRowCheck11837]

theorem rawRowCheck11838 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form3 = rawRow11838 := by decide +kernel

theorem rowCheck11838 : row11838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11838 := by decide +kernel

theorem rowEval11838 (x : Key → ℝ) : Integer.Sparse.eval row11838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11838, Integer.Sparse.eval_collectBalanced, rawRowCheck11838]

theorem rawRowCheck11839 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form3 = rawRow11839 := by decide +kernel

theorem rowCheck11839 : row11839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11839 := by decide +kernel

theorem rowEval11839 (x : Key → ℝ) : Integer.Sparse.eval row11839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck11839, Integer.Sparse.eval_collectBalanced, rawRowCheck11839]

theorem rawRowCheck11840 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form3 = rawRow11840 := by decide +kernel

theorem rowCheck11840 : row11840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11840 := by decide +kernel

theorem rowEval11840 (x : Key → ℝ) : Integer.Sparse.eval row11840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11840, Integer.Sparse.eval_collectBalanced, rawRowCheck11840]

theorem rawRowCheck11841 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form3 = rawRow11841 := by decide +kernel

theorem rowCheck11841 : row11841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11841 := by decide +kernel

theorem rowEval11841 (x : Key → ℝ) : Integer.Sparse.eval row11841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11841, Integer.Sparse.eval_collectBalanced, rawRowCheck11841]

theorem rawRowCheck11842 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form3 = rawRow11842 := by decide +kernel

theorem rowCheck11842 : row11842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11842 := by decide +kernel

theorem rowEval11842 (x : Key → ℝ) : Integer.Sparse.eval row11842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11842, Integer.Sparse.eval_collectBalanced, rawRowCheck11842]

theorem rawRowCheck11843 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form3 = rawRow11843 := by decide +kernel

theorem rowCheck11843 : row11843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11843 := by decide +kernel

theorem rowEval11843 (x : Key → ℝ) : Integer.Sparse.eval row11843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck11843, Integer.Sparse.eval_collectBalanced, rawRowCheck11843]

theorem rawRowCheck11844 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form3 = rawRow11844 := by decide +kernel

theorem rowCheck11844 : row11844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11844 := by decide +kernel

theorem rowEval11844 (x : Key → ℝ) : Integer.Sparse.eval row11844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11844, Integer.Sparse.eval_collectBalanced, rawRowCheck11844]

theorem rawRowCheck11845 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form3 = rawRow11845 := by decide +kernel

theorem rowCheck11845 : row11845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11845 := by decide +kernel

theorem rowEval11845 (x : Key → ℝ) : Integer.Sparse.eval row11845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck11845, Integer.Sparse.eval_collectBalanced, rawRowCheck11845]

theorem rawRowCheck11846 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form4 = rawRow11846 := by decide +kernel

theorem rowCheck11846 : row11846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11846 := by decide +kernel

theorem rowEval11846 (x : Key → ℝ) : Integer.Sparse.eval row11846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11846, Integer.Sparse.eval_collectBalanced, rawRowCheck11846]

theorem rawRowCheck11847 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form4 = rawRow11847 := by decide +kernel

theorem rowCheck11847 : row11847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11847 := by decide +kernel

theorem rowEval11847 (x : Key → ℝ) : Integer.Sparse.eval row11847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11847, Integer.Sparse.eval_collectBalanced, rawRowCheck11847]

theorem rawRowCheck11848 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form4 = rawRow11848 := by decide +kernel

theorem rowCheck11848 : row11848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11848 := by decide +kernel

theorem rowEval11848 (x : Key → ℝ) : Integer.Sparse.eval row11848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11848, Integer.Sparse.eval_collectBalanced, rawRowCheck11848]

theorem rawRowCheck11849 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form4 = rawRow11849 := by decide +kernel

theorem rowCheck11849 : row11849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11849 := by decide +kernel

theorem rowEval11849 (x : Key → ℝ) : Integer.Sparse.eval row11849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11849, Integer.Sparse.eval_collectBalanced, rawRowCheck11849]

theorem rawRowCheck11850 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form4 = rawRow11850 := by decide +kernel

theorem rowCheck11850 : row11850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11850 := by decide +kernel

theorem rowEval11850 (x : Key → ℝ) : Integer.Sparse.eval row11850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11850, Integer.Sparse.eval_collectBalanced, rawRowCheck11850]

theorem rawRowCheck11851 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form4 = rawRow11851 := by decide +kernel

theorem rowCheck11851 : row11851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11851 := by decide +kernel

theorem rowEval11851 (x : Key → ℝ) : Integer.Sparse.eval row11851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11851, Integer.Sparse.eval_collectBalanced, rawRowCheck11851]

theorem rawRowCheck11852 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4 = rawRow11852 := by decide +kernel

theorem rowCheck11852 : row11852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11852 := by decide +kernel

theorem rowEval11852 (x : Key → ℝ) : Integer.Sparse.eval row11852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11852, Integer.Sparse.eval_collectBalanced, rawRowCheck11852]

theorem rawRowCheck11853 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4 = rawRow11853 := by decide +kernel

theorem rowCheck11853 : row11853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11853 := by decide +kernel

theorem rowEval11853 (x : Key → ℝ) : Integer.Sparse.eval row11853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11853, Integer.Sparse.eval_collectBalanced, rawRowCheck11853]

theorem rawRowCheck11854 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4 = rawRow11854 := by decide +kernel

theorem rowCheck11854 : row11854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11854 := by decide +kernel

theorem rowEval11854 (x : Key → ℝ) : Integer.Sparse.eval row11854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11854, Integer.Sparse.eval_collectBalanced, rawRowCheck11854]

theorem rawRowCheck11855 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4 = rawRow11855 := by decide +kernel

theorem rowCheck11855 : row11855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11855 := by decide +kernel

theorem rowEval11855 (x : Key → ℝ) : Integer.Sparse.eval row11855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11855, Integer.Sparse.eval_collectBalanced, rawRowCheck11855]

theorem rawRowCheck11856 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4 = rawRow11856 := by decide +kernel

theorem rowCheck11856 : row11856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11856 := by decide +kernel

theorem rowEval11856 (x : Key → ℝ) : Integer.Sparse.eval row11856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11856, Integer.Sparse.eval_collectBalanced, rawRowCheck11856]

theorem rawRowCheck11857 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4 = rawRow11857 := by decide +kernel

theorem rowCheck11857 : row11857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11857 := by decide +kernel

theorem rowEval11857 (x : Key → ℝ) : Integer.Sparse.eval row11857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11857, Integer.Sparse.eval_collectBalanced, rawRowCheck11857]

theorem rawRowCheck11858 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4 = rawRow11858 := by decide +kernel

theorem rowCheck11858 : row11858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11858 := by decide +kernel

theorem rowEval11858 (x : Key → ℝ) : Integer.Sparse.eval row11858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11858, Integer.Sparse.eval_collectBalanced, rawRowCheck11858]

theorem rawRowCheck11859 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4 = rawRow11859 := by decide +kernel

theorem rowCheck11859 : row11859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11859 := by decide +kernel

theorem rowEval11859 (x : Key → ℝ) : Integer.Sparse.eval row11859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11859, Integer.Sparse.eval_collectBalanced, rawRowCheck11859]

theorem rawRowCheck11860 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4 = rawRow11860 := by decide +kernel

theorem rowCheck11860 : row11860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11860 := by decide +kernel

theorem rowEval11860 (x : Key → ℝ) : Integer.Sparse.eval row11860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11860, Integer.Sparse.eval_collectBalanced, rawRowCheck11860]

theorem rawRowCheck11861 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4 = rawRow11861 := by decide +kernel

theorem rowCheck11861 : row11861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11861 := by decide +kernel

theorem rowEval11861 (x : Key → ℝ) : Integer.Sparse.eval row11861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11861, Integer.Sparse.eval_collectBalanced, rawRowCheck11861]

theorem rawRowCheck11862 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4 = rawRow11862 := by decide +kernel

theorem rowCheck11862 : row11862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11862 := by decide +kernel

theorem rowEval11862 (x : Key → ℝ) : Integer.Sparse.eval row11862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11862, Integer.Sparse.eval_collectBalanced, rawRowCheck11862]

theorem rawRowCheck11863 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4 = rawRow11863 := by decide +kernel

theorem rowCheck11863 : row11863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11863 := by decide +kernel

theorem rowEval11863 (x : Key → ℝ) : Integer.Sparse.eval row11863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11863, Integer.Sparse.eval_collectBalanced, rawRowCheck11863]

theorem rawRowCheck11882 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form6 = rawRow11882 := by decide +kernel

theorem rowCheck11882 : row11882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11882 := by decide +kernel

theorem rowEval11882 (x : Key → ℝ) : Integer.Sparse.eval row11882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11882, Integer.Sparse.eval_collectBalanced, rawRowCheck11882]

theorem rawRowCheck11883 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form6 = rawRow11883 := by decide +kernel

theorem rowCheck11883 : row11883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11883 := by decide +kernel

theorem rowEval11883 (x : Key → ℝ) : Integer.Sparse.eval row11883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11883, Integer.Sparse.eval_collectBalanced, rawRowCheck11883]

theorem rawRowCheck11884 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form6 = rawRow11884 := by decide +kernel

theorem rowCheck11884 : row11884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11884 := by decide +kernel

theorem rowEval11884 (x : Key → ℝ) : Integer.Sparse.eval row11884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11884, Integer.Sparse.eval_collectBalanced, rawRowCheck11884]

theorem rawRowCheck11885 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form6 = rawRow11885 := by decide +kernel

theorem rowCheck11885 : row11885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11885 := by decide +kernel

theorem rowEval11885 (x : Key → ℝ) : Integer.Sparse.eval row11885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11885, Integer.Sparse.eval_collectBalanced, rawRowCheck11885]

theorem rawRowCheck11886 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form6 = rawRow11886 := by decide +kernel

theorem rowCheck11886 : row11886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11886 := by decide +kernel

theorem rowEval11886 (x : Key → ℝ) : Integer.Sparse.eval row11886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11886, Integer.Sparse.eval_collectBalanced, rawRowCheck11886]

theorem rawRowCheck11887 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form6 = rawRow11887 := by decide +kernel

theorem rowCheck11887 : row11887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11887 := by decide +kernel

theorem rowEval11887 (x : Key → ℝ) : Integer.Sparse.eval row11887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11887, Integer.Sparse.eval_collectBalanced, rawRowCheck11887]

theorem rawRowCheck11888 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6 = rawRow11888 := by decide +kernel

theorem rowCheck11888 : row11888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11888 := by decide +kernel

theorem rowEval11888 (x : Key → ℝ) : Integer.Sparse.eval row11888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11888, Integer.Sparse.eval_collectBalanced, rawRowCheck11888]

theorem rawRowCheck11889 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6 = rawRow11889 := by decide +kernel

theorem rowCheck11889 : row11889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11889 := by decide +kernel

theorem rowEval11889 (x : Key → ℝ) : Integer.Sparse.eval row11889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11889, Integer.Sparse.eval_collectBalanced, rawRowCheck11889]

theorem rawRowCheck11890 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6 = rawRow11890 := by decide +kernel

theorem rowCheck11890 : row11890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11890 := by decide +kernel

theorem rowEval11890 (x : Key → ℝ) : Integer.Sparse.eval row11890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11890, Integer.Sparse.eval_collectBalanced, rawRowCheck11890]

theorem rawRowCheck11891 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6 = rawRow11891 := by decide +kernel

theorem rowCheck11891 : row11891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11891 := by decide +kernel

theorem rowEval11891 (x : Key → ℝ) : Integer.Sparse.eval row11891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11891, Integer.Sparse.eval_collectBalanced, rawRowCheck11891]

theorem rawRowCheck11892 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6 = rawRow11892 := by decide +kernel

theorem rowCheck11892 : row11892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11892 := by decide +kernel

theorem rowEval11892 (x : Key → ℝ) : Integer.Sparse.eval row11892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11892, Integer.Sparse.eval_collectBalanced, rawRowCheck11892]

theorem rawRowCheck11893 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6 = rawRow11893 := by decide +kernel

theorem rowCheck11893 : row11893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11893 := by decide +kernel

theorem rowEval11893 (x : Key → ℝ) : Integer.Sparse.eval row11893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11893, Integer.Sparse.eval_collectBalanced, rawRowCheck11893]

theorem rawRowCheck11894 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6 = rawRow11894 := by decide +kernel

theorem rowCheck11894 : row11894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11894 := by decide +kernel

theorem rowEval11894 (x : Key → ℝ) : Integer.Sparse.eval row11894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11894, Integer.Sparse.eval_collectBalanced, rawRowCheck11894]

theorem rawRowCheck11895 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6 = rawRow11895 := by decide +kernel

theorem rowCheck11895 : row11895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11895 := by decide +kernel

theorem rowEval11895 (x : Key → ℝ) : Integer.Sparse.eval row11895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11895, Integer.Sparse.eval_collectBalanced, rawRowCheck11895]

theorem rawRowCheck11896 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6 = rawRow11896 := by decide +kernel

theorem rowCheck11896 : row11896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11896 := by decide +kernel

theorem rowEval11896 (x : Key → ℝ) : Integer.Sparse.eval row11896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11896, Integer.Sparse.eval_collectBalanced, rawRowCheck11896]

theorem rawRowCheck11897 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6 = rawRow11897 := by decide +kernel

theorem rowCheck11897 : row11897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11897 := by decide +kernel

theorem rowEval11897 (x : Key → ℝ) : Integer.Sparse.eval row11897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11897, Integer.Sparse.eval_collectBalanced, rawRowCheck11897]

theorem rawRowCheck11898 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6 = rawRow11898 := by decide +kernel

theorem rowCheck11898 : row11898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11898 := by decide +kernel

theorem rowEval11898 (x : Key → ℝ) : Integer.Sparse.eval row11898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11898, Integer.Sparse.eval_collectBalanced, rawRowCheck11898]

theorem rawRowCheck11899 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6 = rawRow11899 := by decide +kernel

theorem rowCheck11899 : row11899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11899 := by decide +kernel

theorem rowEval11899 (x : Key → ℝ) : Integer.Sparse.eval row11899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11899, Integer.Sparse.eval_collectBalanced, rawRowCheck11899]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck11954 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form10 = rawRow11954 := by decide +kernel

theorem rowCheck11954 : row11954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11954 := by decide +kernel

theorem rowEval11954 (x : Key → ℝ) : Integer.Sparse.eval row11954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11954, Integer.Sparse.eval_collectBalanced, rawRowCheck11954]

theorem rawRowCheck11955 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form10 = rawRow11955 := by decide +kernel

theorem rowCheck11955 : row11955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11955 := by decide +kernel

theorem rowEval11955 (x : Key → ℝ) : Integer.Sparse.eval row11955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11955, Integer.Sparse.eval_collectBalanced, rawRowCheck11955]

theorem rawRowCheck11956 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form10 = rawRow11956 := by decide +kernel

theorem rowCheck11956 : row11956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11956 := by decide +kernel

theorem rowEval11956 (x : Key → ℝ) : Integer.Sparse.eval row11956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11956, Integer.Sparse.eval_collectBalanced, rawRowCheck11956]

theorem rawRowCheck11957 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form10 = rawRow11957 := by decide +kernel

theorem rowCheck11957 : row11957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11957 := by decide +kernel

theorem rowEval11957 (x : Key → ℝ) : Integer.Sparse.eval row11957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11957, Integer.Sparse.eval_collectBalanced, rawRowCheck11957]

theorem rawRowCheck11958 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form10 = rawRow11958 := by decide +kernel

theorem rowCheck11958 : row11958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11958 := by decide +kernel

theorem rowEval11958 (x : Key → ℝ) : Integer.Sparse.eval row11958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11958, Integer.Sparse.eval_collectBalanced, rawRowCheck11958]

theorem rawRowCheck11959 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form10 = rawRow11959 := by decide +kernel

theorem rowCheck11959 : row11959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11959 := by decide +kernel

theorem rowEval11959 (x : Key → ℝ) : Integer.Sparse.eval row11959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11959, Integer.Sparse.eval_collectBalanced, rawRowCheck11959]

theorem rawRowCheck11960 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form10 = rawRow11960 := by decide +kernel

theorem rowCheck11960 : row11960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11960 := by decide +kernel

theorem rowEval11960 (x : Key → ℝ) : Integer.Sparse.eval row11960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11960, Integer.Sparse.eval_collectBalanced, rawRowCheck11960]

theorem rawRowCheck11961 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form10 = rawRow11961 := by decide +kernel

theorem rowCheck11961 : row11961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11961 := by decide +kernel

theorem rowEval11961 (x : Key → ℝ) : Integer.Sparse.eval row11961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11961, Integer.Sparse.eval_collectBalanced, rawRowCheck11961]

theorem rawRowCheck11962 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form10 = rawRow11962 := by decide +kernel

theorem rowCheck11962 : row11962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11962 := by decide +kernel

theorem rowEval11962 (x : Key → ℝ) : Integer.Sparse.eval row11962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11962, Integer.Sparse.eval_collectBalanced, rawRowCheck11962]

theorem rawRowCheck11963 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form10 = rawRow11963 := by decide +kernel

theorem rowCheck11963 : row11963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11963 := by decide +kernel

theorem rowEval11963 (x : Key → ℝ) : Integer.Sparse.eval row11963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11963, Integer.Sparse.eval_collectBalanced, rawRowCheck11963]

theorem rawRowCheck11964 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form10 = rawRow11964 := by decide +kernel

theorem rowCheck11964 : row11964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11964 := by decide +kernel

theorem rowEval11964 (x : Key → ℝ) : Integer.Sparse.eval row11964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11964, Integer.Sparse.eval_collectBalanced, rawRowCheck11964]

theorem rawRowCheck11965 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form10 = rawRow11965 := by decide +kernel

theorem rowCheck11965 : row11965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11965 := by decide +kernel

theorem rowEval11965 (x : Key → ℝ) : Integer.Sparse.eval row11965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck11965, Integer.Sparse.eval_collectBalanced, rawRowCheck11965]

theorem rawRowCheck11966 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form10 = rawRow11966 := by decide +kernel

theorem rowCheck11966 : row11966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11966 := by decide +kernel

theorem rowEval11966 (x : Key → ℝ) : Integer.Sparse.eval row11966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11966, Integer.Sparse.eval_collectBalanced, rawRowCheck11966]

theorem rawRowCheck11967 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form10 = rawRow11967 := by decide +kernel

theorem rowCheck11967 : row11967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11967 := by decide +kernel

theorem rowEval11967 (x : Key → ℝ) : Integer.Sparse.eval row11967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11967, Integer.Sparse.eval_collectBalanced, rawRowCheck11967]

theorem rawRowCheck11968 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form10 = rawRow11968 := by decide +kernel

theorem rowCheck11968 : row11968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11968 := by decide +kernel

theorem rowEval11968 (x : Key → ℝ) : Integer.Sparse.eval row11968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11968, Integer.Sparse.eval_collectBalanced, rawRowCheck11968]

theorem rawRowCheck11969 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form10 = rawRow11969 := by decide +kernel

theorem rowCheck11969 : row11969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11969 := by decide +kernel

theorem rowEval11969 (x : Key → ℝ) : Integer.Sparse.eval row11969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck11969, Integer.Sparse.eval_collectBalanced, rawRowCheck11969]

theorem rawRowCheck11970 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form10 = rawRow11970 := by decide +kernel

theorem rowCheck11970 : row11970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11970 := by decide +kernel

theorem rowEval11970 (x : Key → ℝ) : Integer.Sparse.eval row11970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11970, Integer.Sparse.eval_collectBalanced, rawRowCheck11970]

theorem rawRowCheck11971 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form10 = rawRow11971 := by decide +kernel

theorem rowCheck11971 : row11971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11971 := by decide +kernel

theorem rowEval11971 (x : Key → ℝ) : Integer.Sparse.eval row11971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck11971, Integer.Sparse.eval_collectBalanced, rawRowCheck11971]

theorem rawRowCheck11972 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form11 = rawRow11972 := by decide +kernel

theorem rowCheck11972 : row11972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11972 := by decide +kernel

theorem rowEval11972 (x : Key → ℝ) : Integer.Sparse.eval row11972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11972, Integer.Sparse.eval_collectBalanced, rawRowCheck11972]

theorem rawRowCheck11973 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form11 = rawRow11973 := by decide +kernel

theorem rowCheck11973 : row11973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11973 := by decide +kernel

theorem rowEval11973 (x : Key → ℝ) : Integer.Sparse.eval row11973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11973, Integer.Sparse.eval_collectBalanced, rawRowCheck11973]

theorem rawRowCheck11974 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form11 = rawRow11974 := by decide +kernel

theorem rowCheck11974 : row11974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11974 := by decide +kernel

theorem rowEval11974 (x : Key → ℝ) : Integer.Sparse.eval row11974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11974, Integer.Sparse.eval_collectBalanced, rawRowCheck11974]

theorem rawRowCheck11975 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form11 = rawRow11975 := by decide +kernel

theorem rowCheck11975 : row11975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11975 := by decide +kernel

theorem rowEval11975 (x : Key → ℝ) : Integer.Sparse.eval row11975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11975, Integer.Sparse.eval_collectBalanced, rawRowCheck11975]

theorem rawRowCheck11976 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form11 = rawRow11976 := by decide +kernel

theorem rowCheck11976 : row11976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11976 := by decide +kernel

theorem rowEval11976 (x : Key → ℝ) : Integer.Sparse.eval row11976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11976, Integer.Sparse.eval_collectBalanced, rawRowCheck11976]

theorem rawRowCheck11977 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form11 = rawRow11977 := by decide +kernel

theorem rowCheck11977 : row11977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11977 := by decide +kernel

theorem rowEval11977 (x : Key → ℝ) : Integer.Sparse.eval row11977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11977, Integer.Sparse.eval_collectBalanced, rawRowCheck11977]

theorem rawRowCheck11978 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form11 = rawRow11978 := by decide +kernel

theorem rowCheck11978 : row11978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11978 := by decide +kernel

theorem rowEval11978 (x : Key → ℝ) : Integer.Sparse.eval row11978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11978, Integer.Sparse.eval_collectBalanced, rawRowCheck11978]

theorem rawRowCheck11979 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form11 = rawRow11979 := by decide +kernel

theorem rowCheck11979 : row11979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11979 := by decide +kernel

theorem rowEval11979 (x : Key → ℝ) : Integer.Sparse.eval row11979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11979, Integer.Sparse.eval_collectBalanced, rawRowCheck11979]

theorem rawRowCheck11980 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form11 = rawRow11980 := by decide +kernel

theorem rowCheck11980 : row11980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11980 := by decide +kernel

theorem rowEval11980 (x : Key → ℝ) : Integer.Sparse.eval row11980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11980, Integer.Sparse.eval_collectBalanced, rawRowCheck11980]

theorem rawRowCheck11981 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form11 = rawRow11981 := by decide +kernel

theorem rowCheck11981 : row11981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11981 := by decide +kernel

theorem rowEval11981 (x : Key → ℝ) : Integer.Sparse.eval row11981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11981, Integer.Sparse.eval_collectBalanced, rawRowCheck11981]

theorem rawRowCheck11982 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form11 = rawRow11982 := by decide +kernel

theorem rowCheck11982 : row11982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11982 := by decide +kernel

theorem rowEval11982 (x : Key → ℝ) : Integer.Sparse.eval row11982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11982, Integer.Sparse.eval_collectBalanced, rawRowCheck11982]

theorem rawRowCheck11983 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form11 = rawRow11983 := by decide +kernel

theorem rowCheck11983 : row11983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11983 := by decide +kernel

theorem rowEval11983 (x : Key → ℝ) : Integer.Sparse.eval row11983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11983, Integer.Sparse.eval_collectBalanced, rawRowCheck11983]

theorem rawRowCheck11984 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form11 = rawRow11984 := by decide +kernel

theorem rowCheck11984 : row11984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11984 := by decide +kernel

theorem rowEval11984 (x : Key → ℝ) : Integer.Sparse.eval row11984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11984, Integer.Sparse.eval_collectBalanced, rawRowCheck11984]

theorem rawRowCheck11985 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form11 = rawRow11985 := by decide +kernel

theorem rowCheck11985 : row11985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11985 := by decide +kernel

theorem rowEval11985 (x : Key → ℝ) : Integer.Sparse.eval row11985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11985, Integer.Sparse.eval_collectBalanced, rawRowCheck11985]

theorem rawRowCheck11986 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form11 = rawRow11986 := by decide +kernel

theorem rowCheck11986 : row11986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11986 := by decide +kernel

theorem rowEval11986 (x : Key → ℝ) : Integer.Sparse.eval row11986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11986, Integer.Sparse.eval_collectBalanced, rawRowCheck11986]

theorem rawRowCheck11987 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form11 = rawRow11987 := by decide +kernel

theorem rowCheck11987 : row11987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11987 := by decide +kernel

theorem rowEval11987 (x : Key → ℝ) : Integer.Sparse.eval row11987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11987, Integer.Sparse.eval_collectBalanced, rawRowCheck11987]

theorem rawRowCheck11988 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form11 = rawRow11988 := by decide +kernel

theorem rowCheck11988 : row11988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11988 := by decide +kernel

theorem rowEval11988 (x : Key → ℝ) : Integer.Sparse.eval row11988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11988, Integer.Sparse.eval_collectBalanced, rawRowCheck11988]

theorem rawRowCheck11989 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form11 = rawRow11989 := by decide +kernel

theorem rowCheck11989 : row11989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11989 := by decide +kernel

theorem rowEval11989 (x : Key → ℝ) : Integer.Sparse.eval row11989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11989, Integer.Sparse.eval_collectBalanced, rawRowCheck11989]

theorem rawRowCheck11990 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form12 = rawRow11990 := by decide +kernel

theorem rowCheck11990 : row11990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11990 := by decide +kernel

theorem rowEval11990 (x : Key → ℝ) : Integer.Sparse.eval row11990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11990, Integer.Sparse.eval_collectBalanced, rawRowCheck11990]

theorem rawRowCheck11991 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form12 = rawRow11991 := by decide +kernel

theorem rowCheck11991 : row11991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11991 := by decide +kernel

theorem rowEval11991 (x : Key → ℝ) : Integer.Sparse.eval row11991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11991, Integer.Sparse.eval_collectBalanced, rawRowCheck11991]

theorem rawRowCheck11992 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form12 = rawRow11992 := by decide +kernel

theorem rowCheck11992 : row11992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11992 := by decide +kernel

theorem rowEval11992 (x : Key → ℝ) : Integer.Sparse.eval row11992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11992, Integer.Sparse.eval_collectBalanced, rawRowCheck11992]

theorem rawRowCheck11993 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form12 = rawRow11993 := by decide +kernel

theorem rowCheck11993 : row11993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11993 := by decide +kernel

theorem rowEval11993 (x : Key → ℝ) : Integer.Sparse.eval row11993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11993, Integer.Sparse.eval_collectBalanced, rawRowCheck11993]

theorem rawRowCheck11994 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form12 = rawRow11994 := by decide +kernel

theorem rowCheck11994 : row11994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11994 := by decide +kernel

theorem rowEval11994 (x : Key → ℝ) : Integer.Sparse.eval row11994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11994, Integer.Sparse.eval_collectBalanced, rawRowCheck11994]

theorem rawRowCheck11995 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form12 = rawRow11995 := by decide +kernel

theorem rowCheck11995 : row11995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11995 := by decide +kernel

theorem rowEval11995 (x : Key → ℝ) : Integer.Sparse.eval row11995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11995, Integer.Sparse.eval_collectBalanced, rawRowCheck11995]

theorem rawRowCheck11996 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12 = rawRow11996 := by decide +kernel

theorem rowCheck11996 : row11996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11996 := by decide +kernel

theorem rowEval11996 (x : Key → ℝ) : Integer.Sparse.eval row11996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11996, Integer.Sparse.eval_collectBalanced, rawRowCheck11996]

theorem rawRowCheck11997 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12 = rawRow11997 := by decide +kernel

theorem rowCheck11997 : row11997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11997 := by decide +kernel

theorem rowEval11997 (x : Key → ℝ) : Integer.Sparse.eval row11997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11997, Integer.Sparse.eval_collectBalanced, rawRowCheck11997]

theorem rawRowCheck11998 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12 = rawRow11998 := by decide +kernel

theorem rowCheck11998 : row11998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11998 := by decide +kernel

theorem rowEval11998 (x : Key → ℝ) : Integer.Sparse.eval row11998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11998, Integer.Sparse.eval_collectBalanced, rawRowCheck11998]

theorem rawRowCheck11999 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12 = rawRow11999 := by decide +kernel

theorem rowCheck11999 : row11999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11999 := by decide +kernel

theorem rowEval11999 (x : Key → ℝ) : Integer.Sparse.eval row11999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11999, Integer.Sparse.eval_collectBalanced, rawRowCheck11999]

theorem rawRowCheck12000 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12 = rawRow12000 := by decide +kernel

theorem rowCheck12000 : row12000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12000 := by decide +kernel

theorem rowEval12000 (x : Key → ℝ) : Integer.Sparse.eval row12000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12000, Integer.Sparse.eval_collectBalanced, rawRowCheck12000]

theorem rawRowCheck12001 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12 = rawRow12001 := by decide +kernel

theorem rowCheck12001 : row12001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12001 := by decide +kernel

theorem rowEval12001 (x : Key → ℝ) : Integer.Sparse.eval row12001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12001, Integer.Sparse.eval_collectBalanced, rawRowCheck12001]

theorem rawRowCheck12002 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12 = rawRow12002 := by decide +kernel

theorem rowCheck12002 : row12002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12002 := by decide +kernel

theorem rowEval12002 (x : Key → ℝ) : Integer.Sparse.eval row12002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12002, Integer.Sparse.eval_collectBalanced, rawRowCheck12002]

theorem rawRowCheck12003 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12 = rawRow12003 := by decide +kernel

theorem rowCheck12003 : row12003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12003 := by decide +kernel

theorem rowEval12003 (x : Key → ℝ) : Integer.Sparse.eval row12003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12003, Integer.Sparse.eval_collectBalanced, rawRowCheck12003]

theorem rawRowCheck12004 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12 = rawRow12004 := by decide +kernel

theorem rowCheck12004 : row12004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12004 := by decide +kernel

theorem rowEval12004 (x : Key → ℝ) : Integer.Sparse.eval row12004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12004, Integer.Sparse.eval_collectBalanced, rawRowCheck12004]

theorem rawRowCheck12005 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12 = rawRow12005 := by decide +kernel

theorem rowCheck12005 : row12005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12005 := by decide +kernel

theorem rowEval12005 (x : Key → ℝ) : Integer.Sparse.eval row12005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12005, Integer.Sparse.eval_collectBalanced, rawRowCheck12005]

theorem rawRowCheck12006 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12 = rawRow12006 := by decide +kernel

theorem rowCheck12006 : row12006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12006 := by decide +kernel

theorem rowEval12006 (x : Key → ℝ) : Integer.Sparse.eval row12006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12006, Integer.Sparse.eval_collectBalanced, rawRowCheck12006]

theorem rawRowCheck12007 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12 = rawRow12007 := by decide +kernel

theorem rowCheck12007 : row12007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12007 := by decide +kernel

theorem rowEval12007 (x : Key → ℝ) : Integer.Sparse.eval row12007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12007, Integer.Sparse.eval_collectBalanced, rawRowCheck12007]

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

theorem rawRowCheck12026 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12026 := by decide +kernel

theorem rowCheck12026 : row12026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12026 := by decide +kernel

theorem rowEval12026 (x : Key → ℝ) : Integer.Sparse.eval row12026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12026, Integer.Sparse.eval_collectBalanced, rawRowCheck12026]

theorem rawRowCheck12027 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12027 := by decide +kernel

theorem rowCheck12027 : row12027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12027 := by decide +kernel

theorem rowEval12027 (x : Key → ℝ) : Integer.Sparse.eval row12027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12027, Integer.Sparse.eval_collectBalanced, rawRowCheck12027]

theorem rawRowCheck12028 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12028 := by decide +kernel

theorem rowCheck12028 : row12028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12028 := by decide +kernel

theorem rowEval12028 (x : Key → ℝ) : Integer.Sparse.eval row12028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12028, Integer.Sparse.eval_collectBalanced, rawRowCheck12028]

theorem rawRowCheck12029 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form14 = rawRow12029 := by decide +kernel

theorem rowCheck12029 : row12029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12029 := by decide +kernel

theorem rowEval12029 (x : Key → ℝ) : Integer.Sparse.eval row12029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12029, Integer.Sparse.eval_collectBalanced, rawRowCheck12029]

theorem rawRowCheck12030 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form14 = rawRow12030 := by decide +kernel

theorem rowCheck12030 : row12030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12030 := by decide +kernel

theorem rowEval12030 (x : Key → ℝ) : Integer.Sparse.eval row12030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12030, Integer.Sparse.eval_collectBalanced, rawRowCheck12030]

theorem rawRowCheck12031 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form14 = rawRow12031 := by decide +kernel

theorem rowCheck12031 : row12031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12031 := by decide +kernel

theorem rowEval12031 (x : Key → ℝ) : Integer.Sparse.eval row12031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12031, Integer.Sparse.eval_collectBalanced, rawRowCheck12031]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck12032 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12032 := by decide +kernel

theorem rowCheck12032 : row12032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12032 := by decide +kernel

theorem rowEval12032 (x : Key → ℝ) : Integer.Sparse.eval row12032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12032, Integer.Sparse.eval_collectBalanced, rawRowCheck12032]

theorem rawRowCheck12033 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12033 := by decide +kernel

theorem rowCheck12033 : row12033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12033 := by decide +kernel

theorem rowEval12033 (x : Key → ℝ) : Integer.Sparse.eval row12033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12033, Integer.Sparse.eval_collectBalanced, rawRowCheck12033]

theorem rawRowCheck12034 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12034 := by decide +kernel

theorem rowCheck12034 : row12034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12034 := by decide +kernel

theorem rowEval12034 (x : Key → ℝ) : Integer.Sparse.eval row12034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12034, Integer.Sparse.eval_collectBalanced, rawRowCheck12034]

theorem rawRowCheck12035 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14 = rawRow12035 := by decide +kernel

theorem rowCheck12035 : row12035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12035 := by decide +kernel

theorem rowEval12035 (x : Key → ℝ) : Integer.Sparse.eval row12035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12035, Integer.Sparse.eval_collectBalanced, rawRowCheck12035]

theorem rawRowCheck12036 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14 = rawRow12036 := by decide +kernel

theorem rowCheck12036 : row12036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12036 := by decide +kernel

theorem rowEval12036 (x : Key → ℝ) : Integer.Sparse.eval row12036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12036, Integer.Sparse.eval_collectBalanced, rawRowCheck12036]

theorem rawRowCheck12037 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14 = rawRow12037 := by decide +kernel

theorem rowCheck12037 : row12037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12037 := by decide +kernel

theorem rowEval12037 (x : Key → ℝ) : Integer.Sparse.eval row12037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12037, Integer.Sparse.eval_collectBalanced, rawRowCheck12037]

theorem rawRowCheck12038 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14 = rawRow12038 := by decide +kernel

theorem rowCheck12038 : row12038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12038 := by decide +kernel

theorem rowEval12038 (x : Key → ℝ) : Integer.Sparse.eval row12038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12038, Integer.Sparse.eval_collectBalanced, rawRowCheck12038]

theorem rawRowCheck12039 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14 = rawRow12039 := by decide +kernel

theorem rowCheck12039 : row12039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12039 := by decide +kernel

theorem rowEval12039 (x : Key → ℝ) : Integer.Sparse.eval row12039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12039, Integer.Sparse.eval_collectBalanced, rawRowCheck12039]

theorem rawRowCheck12040 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14 = rawRow12040 := by decide +kernel

theorem rowCheck12040 : row12040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12040 := by decide +kernel

theorem rowEval12040 (x : Key → ℝ) : Integer.Sparse.eval row12040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12040, Integer.Sparse.eval_collectBalanced, rawRowCheck12040]

theorem rawRowCheck12041 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14 = rawRow12041 := by decide +kernel

theorem rowCheck12041 : row12041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12041 := by decide +kernel

theorem rowEval12041 (x : Key → ℝ) : Integer.Sparse.eval row12041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12041, Integer.Sparse.eval_collectBalanced, rawRowCheck12041]

theorem rawRowCheck12042 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14 = rawRow12042 := by decide +kernel

theorem rowCheck12042 : row12042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12042 := by decide +kernel

theorem rowEval12042 (x : Key → ℝ) : Integer.Sparse.eval row12042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12042, Integer.Sparse.eval_collectBalanced, rawRowCheck12042]

theorem rawRowCheck12043 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14 = rawRow12043 := by decide +kernel

theorem rowCheck12043 : row12043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12043 := by decide +kernel

theorem rowEval12043 (x : Key → ℝ) : Integer.Sparse.eval row12043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12043, Integer.Sparse.eval_collectBalanced, rawRowCheck12043]

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

theorem rawRowCheck12062 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12062 := by decide +kernel

theorem rowCheck12062 : row12062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12062 := by decide +kernel

theorem rowEval12062 (x : Key → ℝ) : Integer.Sparse.eval row12062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12062, Integer.Sparse.eval_collectBalanced, rawRowCheck12062]

theorem rawRowCheck12063 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12063 := by decide +kernel

theorem rowCheck12063 : row12063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12063 := by decide +kernel

theorem rowEval12063 (x : Key → ℝ) : Integer.Sparse.eval row12063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12063, Integer.Sparse.eval_collectBalanced, rawRowCheck12063]

theorem rawRowCheck12064 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12064 := by decide +kernel

theorem rowCheck12064 : row12064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12064 := by decide +kernel

theorem rowEval12064 (x : Key → ℝ) : Integer.Sparse.eval row12064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12064, Integer.Sparse.eval_collectBalanced, rawRowCheck12064]

theorem rawRowCheck12065 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form16 = rawRow12065 := by decide +kernel

theorem rowCheck12065 : row12065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12065 := by decide +kernel

theorem rowEval12065 (x : Key → ℝ) : Integer.Sparse.eval row12065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12065, Integer.Sparse.eval_collectBalanced, rawRowCheck12065]

theorem rawRowCheck12066 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form16 = rawRow12066 := by decide +kernel

theorem rowCheck12066 : row12066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12066 := by decide +kernel

theorem rowEval12066 (x : Key → ℝ) : Integer.Sparse.eval row12066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12066, Integer.Sparse.eval_collectBalanced, rawRowCheck12066]

theorem rawRowCheck12067 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form16 = rawRow12067 := by decide +kernel

theorem rowCheck12067 : row12067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12067 := by decide +kernel

theorem rowEval12067 (x : Key → ℝ) : Integer.Sparse.eval row12067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12067, Integer.Sparse.eval_collectBalanced, rawRowCheck12067]

theorem rawRowCheck12068 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12068 := by decide +kernel

theorem rowCheck12068 : row12068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12068 := by decide +kernel

theorem rowEval12068 (x : Key → ℝ) : Integer.Sparse.eval row12068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12068, Integer.Sparse.eval_collectBalanced, rawRowCheck12068]

theorem rawRowCheck12069 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12069 := by decide +kernel

theorem rowCheck12069 : row12069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12069 := by decide +kernel

theorem rowEval12069 (x : Key → ℝ) : Integer.Sparse.eval row12069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12069, Integer.Sparse.eval_collectBalanced, rawRowCheck12069]

theorem rawRowCheck12070 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12070 := by decide +kernel

theorem rowCheck12070 : row12070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12070 := by decide +kernel

theorem rowEval12070 (x : Key → ℝ) : Integer.Sparse.eval row12070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12070, Integer.Sparse.eval_collectBalanced, rawRowCheck12070]

theorem rawRowCheck12071 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16 = rawRow12071 := by decide +kernel

theorem rowCheck12071 : row12071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12071 := by decide +kernel

theorem rowEval12071 (x : Key → ℝ) : Integer.Sparse.eval row12071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12071, Integer.Sparse.eval_collectBalanced, rawRowCheck12071]

theorem rawRowCheck12072 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16 = rawRow12072 := by decide +kernel

theorem rowCheck12072 : row12072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12072 := by decide +kernel

theorem rowEval12072 (x : Key → ℝ) : Integer.Sparse.eval row12072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12072, Integer.Sparse.eval_collectBalanced, rawRowCheck12072]

theorem rawRowCheck12073 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16 = rawRow12073 := by decide +kernel

theorem rowCheck12073 : row12073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12073 := by decide +kernel

theorem rowEval12073 (x : Key → ℝ) : Integer.Sparse.eval row12073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12073, Integer.Sparse.eval_collectBalanced, rawRowCheck12073]

theorem rawRowCheck12074 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16 = rawRow12074 := by decide +kernel

theorem rowCheck12074 : row12074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12074 := by decide +kernel

theorem rowEval12074 (x : Key → ℝ) : Integer.Sparse.eval row12074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12074, Integer.Sparse.eval_collectBalanced, rawRowCheck12074]

theorem rawRowCheck12075 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16 = rawRow12075 := by decide +kernel

theorem rowCheck12075 : row12075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12075 := by decide +kernel

theorem rowEval12075 (x : Key → ℝ) : Integer.Sparse.eval row12075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12075, Integer.Sparse.eval_collectBalanced, rawRowCheck12075]

theorem rawRowCheck12076 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16 = rawRow12076 := by decide +kernel

theorem rowCheck12076 : row12076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12076 := by decide +kernel

theorem rowEval12076 (x : Key → ℝ) : Integer.Sparse.eval row12076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12076, Integer.Sparse.eval_collectBalanced, rawRowCheck12076]

theorem rawRowCheck12077 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16 = rawRow12077 := by decide +kernel

theorem rowCheck12077 : row12077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12077 := by decide +kernel

theorem rowEval12077 (x : Key → ℝ) : Integer.Sparse.eval row12077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12077, Integer.Sparse.eval_collectBalanced, rawRowCheck12077]

theorem rawRowCheck12078 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16 = rawRow12078 := by decide +kernel

theorem rowCheck12078 : row12078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12078 := by decide +kernel

theorem rowEval12078 (x : Key → ℝ) : Integer.Sparse.eval row12078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12078, Integer.Sparse.eval_collectBalanced, rawRowCheck12078]

theorem rawRowCheck12079 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16 = rawRow12079 := by decide +kernel

theorem rowCheck12079 : row12079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12079 := by decide +kernel

theorem rowEval12079 (x : Key → ℝ) : Integer.Sparse.eval row12079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12079, Integer.Sparse.eval_collectBalanced, rawRowCheck12079]

theorem rawRowCheck12080 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form17 = rawRow12080 := by decide +kernel

theorem rowCheck12080 : row12080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12080 := by decide +kernel

theorem rowEval12080 (x : Key → ℝ) : Integer.Sparse.eval row12080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12080, Integer.Sparse.eval_collectBalanced, rawRowCheck12080]

theorem rawRowCheck12081 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form17 = rawRow12081 := by decide +kernel

theorem rowCheck12081 : row12081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12081 := by decide +kernel

theorem rowEval12081 (x : Key → ℝ) : Integer.Sparse.eval row12081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12081, Integer.Sparse.eval_collectBalanced, rawRowCheck12081]

theorem rawRowCheck12082 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form17 = rawRow12082 := by decide +kernel

theorem rowCheck12082 : row12082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12082 := by decide +kernel

theorem rowEval12082 (x : Key → ℝ) : Integer.Sparse.eval row12082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12082, Integer.Sparse.eval_collectBalanced, rawRowCheck12082]

theorem rawRowCheck12083 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form17 = rawRow12083 := by decide +kernel

theorem rowCheck12083 : row12083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12083 := by decide +kernel

theorem rowEval12083 (x : Key → ℝ) : Integer.Sparse.eval row12083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12083, Integer.Sparse.eval_collectBalanced, rawRowCheck12083]

theorem rawRowCheck12084 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form17 = rawRow12084 := by decide +kernel

theorem rowCheck12084 : row12084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12084 := by decide +kernel

theorem rowEval12084 (x : Key → ℝ) : Integer.Sparse.eval row12084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12084, Integer.Sparse.eval_collectBalanced, rawRowCheck12084]

theorem rawRowCheck12085 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form17 = rawRow12085 := by decide +kernel

theorem rowCheck12085 : row12085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12085 := by decide +kernel

theorem rowEval12085 (x : Key → ℝ) : Integer.Sparse.eval row12085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12085, Integer.Sparse.eval_collectBalanced, rawRowCheck12085]

theorem rawRowCheck12086 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17 = rawRow12086 := by decide +kernel

theorem rowCheck12086 : row12086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12086 := by decide +kernel

theorem rowEval12086 (x : Key → ℝ) : Integer.Sparse.eval row12086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12086, Integer.Sparse.eval_collectBalanced, rawRowCheck12086]

theorem rawRowCheck12087 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17 = rawRow12087 := by decide +kernel

theorem rowCheck12087 : row12087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12087 := by decide +kernel

theorem rowEval12087 (x : Key → ℝ) : Integer.Sparse.eval row12087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12087, Integer.Sparse.eval_collectBalanced, rawRowCheck12087]

theorem rawRowCheck12088 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17 = rawRow12088 := by decide +kernel

theorem rowCheck12088 : row12088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12088 := by decide +kernel

theorem rowEval12088 (x : Key → ℝ) : Integer.Sparse.eval row12088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12088, Integer.Sparse.eval_collectBalanced, rawRowCheck12088]

theorem rawRowCheck12089 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17 = rawRow12089 := by decide +kernel

theorem rowCheck12089 : row12089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12089 := by decide +kernel

theorem rowEval12089 (x : Key → ℝ) : Integer.Sparse.eval row12089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12089, Integer.Sparse.eval_collectBalanced, rawRowCheck12089]

theorem rawRowCheck12090 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17 = rawRow12090 := by decide +kernel

theorem rowCheck12090 : row12090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12090 := by decide +kernel

theorem rowEval12090 (x : Key → ℝ) : Integer.Sparse.eval row12090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12090, Integer.Sparse.eval_collectBalanced, rawRowCheck12090]

theorem rawRowCheck12091 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17 = rawRow12091 := by decide +kernel

theorem rowCheck12091 : row12091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12091 := by decide +kernel

theorem rowEval12091 (x : Key → ℝ) : Integer.Sparse.eval row12091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12091, Integer.Sparse.eval_collectBalanced, rawRowCheck12091]

theorem rawRowCheck12092 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17 = rawRow12092 := by decide +kernel

theorem rowCheck12092 : row12092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12092 := by decide +kernel

theorem rowEval12092 (x : Key → ℝ) : Integer.Sparse.eval row12092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12092, Integer.Sparse.eval_collectBalanced, rawRowCheck12092]

theorem rawRowCheck12093 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17 = rawRow12093 := by decide +kernel

theorem rowCheck12093 : row12093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12093 := by decide +kernel

theorem rowEval12093 (x : Key → ℝ) : Integer.Sparse.eval row12093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12093, Integer.Sparse.eval_collectBalanced, rawRowCheck12093]

theorem rawRowCheck12094 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17 = rawRow12094 := by decide +kernel

theorem rowCheck12094 : row12094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12094 := by decide +kernel

theorem rowEval12094 (x : Key → ℝ) : Integer.Sparse.eval row12094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12094, Integer.Sparse.eval_collectBalanced, rawRowCheck12094]

theorem rawRowCheck12095 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17 = rawRow12095 := by decide +kernel

theorem rowCheck12095 : row12095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12095 := by decide +kernel

theorem rowEval12095 (x : Key → ℝ) : Integer.Sparse.eval row12095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12095, Integer.Sparse.eval_collectBalanced, rawRowCheck12095]

theorem rawRowCheck12096 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17 = rawRow12096 := by decide +kernel

theorem rowCheck12096 : row12096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12096 := by decide +kernel

theorem rowEval12096 (x : Key → ℝ) : Integer.Sparse.eval row12096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12096, Integer.Sparse.eval_collectBalanced, rawRowCheck12096]

theorem rawRowCheck12097 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17 = rawRow12097 := by decide +kernel

theorem rowCheck12097 : row12097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12097 := by decide +kernel

theorem rowEval12097 (x : Key → ℝ) : Integer.Sparse.eval row12097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12097, Integer.Sparse.eval_collectBalanced, rawRowCheck12097]

theorem rawRowCheck12098 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form18 = rawRow12098 := by decide +kernel

theorem rowCheck12098 : row12098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12098 := by decide +kernel

theorem rowEval12098 (x : Key → ℝ) : Integer.Sparse.eval row12098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12098, Integer.Sparse.eval_collectBalanced, rawRowCheck12098]

theorem rawRowCheck12099 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form18 = rawRow12099 := by decide +kernel

theorem rowCheck12099 : row12099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12099 := by decide +kernel

theorem rowEval12099 (x : Key → ℝ) : Integer.Sparse.eval row12099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12099, Integer.Sparse.eval_collectBalanced, rawRowCheck12099]

theorem rawRowCheck12100 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form18 = rawRow12100 := by decide +kernel

theorem rowCheck12100 : row12100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12100 := by decide +kernel

theorem rowEval12100 (x : Key → ℝ) : Integer.Sparse.eval row12100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12100, Integer.Sparse.eval_collectBalanced, rawRowCheck12100]

theorem rawRowCheck12101 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form18 = rawRow12101 := by decide +kernel

theorem rowCheck12101 : row12101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12101 := by decide +kernel

theorem rowEval12101 (x : Key → ℝ) : Integer.Sparse.eval row12101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12101, Integer.Sparse.eval_collectBalanced, rawRowCheck12101]

theorem rawRowCheck12102 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form18 = rawRow12102 := by decide +kernel

theorem rowCheck12102 : row12102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12102 := by decide +kernel

theorem rowEval12102 (x : Key → ℝ) : Integer.Sparse.eval row12102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12102, Integer.Sparse.eval_collectBalanced, rawRowCheck12102]

theorem rawRowCheck12103 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form18 = rawRow12103 := by decide +kernel

theorem rowCheck12103 : row12103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12103 := by decide +kernel

theorem rowEval12103 (x : Key → ℝ) : Integer.Sparse.eval row12103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12103, Integer.Sparse.eval_collectBalanced, rawRowCheck12103]

theorem rawRowCheck12104 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form18 = rawRow12104 := by decide +kernel

theorem rowCheck12104 : row12104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12104 := by decide +kernel

theorem rowEval12104 (x : Key → ℝ) : Integer.Sparse.eval row12104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12104, Integer.Sparse.eval_collectBalanced, rawRowCheck12104]

theorem rawRowCheck12105 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form18 = rawRow12105 := by decide +kernel

theorem rowCheck12105 : row12105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12105 := by decide +kernel

theorem rowEval12105 (x : Key → ℝ) : Integer.Sparse.eval row12105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12105, Integer.Sparse.eval_collectBalanced, rawRowCheck12105]

theorem rawRowCheck12106 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form18 = rawRow12106 := by decide +kernel

theorem rowCheck12106 : row12106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12106 := by decide +kernel

theorem rowEval12106 (x : Key → ℝ) : Integer.Sparse.eval row12106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12106, Integer.Sparse.eval_collectBalanced, rawRowCheck12106]

theorem rawRowCheck12107 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form18 = rawRow12107 := by decide +kernel

theorem rowCheck12107 : row12107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12107 := by decide +kernel

theorem rowEval12107 (x : Key → ℝ) : Integer.Sparse.eval row12107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12107, Integer.Sparse.eval_collectBalanced, rawRowCheck12107]

theorem rawRowCheck12108 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form18 = rawRow12108 := by decide +kernel

theorem rowCheck12108 : row12108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12108 := by decide +kernel

theorem rowEval12108 (x : Key → ℝ) : Integer.Sparse.eval row12108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12108, Integer.Sparse.eval_collectBalanced, rawRowCheck12108]

theorem rawRowCheck12109 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form18 = rawRow12109 := by decide +kernel

theorem rowCheck12109 : row12109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12109 := by decide +kernel

theorem rowEval12109 (x : Key → ℝ) : Integer.Sparse.eval row12109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12109, Integer.Sparse.eval_collectBalanced, rawRowCheck12109]

theorem rawRowCheck12110 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form18 = rawRow12110 := by decide +kernel

theorem rowCheck12110 : row12110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12110 := by decide +kernel

theorem rowEval12110 (x : Key → ℝ) : Integer.Sparse.eval row12110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12110, Integer.Sparse.eval_collectBalanced, rawRowCheck12110]

theorem rawRowCheck12111 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form18 = rawRow12111 := by decide +kernel

theorem rowCheck12111 : row12111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12111 := by decide +kernel

theorem rowEval12111 (x : Key → ℝ) : Integer.Sparse.eval row12111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12111, Integer.Sparse.eval_collectBalanced, rawRowCheck12111]

theorem rawRowCheck12112 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form18 = rawRow12112 := by decide +kernel

theorem rowCheck12112 : row12112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12112 := by decide +kernel

theorem rowEval12112 (x : Key → ℝ) : Integer.Sparse.eval row12112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12112, Integer.Sparse.eval_collectBalanced, rawRowCheck12112]

theorem rawRowCheck12113 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form18 = rawRow12113 := by decide +kernel

theorem rowCheck12113 : row12113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12113 := by decide +kernel

theorem rowEval12113 (x : Key → ℝ) : Integer.Sparse.eval row12113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12113, Integer.Sparse.eval_collectBalanced, rawRowCheck12113]

theorem rawRowCheck12114 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form18 = rawRow12114 := by decide +kernel

theorem rowCheck12114 : row12114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12114 := by decide +kernel

theorem rowEval12114 (x : Key → ℝ) : Integer.Sparse.eval row12114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12114, Integer.Sparse.eval_collectBalanced, rawRowCheck12114]

theorem rawRowCheck12115 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form18 = rawRow12115 := by decide +kernel

theorem rowCheck12115 : row12115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12115 := by decide +kernel

theorem rowEval12115 (x : Key → ℝ) : Integer.Sparse.eval row12115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12115, Integer.Sparse.eval_collectBalanced, rawRowCheck12115]

theorem rawRowCheck12116 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form19 = rawRow12116 := by decide +kernel

theorem rowCheck12116 : row12116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12116 := by decide +kernel

theorem rowEval12116 (x : Key → ℝ) : Integer.Sparse.eval row12116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12116, Integer.Sparse.eval_collectBalanced, rawRowCheck12116]

theorem rawRowCheck12117 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form19 = rawRow12117 := by decide +kernel

theorem rowCheck12117 : row12117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12117 := by decide +kernel

theorem rowEval12117 (x : Key → ℝ) : Integer.Sparse.eval row12117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12117, Integer.Sparse.eval_collectBalanced, rawRowCheck12117]

theorem rawRowCheck12118 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form19 = rawRow12118 := by decide +kernel

theorem rowCheck12118 : row12118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12118 := by decide +kernel

theorem rowEval12118 (x : Key → ℝ) : Integer.Sparse.eval row12118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12118, Integer.Sparse.eval_collectBalanced, rawRowCheck12118]

theorem rawRowCheck12119 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form19 = rawRow12119 := by decide +kernel

theorem rowCheck12119 : row12119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12119 := by decide +kernel

theorem rowEval12119 (x : Key → ℝ) : Integer.Sparse.eval row12119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12119, Integer.Sparse.eval_collectBalanced, rawRowCheck12119]

theorem rawRowCheck12120 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form19 = rawRow12120 := by decide +kernel

theorem rowCheck12120 : row12120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12120 := by decide +kernel

theorem rowEval12120 (x : Key → ℝ) : Integer.Sparse.eval row12120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12120, Integer.Sparse.eval_collectBalanced, rawRowCheck12120]

theorem rawRowCheck12121 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form19 = rawRow12121 := by decide +kernel

theorem rowCheck12121 : row12121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12121 := by decide +kernel

theorem rowEval12121 (x : Key → ℝ) : Integer.Sparse.eval row12121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12121, Integer.Sparse.eval_collectBalanced, rawRowCheck12121]

theorem rawRowCheck12122 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form19 = rawRow12122 := by decide +kernel

theorem rowCheck12122 : row12122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12122 := by decide +kernel

theorem rowEval12122 (x : Key → ℝ) : Integer.Sparse.eval row12122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12122, Integer.Sparse.eval_collectBalanced, rawRowCheck12122]

theorem rawRowCheck12123 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form19 = rawRow12123 := by decide +kernel

theorem rowCheck12123 : row12123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12123 := by decide +kernel

theorem rowEval12123 (x : Key → ℝ) : Integer.Sparse.eval row12123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12123, Integer.Sparse.eval_collectBalanced, rawRowCheck12123]

theorem rawRowCheck12124 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form19 = rawRow12124 := by decide +kernel

theorem rowCheck12124 : row12124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12124 := by decide +kernel

theorem rowEval12124 (x : Key → ℝ) : Integer.Sparse.eval row12124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12124, Integer.Sparse.eval_collectBalanced, rawRowCheck12124]

theorem rawRowCheck12125 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form19 = rawRow12125 := by decide +kernel

theorem rowCheck12125 : row12125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12125 := by decide +kernel

theorem rowEval12125 (x : Key → ℝ) : Integer.Sparse.eval row12125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12125, Integer.Sparse.eval_collectBalanced, rawRowCheck12125]

theorem rawRowCheck12126 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form19 = rawRow12126 := by decide +kernel

theorem rowCheck12126 : row12126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12126 := by decide +kernel

theorem rowEval12126 (x : Key → ℝ) : Integer.Sparse.eval row12126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12126, Integer.Sparse.eval_collectBalanced, rawRowCheck12126]

theorem rawRowCheck12127 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form19 = rawRow12127 := by decide +kernel

theorem rowCheck12127 : row12127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12127 := by decide +kernel

theorem rowEval12127 (x : Key → ℝ) : Integer.Sparse.eval row12127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12127, Integer.Sparse.eval_collectBalanced, rawRowCheck12127]

theorem rawRowCheck12128 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form19 = rawRow12128 := by decide +kernel

theorem rowCheck12128 : row12128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12128 := by decide +kernel

theorem rowEval12128 (x : Key → ℝ) : Integer.Sparse.eval row12128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12128, Integer.Sparse.eval_collectBalanced, rawRowCheck12128]

theorem rawRowCheck12129 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form19 = rawRow12129 := by decide +kernel

theorem rowCheck12129 : row12129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12129 := by decide +kernel

theorem rowEval12129 (x : Key → ℝ) : Integer.Sparse.eval row12129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12129, Integer.Sparse.eval_collectBalanced, rawRowCheck12129]

theorem rawRowCheck12130 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form19 = rawRow12130 := by decide +kernel

theorem rowCheck12130 : row12130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12130 := by decide +kernel

theorem rowEval12130 (x : Key → ℝ) : Integer.Sparse.eval row12130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12130, Integer.Sparse.eval_collectBalanced, rawRowCheck12130]

theorem rawRowCheck12131 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form19 = rawRow12131 := by decide +kernel

theorem rowCheck12131 : row12131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12131 := by decide +kernel

theorem rowEval12131 (x : Key → ℝ) : Integer.Sparse.eval row12131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12131, Integer.Sparse.eval_collectBalanced, rawRowCheck12131]

theorem rawRowCheck12132 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form19 = rawRow12132 := by decide +kernel

theorem rowCheck12132 : row12132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12132 := by decide +kernel

theorem rowEval12132 (x : Key → ℝ) : Integer.Sparse.eval row12132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12132, Integer.Sparse.eval_collectBalanced, rawRowCheck12132]

theorem rawRowCheck12133 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form19 = rawRow12133 := by decide +kernel

theorem rowCheck12133 : row12133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12133 := by decide +kernel

theorem rowEval12133 (x : Key → ℝ) : Integer.Sparse.eval row12133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12133, Integer.Sparse.eval_collectBalanced, rawRowCheck12133]

theorem rawRowCheck12134 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form20 = rawRow12134 := by decide +kernel

theorem rowCheck12134 : row12134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12134 := by decide +kernel

theorem rowEval12134 (x : Key → ℝ) : Integer.Sparse.eval row12134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12134, Integer.Sparse.eval_collectBalanced, rawRowCheck12134]

theorem rawRowCheck12135 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form20 = rawRow12135 := by decide +kernel

theorem rowCheck12135 : row12135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12135 := by decide +kernel

theorem rowEval12135 (x : Key → ℝ) : Integer.Sparse.eval row12135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12135, Integer.Sparse.eval_collectBalanced, rawRowCheck12135]

theorem rawRowCheck12136 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form20 = rawRow12136 := by decide +kernel

theorem rowCheck12136 : row12136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12136 := by decide +kernel

theorem rowEval12136 (x : Key → ℝ) : Integer.Sparse.eval row12136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12136, Integer.Sparse.eval_collectBalanced, rawRowCheck12136]

theorem rawRowCheck12137 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form20 = rawRow12137 := by decide +kernel

theorem rowCheck12137 : row12137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12137 := by decide +kernel

theorem rowEval12137 (x : Key → ℝ) : Integer.Sparse.eval row12137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12137, Integer.Sparse.eval_collectBalanced, rawRowCheck12137]

theorem rawRowCheck12138 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form20 = rawRow12138 := by decide +kernel

theorem rowCheck12138 : row12138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12138 := by decide +kernel

theorem rowEval12138 (x : Key → ℝ) : Integer.Sparse.eval row12138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12138, Integer.Sparse.eval_collectBalanced, rawRowCheck12138]

theorem rawRowCheck12139 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form20 = rawRow12139 := by decide +kernel

theorem rowCheck12139 : row12139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12139 := by decide +kernel

theorem rowEval12139 (x : Key → ℝ) : Integer.Sparse.eval row12139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12139, Integer.Sparse.eval_collectBalanced, rawRowCheck12139]

theorem rawRowCheck12140 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form20 = rawRow12140 := by decide +kernel

theorem rowCheck12140 : row12140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12140 := by decide +kernel

theorem rowEval12140 (x : Key → ℝ) : Integer.Sparse.eval row12140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12140, Integer.Sparse.eval_collectBalanced, rawRowCheck12140]

theorem rawRowCheck12141 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form20 = rawRow12141 := by decide +kernel

theorem rowCheck12141 : row12141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12141 := by decide +kernel

theorem rowEval12141 (x : Key → ℝ) : Integer.Sparse.eval row12141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12141, Integer.Sparse.eval_collectBalanced, rawRowCheck12141]

theorem rawRowCheck12142 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form20 = rawRow12142 := by decide +kernel

theorem rowCheck12142 : row12142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12142 := by decide +kernel

theorem rowEval12142 (x : Key → ℝ) : Integer.Sparse.eval row12142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12142, Integer.Sparse.eval_collectBalanced, rawRowCheck12142]

theorem rawRowCheck12143 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form20 = rawRow12143 := by decide +kernel

theorem rowCheck12143 : row12143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12143 := by decide +kernel

theorem rowEval12143 (x : Key → ℝ) : Integer.Sparse.eval row12143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12143, Integer.Sparse.eval_collectBalanced, rawRowCheck12143]

theorem rawRowCheck12144 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form20 = rawRow12144 := by decide +kernel

theorem rowCheck12144 : row12144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12144 := by decide +kernel

theorem rowEval12144 (x : Key → ℝ) : Integer.Sparse.eval row12144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12144, Integer.Sparse.eval_collectBalanced, rawRowCheck12144]

theorem rawRowCheck12145 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form20 = rawRow12145 := by decide +kernel

theorem rowCheck12145 : row12145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12145 := by decide +kernel

theorem rowEval12145 (x : Key → ℝ) : Integer.Sparse.eval row12145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12145, Integer.Sparse.eval_collectBalanced, rawRowCheck12145]

theorem rawRowCheck12146 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form20 = rawRow12146 := by decide +kernel

theorem rowCheck12146 : row12146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12146 := by decide +kernel

theorem rowEval12146 (x : Key → ℝ) : Integer.Sparse.eval row12146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12146, Integer.Sparse.eval_collectBalanced, rawRowCheck12146]

theorem rawRowCheck12147 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form20 = rawRow12147 := by decide +kernel

theorem rowCheck12147 : row12147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12147 := by decide +kernel

theorem rowEval12147 (x : Key → ℝ) : Integer.Sparse.eval row12147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12147, Integer.Sparse.eval_collectBalanced, rawRowCheck12147]

theorem rawRowCheck12148 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form20 = rawRow12148 := by decide +kernel

theorem rowCheck12148 : row12148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12148 := by decide +kernel

theorem rowEval12148 (x : Key → ℝ) : Integer.Sparse.eval row12148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12148, Integer.Sparse.eval_collectBalanced, rawRowCheck12148]

theorem rawRowCheck12149 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form20 = rawRow12149 := by decide +kernel

theorem rowCheck12149 : row12149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12149 := by decide +kernel

theorem rowEval12149 (x : Key → ℝ) : Integer.Sparse.eval row12149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12149, Integer.Sparse.eval_collectBalanced, rawRowCheck12149]

theorem rawRowCheck12150 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form20 = rawRow12150 := by decide +kernel

theorem rowCheck12150 : row12150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12150 := by decide +kernel

theorem rowEval12150 (x : Key → ℝ) : Integer.Sparse.eval row12150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12150, Integer.Sparse.eval_collectBalanced, rawRowCheck12150]

theorem rawRowCheck12151 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form20 = rawRow12151 := by decide +kernel

theorem rowCheck12151 : row12151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12151 := by decide +kernel

theorem rowEval12151 (x : Key → ℝ) : Integer.Sparse.eval row12151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12151, Integer.Sparse.eval_collectBalanced, rawRowCheck12151]

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

theorem rawRowCheck12188 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form23 = rawRow12188 := by decide +kernel

theorem rowCheck12188 : row12188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12188 := by decide +kernel

theorem rowEval12188 (x : Key → ℝ) : Integer.Sparse.eval row12188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12188, Integer.Sparse.eval_collectBalanced, rawRowCheck12188]

theorem rawRowCheck12189 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form23 = rawRow12189 := by decide +kernel

theorem rowCheck12189 : row12189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12189 := by decide +kernel

theorem rowEval12189 (x : Key → ℝ) : Integer.Sparse.eval row12189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12189, Integer.Sparse.eval_collectBalanced, rawRowCheck12189]

theorem rawRowCheck12190 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form23 = rawRow12190 := by decide +kernel

theorem rowCheck12190 : row12190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12190 := by decide +kernel

theorem rowEval12190 (x : Key → ℝ) : Integer.Sparse.eval row12190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12190, Integer.Sparse.eval_collectBalanced, rawRowCheck12190]

theorem rawRowCheck12191 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form23 = rawRow12191 := by decide +kernel

theorem rowCheck12191 : row12191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12191 := by decide +kernel

theorem rowEval12191 (x : Key → ℝ) : Integer.Sparse.eval row12191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12191, Integer.Sparse.eval_collectBalanced, rawRowCheck12191]

theorem rawRowCheck12192 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form23 = rawRow12192 := by decide +kernel

theorem rowCheck12192 : row12192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12192 := by decide +kernel

theorem rowEval12192 (x : Key → ℝ) : Integer.Sparse.eval row12192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12192, Integer.Sparse.eval_collectBalanced, rawRowCheck12192]

theorem rawRowCheck12193 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form23 = rawRow12193 := by decide +kernel

theorem rowCheck12193 : row12193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12193 := by decide +kernel

theorem rowEval12193 (x : Key → ℝ) : Integer.Sparse.eval row12193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12193, Integer.Sparse.eval_collectBalanced, rawRowCheck12193]

theorem rawRowCheck12194 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form23 = rawRow12194 := by decide +kernel

theorem rowCheck12194 : row12194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12194 := by decide +kernel

theorem rowEval12194 (x : Key → ℝ) : Integer.Sparse.eval row12194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12194, Integer.Sparse.eval_collectBalanced, rawRowCheck12194]

theorem rawRowCheck12195 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form23 = rawRow12195 := by decide +kernel

theorem rowCheck12195 : row12195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12195 := by decide +kernel

theorem rowEval12195 (x : Key → ℝ) : Integer.Sparse.eval row12195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12195, Integer.Sparse.eval_collectBalanced, rawRowCheck12195]

theorem rawRowCheck12196 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form23 = rawRow12196 := by decide +kernel

theorem rowCheck12196 : row12196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12196 := by decide +kernel

theorem rowEval12196 (x : Key → ℝ) : Integer.Sparse.eval row12196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12196, Integer.Sparse.eval_collectBalanced, rawRowCheck12196]

theorem rawRowCheck12197 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form23 = rawRow12197 := by decide +kernel

theorem rowCheck12197 : row12197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12197 := by decide +kernel

theorem rowEval12197 (x : Key → ℝ) : Integer.Sparse.eval row12197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12197, Integer.Sparse.eval_collectBalanced, rawRowCheck12197]

theorem rawRowCheck12198 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form23 = rawRow12198 := by decide +kernel

theorem rowCheck12198 : row12198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12198 := by decide +kernel

theorem rowEval12198 (x : Key → ℝ) : Integer.Sparse.eval row12198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12198, Integer.Sparse.eval_collectBalanced, rawRowCheck12198]

theorem rawRowCheck12199 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form23 = rawRow12199 := by decide +kernel

theorem rowCheck12199 : row12199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12199 := by decide +kernel

theorem rowEval12199 (x : Key → ℝ) : Integer.Sparse.eval row12199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form23) x := by
  rw [rowCheck12199, Integer.Sparse.eval_collectBalanced, rawRowCheck12199]

theorem rawRowCheck12200 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form23 = rawRow12200 := by decide +kernel

theorem rowCheck12200 : row12200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12200 := by decide +kernel

theorem rowEval12200 (x : Key → ℝ) : Integer.Sparse.eval row12200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12200, Integer.Sparse.eval_collectBalanced, rawRowCheck12200]

theorem rawRowCheck12201 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form23 = rawRow12201 := by decide +kernel

theorem rowCheck12201 : row12201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12201 := by decide +kernel

theorem rowEval12201 (x : Key → ℝ) : Integer.Sparse.eval row12201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12201, Integer.Sparse.eval_collectBalanced, rawRowCheck12201]

theorem rawRowCheck12202 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form23 = rawRow12202 := by decide +kernel

theorem rowCheck12202 : row12202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12202 := by decide +kernel

theorem rowEval12202 (x : Key → ℝ) : Integer.Sparse.eval row12202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12202, Integer.Sparse.eval_collectBalanced, rawRowCheck12202]

theorem rawRowCheck12203 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form23 = rawRow12203 := by decide +kernel

theorem rowCheck12203 : row12203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12203 := by decide +kernel

theorem rowEval12203 (x : Key → ℝ) : Integer.Sparse.eval row12203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form23) x := by
  rw [rowCheck12203, Integer.Sparse.eval_collectBalanced, rawRowCheck12203]

theorem rawRowCheck12204 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form23 = rawRow12204 := by decide +kernel

theorem rowCheck12204 : row12204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12204 := by decide +kernel

theorem rowEval12204 (x : Key → ℝ) : Integer.Sparse.eval row12204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12204, Integer.Sparse.eval_collectBalanced, rawRowCheck12204]

theorem rawRowCheck12205 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form23 = rawRow12205 := by decide +kernel

theorem rowCheck12205 : row12205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12205 := by decide +kernel

theorem rowEval12205 (x : Key → ℝ) : Integer.Sparse.eval row12205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form23) x := by
  rw [rowCheck12205, Integer.Sparse.eval_collectBalanced, rawRowCheck12205]

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

theorem entryCheck23_1 : entry23_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_1 k)) := by decide +kernel

theorem rowsSound23_1 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval11792 x
  · exact rowEval11793 x
  · exact rowEval11794 x
  · exact rowEval11795 x
  · exact rowEval11796 x
  · exact rowEval11797 x
  · exact rowEval11798 x
  · exact rowEval11799 x
  · exact rowEval11800 x
  · exact rowEval11801 x
  · exact rowEval11802 x
  · exact rowEval11803 x
  · exact rowEval11804 x
  · exact rowEval11805 x
  · exact rowEval11806 x
  · exact rowEval11807 x
  · exact rowEval11808 x
  · exact rowEval11809 x

theorem entryEval23_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_1 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck23_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_1]

theorem entryCheck23_2 : entry23_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_2 k)) := by decide +kernel

theorem rowsSound23_2 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval11810 x
  · exact rowEval11811 x
  · exact rowEval11812 x
  · exact rowEval11813 x
  · exact rowEval11814 x
  · exact rowEval11815 x
  · exact rowEval11816 x
  · exact rowEval11817 x
  · exact rowEval11818 x
  · exact rowEval11819 x
  · exact rowEval11820 x
  · exact rowEval11821 x
  · exact rowEval11822 x
  · exact rowEval11823 x
  · exact rowEval11824 x
  · exact rowEval11825 x
  · exact rowEval11826 x
  · exact rowEval11827 x

theorem entryEval23_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_2 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck23_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_2]

theorem entryCheck23_3 : entry23_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_3 k)) := by decide +kernel

theorem rowsSound23_3 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval11828 x
  · exact rowEval11829 x
  · exact rowEval11830 x
  · exact rowEval11831 x
  · exact rowEval11832 x
  · exact rowEval11833 x
  · exact rowEval11834 x
  · exact rowEval11835 x
  · exact rowEval11836 x
  · exact rowEval11837 x
  · exact rowEval11838 x
  · exact rowEval11839 x
  · exact rowEval11840 x
  · exact rowEval11841 x
  · exact rowEval11842 x
  · exact rowEval11843 x
  · exact rowEval11844 x
  · exact rowEval11845 x

theorem entryEval23_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_3 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck23_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_3]

theorem entryCheck23_4 : entry23_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_4 k)) := by decide +kernel

theorem rowsSound23_4 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval11846 x
  · exact rowEval11847 x
  · exact rowEval11848 x
  · exact rowEval11849 x
  · exact rowEval11850 x
  · exact rowEval11851 x
  · exact rowEval11852 x
  · exact rowEval11853 x
  · exact rowEval11854 x
  · exact rowEval11855 x
  · exact rowEval11856 x
  · exact rowEval11857 x
  · exact rowEval11858 x
  · exact rowEval11859 x
  · exact rowEval11860 x
  · exact rowEval11861 x
  · exact rowEval11862 x
  · exact rowEval11863 x

theorem entryEval23_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_4 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck23_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_4]

theorem entryCheck23_6 : entry23_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_6 k)) := by decide +kernel

theorem rowsSound23_6 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval11882 x
  · exact rowEval11883 x
  · exact rowEval11884 x
  · exact rowEval11885 x
  · exact rowEval11886 x
  · exact rowEval11887 x
  · exact rowEval11888 x
  · exact rowEval11889 x
  · exact rowEval11890 x
  · exact rowEval11891 x
  · exact rowEval11892 x
  · exact rowEval11893 x
  · exact rowEval11894 x
  · exact rowEval11895 x
  · exact rowEval11896 x
  · exact rowEval11897 x
  · exact rowEval11898 x
  · exact rowEval11899 x

theorem entryEval23_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_6 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck23_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_6]

theorem entryCheck23_10 : entry23_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_10 k)) := by decide +kernel

theorem rowsSound23_10 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval11954 x
  · exact rowEval11955 x
  · exact rowEval11956 x
  · exact rowEval11957 x
  · exact rowEval11958 x
  · exact rowEval11959 x
  · exact rowEval11960 x
  · exact rowEval11961 x
  · exact rowEval11962 x
  · exact rowEval11963 x
  · exact rowEval11964 x
  · exact rowEval11965 x
  · exact rowEval11966 x
  · exact rowEval11967 x
  · exact rowEval11968 x
  · exact rowEval11969 x
  · exact rowEval11970 x
  · exact rowEval11971 x

theorem entryEval23_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_10 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck23_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_10]

theorem entryCheck23_11 : entry23_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_11 k)) := by decide +kernel

theorem rowsSound23_11 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval11972 x
  · exact rowEval11973 x
  · exact rowEval11974 x
  · exact rowEval11975 x
  · exact rowEval11976 x
  · exact rowEval11977 x
  · exact rowEval11978 x
  · exact rowEval11979 x
  · exact rowEval11980 x
  · exact rowEval11981 x
  · exact rowEval11982 x
  · exact rowEval11983 x
  · exact rowEval11984 x
  · exact rowEval11985 x
  · exact rowEval11986 x
  · exact rowEval11987 x
  · exact rowEval11988 x
  · exact rowEval11989 x

theorem entryEval23_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_11 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck23_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_11]

theorem entryCheck23_12 : entry23_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_12 k)) := by decide +kernel

theorem rowsSound23_12 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval11990 x
  · exact rowEval11991 x
  · exact rowEval11992 x
  · exact rowEval11993 x
  · exact rowEval11994 x
  · exact rowEval11995 x
  · exact rowEval11996 x
  · exact rowEval11997 x
  · exact rowEval11998 x
  · exact rowEval11999 x
  · exact rowEval12000 x
  · exact rowEval12001 x
  · exact rowEval12002 x
  · exact rowEval12003 x
  · exact rowEval12004 x
  · exact rowEval12005 x
  · exact rowEval12006 x
  · exact rowEval12007 x

theorem entryEval23_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_12 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck23_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_12]

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

theorem entryCheck23_14 : entry23_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_14 k)) := by decide +kernel

theorem rowsSound23_14 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12026 x
  · exact rowEval12027 x
  · exact rowEval12028 x
  · exact rowEval12029 x
  · exact rowEval12030 x
  · exact rowEval12031 x
  · exact rowEval12032 x
  · exact rowEval12033 x
  · exact rowEval12034 x
  · exact rowEval12035 x
  · exact rowEval12036 x
  · exact rowEval12037 x
  · exact rowEval12038 x
  · exact rowEval12039 x
  · exact rowEval12040 x
  · exact rowEval12041 x
  · exact rowEval12042 x
  · exact rowEval12043 x

theorem entryEval23_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_14 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck23_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_14]

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

theorem entryCheck23_16 : entry23_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_16 k)) := by decide +kernel

theorem rowsSound23_16 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12062 x
  · exact rowEval12063 x
  · exact rowEval12064 x
  · exact rowEval12065 x
  · exact rowEval12066 x
  · exact rowEval12067 x
  · exact rowEval12068 x
  · exact rowEval12069 x
  · exact rowEval12070 x
  · exact rowEval12071 x
  · exact rowEval12072 x
  · exact rowEval12073 x
  · exact rowEval12074 x
  · exact rowEval12075 x
  · exact rowEval12076 x
  · exact rowEval12077 x
  · exact rowEval12078 x
  · exact rowEval12079 x

theorem entryEval23_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_16 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck23_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_16]

theorem entryCheck23_17 : entry23_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_17 k)) := by decide +kernel

theorem rowsSound23_17 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12080 x
  · exact rowEval12081 x
  · exact rowEval12082 x
  · exact rowEval12083 x
  · exact rowEval12084 x
  · exact rowEval12085 x
  · exact rowEval12086 x
  · exact rowEval12087 x
  · exact rowEval12088 x
  · exact rowEval12089 x
  · exact rowEval12090 x
  · exact rowEval12091 x
  · exact rowEval12092 x
  · exact rowEval12093 x
  · exact rowEval12094 x
  · exact rowEval12095 x
  · exact rowEval12096 x
  · exact rowEval12097 x

theorem entryEval23_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_17 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck23_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_17]

theorem entryCheck23_18 : entry23_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_18 k)) := by decide +kernel

theorem rowsSound23_18 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12098 x
  · exact rowEval12099 x
  · exact rowEval12100 x
  · exact rowEval12101 x
  · exact rowEval12102 x
  · exact rowEval12103 x
  · exact rowEval12104 x
  · exact rowEval12105 x
  · exact rowEval12106 x
  · exact rowEval12107 x
  · exact rowEval12108 x
  · exact rowEval12109 x
  · exact rowEval12110 x
  · exact rowEval12111 x
  · exact rowEval12112 x
  · exact rowEval12113 x
  · exact rowEval12114 x
  · exact rowEval12115 x

theorem entryEval23_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_18 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck23_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_18]

theorem entryCheck23_19 : entry23_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_19 k)) := by decide +kernel

theorem rowsSound23_19 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12116 x
  · exact rowEval12117 x
  · exact rowEval12118 x
  · exact rowEval12119 x
  · exact rowEval12120 x
  · exact rowEval12121 x
  · exact rowEval12122 x
  · exact rowEval12123 x
  · exact rowEval12124 x
  · exact rowEval12125 x
  · exact rowEval12126 x
  · exact rowEval12127 x
  · exact rowEval12128 x
  · exact rowEval12129 x
  · exact rowEval12130 x
  · exact rowEval12131 x
  · exact rowEval12132 x
  · exact rowEval12133 x

theorem entryEval23_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_19 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck23_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_19]

theorem entryCheck23_20 : entry23_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_20 k)) := by decide +kernel

theorem rowsSound23_20 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval12134 x
  · exact rowEval12135 x
  · exact rowEval12136 x
  · exact rowEval12137 x
  · exact rowEval12138 x
  · exact rowEval12139 x
  · exact rowEval12140 x
  · exact rowEval12141 x
  · exact rowEval12142 x
  · exact rowEval12143 x
  · exact rowEval12144 x
  · exact rowEval12145 x
  · exact rowEval12146 x
  · exact rowEval12147 x
  · exact rowEval12148 x
  · exact rowEval12149 x
  · exact rowEval12150 x
  · exact rowEval12151 x

theorem entryEval23_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_20 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck23_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_20]

theorem entryCheck23_23 : entry23_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_23 k)) := by decide +kernel

theorem rowsSound23_23 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval12188 x
  · exact rowEval12189 x
  · exact rowEval12190 x
  · exact rowEval12191 x
  · exact rowEval12192 x
  · exact rowEval12193 x
  · exact rowEval12194 x
  · exact rowEval12195 x
  · exact rowEval12196 x
  · exact rowEval12197 x
  · exact rowEval12198 x
  · exact rowEval12199 x
  · exact rowEval12200 x
  · exact rowEval12201 x
  · exact rowEval12202 x
  · exact rowEval12203 x
  · exact rowEval12204 x
  · exact rowEval12205 x

theorem entryEval23_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_23 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck23_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_23]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12321 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form23 = rawRow12321 := by decide +kernel

theorem rowCheck12321 : row12321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12321 := by decide +kernel

theorem rowEval12321 (x : Key → ℝ) : Integer.Sparse.eval row12321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12321, Integer.Sparse.eval_collectBalanced, rawRowCheck12321]

theorem rawRowCheck12322 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form23 = rawRow12322 := by decide +kernel

theorem rowCheck12322 : row12322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12322 := by decide +kernel

theorem rowEval12322 (x : Key → ℝ) : Integer.Sparse.eval row12322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12322, Integer.Sparse.eval_collectBalanced, rawRowCheck12322]

theorem rawRowCheck12323 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form23 = rawRow12323 := by decide +kernel

theorem rowCheck12323 : row12323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12323 := by decide +kernel

theorem rowEval12323 (x : Key → ℝ) : Integer.Sparse.eval row12323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12323, Integer.Sparse.eval_collectBalanced, rawRowCheck12323]

theorem rawRowCheck12324 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form23 = rawRow12324 := by decide +kernel

theorem rowCheck12324 : row12324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12324 := by decide +kernel

theorem rowEval12324 (x : Key → ℝ) : Integer.Sparse.eval row12324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12324, Integer.Sparse.eval_collectBalanced, rawRowCheck12324]

theorem rawRowCheck12325 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form23 = rawRow12325 := by decide +kernel

theorem rowCheck12325 : row12325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12325 := by decide +kernel

theorem rowEval12325 (x : Key → ℝ) : Integer.Sparse.eval row12325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck12325, Integer.Sparse.eval_collectBalanced, rawRowCheck12325]

end MUB6.Certificate.GramRows

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

theorem entryCheck24_23 : entry24_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_23 k)) := by decide +kernel

theorem rowsSound24_23 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval12321 x
  · exact rowEval12322 x
  · exact rowEval12323 x
  · exact rowEval12324 x
  · exact rowEval12325 x

theorem entryEval24_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_23 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck24_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_23]

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

theorem rawRowCheck12515 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form23 = rawRow12515 := by decide +kernel

theorem rowCheck12515 : row12515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12515 := by decide +kernel

theorem rowEval12515 (x : Key → ℝ) : Integer.Sparse.eval row12515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12515, Integer.Sparse.eval_collectBalanced, rawRowCheck12515]

theorem rawRowCheck12516 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form23 = rawRow12516 := by decide +kernel

theorem rowCheck12516 : row12516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12516 := by decide +kernel

theorem rowEval12516 (x : Key → ℝ) : Integer.Sparse.eval row12516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12516, Integer.Sparse.eval_collectBalanced, rawRowCheck12516]

theorem rawRowCheck12517 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form23 = rawRow12517 := by decide +kernel

theorem rowCheck12517 : row12517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12517 := by decide +kernel

theorem rowEval12517 (x : Key → ℝ) : Integer.Sparse.eval row12517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12517, Integer.Sparse.eval_collectBalanced, rawRowCheck12517]

theorem rawRowCheck12518 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form23 = rawRow12518 := by decide +kernel

theorem rowCheck12518 : row12518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12518 := by decide +kernel

theorem rowEval12518 (x : Key → ℝ) : Integer.Sparse.eval row12518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12518, Integer.Sparse.eval_collectBalanced, rawRowCheck12518]

theorem rawRowCheck12519 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form23 = rawRow12519 := by decide +kernel

theorem rowCheck12519 : row12519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12519 := by decide +kernel

theorem rowEval12519 (x : Key → ℝ) : Integer.Sparse.eval row12519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12519, Integer.Sparse.eval_collectBalanced, rawRowCheck12519]

theorem rawRowCheck12520 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form23 = rawRow12520 := by decide +kernel

theorem rowCheck12520 : row12520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12520 := by decide +kernel

theorem rowEval12520 (x : Key → ℝ) : Integer.Sparse.eval row12520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12520, Integer.Sparse.eval_collectBalanced, rawRowCheck12520]

theorem rawRowCheck12521 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form23 = rawRow12521 := by decide +kernel

theorem rowCheck12521 : row12521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12521 := by decide +kernel

theorem rowEval12521 (x : Key → ℝ) : Integer.Sparse.eval row12521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12521, Integer.Sparse.eval_collectBalanced, rawRowCheck12521]

theorem rawRowCheck12522 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form23 = rawRow12522 := by decide +kernel

theorem rowCheck12522 : row12522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12522 := by decide +kernel

theorem rowEval12522 (x : Key → ℝ) : Integer.Sparse.eval row12522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12522, Integer.Sparse.eval_collectBalanced, rawRowCheck12522]

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

theorem entryCheck25_23 : entry25_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_23 k)) := by decide +kernel

theorem rowsSound25_23 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval12515 x
  · exact rowEval12516 x
  · exact rowEval12517 x
  · exact rowEval12518 x
  · exact rowEval12519 x
  · exact rowEval12520 x
  · exact rowEval12521 x
  · exact rowEval12522 x

theorem entryEval25_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_23 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck25_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_23]

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

theorem entryEvalRow23_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 23 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 23).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval23_0_e B hB
  · exact entryEval23_1 B hB
  · exact entryEval23_2 B hB
  · exact entryEval23_3 B hB
  · exact entryEval23_4 B hB
  · exact entryEval23_5_e B hB
  · exact entryEval23_6 B hB
  · exact entryEval23_7_e B hB
  · exact entryEval23_8_e B hB
  · exact entryEval23_9_e B hB
  · exact entryEval23_10 B hB
  · exact entryEval23_11 B hB
  · exact entryEval23_12 B hB
  · exact entryEval23_13 B hB
  · exact entryEval23_14 B hB
  · exact entryEval23_15 B hB
  · exact entryEval23_16 B hB
  · exact entryEval23_17 B hB
  · exact entryEval23_18 B hB
  · exact entryEval23_19 B hB
  · exact entryEval23_20 B hB
  · exact entryEval23_21_e B hB
  · exact entryEval23_22_e B hB
  · exact entryEval23_23 B hB
  · exact (entryEval24_23 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_23 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_23_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23_e_oai
