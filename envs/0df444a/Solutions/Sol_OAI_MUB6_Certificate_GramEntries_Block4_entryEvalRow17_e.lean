-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:45:04.377222+00:00
-- url     : https://prove2.me/submissions/8f24c3c4-7dcb-4189-a798-c8d44be1673a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_17_e

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

theorem rawRowCheck16725 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form1 = rawRow16725 := by decide +kernel

theorem rowCheck16725 : row16725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16725 := by decide +kernel

theorem rowEval16725 (x : Key → ℝ) : Integer.Sparse.eval row16725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16725, Integer.Sparse.eval_collectBalanced, rawRowCheck16725]

theorem rawRowCheck16726 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form1 = rawRow16726 := by decide +kernel

theorem rowCheck16726 : row16726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16726 := by decide +kernel

theorem rowEval16726 (x : Key → ℝ) : Integer.Sparse.eval row16726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16726, Integer.Sparse.eval_collectBalanced, rawRowCheck16726]

theorem rawRowCheck16727 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form1 = rawRow16727 := by decide +kernel

theorem rowCheck16727 : row16727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16727 := by decide +kernel

theorem rowEval16727 (x : Key → ℝ) : Integer.Sparse.eval row16727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16727, Integer.Sparse.eval_collectBalanced, rawRowCheck16727]

theorem rawRowCheck16728 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form1 = rawRow16728 := by decide +kernel

theorem rowCheck16728 : row16728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16728 := by decide +kernel

theorem rowEval16728 (x : Key → ℝ) : Integer.Sparse.eval row16728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16728, Integer.Sparse.eval_collectBalanced, rawRowCheck16728]

theorem rawRowCheck16729 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form1 = rawRow16729 := by decide +kernel

theorem rowCheck16729 : row16729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16729 := by decide +kernel

theorem rowEval16729 (x : Key → ℝ) : Integer.Sparse.eval row16729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16729, Integer.Sparse.eval_collectBalanced, rawRowCheck16729]

theorem rawRowCheck16730 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form1 = rawRow16730 := by decide +kernel

theorem rowCheck16730 : row16730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16730 := by decide +kernel

theorem rowEval16730 (x : Key → ℝ) : Integer.Sparse.eval row16730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16730, Integer.Sparse.eval_collectBalanced, rawRowCheck16730]

theorem rawRowCheck16731 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form1 = rawRow16731 := by decide +kernel

theorem rowCheck16731 : row16731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16731 := by decide +kernel

theorem rowEval16731 (x : Key → ℝ) : Integer.Sparse.eval row16731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16731, Integer.Sparse.eval_collectBalanced, rawRowCheck16731]

theorem rawRowCheck16732 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form1 = rawRow16732 := by decide +kernel

theorem rowCheck16732 : row16732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16732 := by decide +kernel

theorem rowEval16732 (x : Key → ℝ) : Integer.Sparse.eval row16732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16732, Integer.Sparse.eval_collectBalanced, rawRowCheck16732]

theorem rawRowCheck16733 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form1 = rawRow16733 := by decide +kernel

theorem rowCheck16733 : row16733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16733 := by decide +kernel

theorem rowEval16733 (x : Key → ℝ) : Integer.Sparse.eval row16733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16733, Integer.Sparse.eval_collectBalanced, rawRowCheck16733]

theorem rawRowCheck16734 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form1 = rawRow16734 := by decide +kernel

theorem rowCheck16734 : row16734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16734 := by decide +kernel

theorem rowEval16734 (x : Key → ℝ) : Integer.Sparse.eval row16734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16734, Integer.Sparse.eval_collectBalanced, rawRowCheck16734]

theorem rawRowCheck16735 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form1 = rawRow16735 := by decide +kernel

theorem rowCheck16735 : row16735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16735 := by decide +kernel

theorem rowEval16735 (x : Key → ℝ) : Integer.Sparse.eval row16735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16735, Integer.Sparse.eval_collectBalanced, rawRowCheck16735]

theorem rawRowCheck16736 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form1 = rawRow16736 := by decide +kernel

theorem rowCheck16736 : row16736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16736 := by decide +kernel

theorem rowEval16736 (x : Key → ℝ) : Integer.Sparse.eval row16736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16736, Integer.Sparse.eval_collectBalanced, rawRowCheck16736]

theorem rawRowCheck16737 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form1 = rawRow16737 := by decide +kernel

theorem rowCheck16737 : row16737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16737 := by decide +kernel

theorem rowEval16737 (x : Key → ℝ) : Integer.Sparse.eval row16737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16737, Integer.Sparse.eval_collectBalanced, rawRowCheck16737]

theorem rawRowCheck16738 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form1 = rawRow16738 := by decide +kernel

theorem rowCheck16738 : row16738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16738 := by decide +kernel

theorem rowEval16738 (x : Key → ℝ) : Integer.Sparse.eval row16738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16738, Integer.Sparse.eval_collectBalanced, rawRowCheck16738]

theorem rawRowCheck16739 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form1 = rawRow16739 := by decide +kernel

theorem rowCheck16739 : row16739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16739 := by decide +kernel

theorem rowEval16739 (x : Key → ℝ) : Integer.Sparse.eval row16739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16739, Integer.Sparse.eval_collectBalanced, rawRowCheck16739]

theorem rawRowCheck16740 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form1 = rawRow16740 := by decide +kernel

theorem rowCheck16740 : row16740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16740 := by decide +kernel

theorem rowEval16740 (x : Key → ℝ) : Integer.Sparse.eval row16740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16740, Integer.Sparse.eval_collectBalanced, rawRowCheck16740]

theorem rawRowCheck16741 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form1 = rawRow16741 := by decide +kernel

theorem rowCheck16741 : row16741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16741 := by decide +kernel

theorem rowEval16741 (x : Key → ℝ) : Integer.Sparse.eval row16741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16741, Integer.Sparse.eval_collectBalanced, rawRowCheck16741]

theorem rawRowCheck16742 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form1 = rawRow16742 := by decide +kernel

theorem rowCheck16742 : row16742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16742 := by decide +kernel

theorem rowEval16742 (x : Key → ℝ) : Integer.Sparse.eval row16742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16742, Integer.Sparse.eval_collectBalanced, rawRowCheck16742]

theorem rawRowCheck16743 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form2 = rawRow16743 := by decide +kernel

theorem rowCheck16743 : row16743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16743 := by decide +kernel

theorem rowEval16743 (x : Key → ℝ) : Integer.Sparse.eval row16743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16743, Integer.Sparse.eval_collectBalanced, rawRowCheck16743]

theorem rawRowCheck16744 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form2 = rawRow16744 := by decide +kernel

theorem rowCheck16744 : row16744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16744 := by decide +kernel

theorem rowEval16744 (x : Key → ℝ) : Integer.Sparse.eval row16744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16744, Integer.Sparse.eval_collectBalanced, rawRowCheck16744]

theorem rawRowCheck16745 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form2 = rawRow16745 := by decide +kernel

theorem rowCheck16745 : row16745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16745 := by decide +kernel

theorem rowEval16745 (x : Key → ℝ) : Integer.Sparse.eval row16745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16745, Integer.Sparse.eval_collectBalanced, rawRowCheck16745]

theorem rawRowCheck16746 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form2 = rawRow16746 := by decide +kernel

theorem rowCheck16746 : row16746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16746 := by decide +kernel

theorem rowEval16746 (x : Key → ℝ) : Integer.Sparse.eval row16746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16746, Integer.Sparse.eval_collectBalanced, rawRowCheck16746]

theorem rawRowCheck16747 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form2 = rawRow16747 := by decide +kernel

theorem rowCheck16747 : row16747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16747 := by decide +kernel

theorem rowEval16747 (x : Key → ℝ) : Integer.Sparse.eval row16747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16747, Integer.Sparse.eval_collectBalanced, rawRowCheck16747]

theorem rawRowCheck16748 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form2 = rawRow16748 := by decide +kernel

theorem rowCheck16748 : row16748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16748 := by decide +kernel

theorem rowEval16748 (x : Key → ℝ) : Integer.Sparse.eval row16748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16748, Integer.Sparse.eval_collectBalanced, rawRowCheck16748]

theorem rawRowCheck16749 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form2 = rawRow16749 := by decide +kernel

theorem rowCheck16749 : row16749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16749 := by decide +kernel

theorem rowEval16749 (x : Key → ℝ) : Integer.Sparse.eval row16749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16749, Integer.Sparse.eval_collectBalanced, rawRowCheck16749]

theorem rawRowCheck16750 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form2 = rawRow16750 := by decide +kernel

theorem rowCheck16750 : row16750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16750 := by decide +kernel

theorem rowEval16750 (x : Key → ℝ) : Integer.Sparse.eval row16750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16750, Integer.Sparse.eval_collectBalanced, rawRowCheck16750]

theorem rawRowCheck16751 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form2 = rawRow16751 := by decide +kernel

theorem rowCheck16751 : row16751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16751 := by decide +kernel

theorem rowEval16751 (x : Key → ℝ) : Integer.Sparse.eval row16751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16751, Integer.Sparse.eval_collectBalanced, rawRowCheck16751]

theorem rawRowCheck16752 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form2 = rawRow16752 := by decide +kernel

theorem rowCheck16752 : row16752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16752 := by decide +kernel

theorem rowEval16752 (x : Key → ℝ) : Integer.Sparse.eval row16752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16752, Integer.Sparse.eval_collectBalanced, rawRowCheck16752]

theorem rawRowCheck16753 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form2 = rawRow16753 := by decide +kernel

theorem rowCheck16753 : row16753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16753 := by decide +kernel

theorem rowEval16753 (x : Key → ℝ) : Integer.Sparse.eval row16753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16753, Integer.Sparse.eval_collectBalanced, rawRowCheck16753]

theorem rawRowCheck16754 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form2 = rawRow16754 := by decide +kernel

theorem rowCheck16754 : row16754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16754 := by decide +kernel

theorem rowEval16754 (x : Key → ℝ) : Integer.Sparse.eval row16754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16754, Integer.Sparse.eval_collectBalanced, rawRowCheck16754]

theorem rawRowCheck16755 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form2 = rawRow16755 := by decide +kernel

theorem rowCheck16755 : row16755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16755 := by decide +kernel

theorem rowEval16755 (x : Key → ℝ) : Integer.Sparse.eval row16755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16755, Integer.Sparse.eval_collectBalanced, rawRowCheck16755]

theorem rawRowCheck16756 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form2 = rawRow16756 := by decide +kernel

theorem rowCheck16756 : row16756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16756 := by decide +kernel

theorem rowEval16756 (x : Key → ℝ) : Integer.Sparse.eval row16756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16756, Integer.Sparse.eval_collectBalanced, rawRowCheck16756]

theorem rawRowCheck16757 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form2 = rawRow16757 := by decide +kernel

theorem rowCheck16757 : row16757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16757 := by decide +kernel

theorem rowEval16757 (x : Key → ℝ) : Integer.Sparse.eval row16757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16757, Integer.Sparse.eval_collectBalanced, rawRowCheck16757]

theorem rawRowCheck16758 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form2 = rawRow16758 := by decide +kernel

theorem rowCheck16758 : row16758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16758 := by decide +kernel

theorem rowEval16758 (x : Key → ℝ) : Integer.Sparse.eval row16758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16758, Integer.Sparse.eval_collectBalanced, rawRowCheck16758]

theorem rawRowCheck16759 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form2 = rawRow16759 := by decide +kernel

theorem rowCheck16759 : row16759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16759 := by decide +kernel

theorem rowEval16759 (x : Key → ℝ) : Integer.Sparse.eval row16759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16759, Integer.Sparse.eval_collectBalanced, rawRowCheck16759]

theorem rawRowCheck16760 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form2 = rawRow16760 := by decide +kernel

theorem rowCheck16760 : row16760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16760 := by decide +kernel

theorem rowEval16760 (x : Key → ℝ) : Integer.Sparse.eval row16760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16760, Integer.Sparse.eval_collectBalanced, rawRowCheck16760]

theorem rawRowCheck16761 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form3 = rawRow16761 := by decide +kernel

theorem rowCheck16761 : row16761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16761 := by decide +kernel

theorem rowEval16761 (x : Key → ℝ) : Integer.Sparse.eval row16761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16761, Integer.Sparse.eval_collectBalanced, rawRowCheck16761]

theorem rawRowCheck16762 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form3 = rawRow16762 := by decide +kernel

theorem rowCheck16762 : row16762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16762 := by decide +kernel

theorem rowEval16762 (x : Key → ℝ) : Integer.Sparse.eval row16762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16762, Integer.Sparse.eval_collectBalanced, rawRowCheck16762]

theorem rawRowCheck16763 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form3 = rawRow16763 := by decide +kernel

theorem rowCheck16763 : row16763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16763 := by decide +kernel

theorem rowEval16763 (x : Key → ℝ) : Integer.Sparse.eval row16763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16763, Integer.Sparse.eval_collectBalanced, rawRowCheck16763]

theorem rawRowCheck16764 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form3 = rawRow16764 := by decide +kernel

theorem rowCheck16764 : row16764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16764 := by decide +kernel

theorem rowEval16764 (x : Key → ℝ) : Integer.Sparse.eval row16764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16764, Integer.Sparse.eval_collectBalanced, rawRowCheck16764]

theorem rawRowCheck16765 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form3 = rawRow16765 := by decide +kernel

theorem rowCheck16765 : row16765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16765 := by decide +kernel

theorem rowEval16765 (x : Key → ℝ) : Integer.Sparse.eval row16765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16765, Integer.Sparse.eval_collectBalanced, rawRowCheck16765]

theorem rawRowCheck16766 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form3 = rawRow16766 := by decide +kernel

theorem rowCheck16766 : row16766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16766 := by decide +kernel

theorem rowEval16766 (x : Key → ℝ) : Integer.Sparse.eval row16766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16766, Integer.Sparse.eval_collectBalanced, rawRowCheck16766]

theorem rawRowCheck16767 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form3 = rawRow16767 := by decide +kernel

theorem rowCheck16767 : row16767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16767 := by decide +kernel

theorem rowEval16767 (x : Key → ℝ) : Integer.Sparse.eval row16767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16767, Integer.Sparse.eval_collectBalanced, rawRowCheck16767]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck16768 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form3 = rawRow16768 := by decide +kernel

theorem rowCheck16768 : row16768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16768 := by decide +kernel

theorem rowEval16768 (x : Key → ℝ) : Integer.Sparse.eval row16768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16768, Integer.Sparse.eval_collectBalanced, rawRowCheck16768]

theorem rawRowCheck16769 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form3 = rawRow16769 := by decide +kernel

theorem rowCheck16769 : row16769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16769 := by decide +kernel

theorem rowEval16769 (x : Key → ℝ) : Integer.Sparse.eval row16769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16769, Integer.Sparse.eval_collectBalanced, rawRowCheck16769]

theorem rawRowCheck16770 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form3 = rawRow16770 := by decide +kernel

theorem rowCheck16770 : row16770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16770 := by decide +kernel

theorem rowEval16770 (x : Key → ℝ) : Integer.Sparse.eval row16770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16770, Integer.Sparse.eval_collectBalanced, rawRowCheck16770]

theorem rawRowCheck16771 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form3 = rawRow16771 := by decide +kernel

theorem rowCheck16771 : row16771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16771 := by decide +kernel

theorem rowEval16771 (x : Key → ℝ) : Integer.Sparse.eval row16771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16771, Integer.Sparse.eval_collectBalanced, rawRowCheck16771]

theorem rawRowCheck16772 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form3 = rawRow16772 := by decide +kernel

theorem rowCheck16772 : row16772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16772 := by decide +kernel

theorem rowEval16772 (x : Key → ℝ) : Integer.Sparse.eval row16772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16772, Integer.Sparse.eval_collectBalanced, rawRowCheck16772]

theorem rawRowCheck16773 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form3 = rawRow16773 := by decide +kernel

theorem rowCheck16773 : row16773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16773 := by decide +kernel

theorem rowEval16773 (x : Key → ℝ) : Integer.Sparse.eval row16773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16773, Integer.Sparse.eval_collectBalanced, rawRowCheck16773]

theorem rawRowCheck16774 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form3 = rawRow16774 := by decide +kernel

theorem rowCheck16774 : row16774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16774 := by decide +kernel

theorem rowEval16774 (x : Key → ℝ) : Integer.Sparse.eval row16774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16774, Integer.Sparse.eval_collectBalanced, rawRowCheck16774]

theorem rawRowCheck16775 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form3 = rawRow16775 := by decide +kernel

theorem rowCheck16775 : row16775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16775 := by decide +kernel

theorem rowEval16775 (x : Key → ℝ) : Integer.Sparse.eval row16775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16775, Integer.Sparse.eval_collectBalanced, rawRowCheck16775]

theorem rawRowCheck16776 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form3 = rawRow16776 := by decide +kernel

theorem rowCheck16776 : row16776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16776 := by decide +kernel

theorem rowEval16776 (x : Key → ℝ) : Integer.Sparse.eval row16776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16776, Integer.Sparse.eval_collectBalanced, rawRowCheck16776]

theorem rawRowCheck16777 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form3 = rawRow16777 := by decide +kernel

theorem rowCheck16777 : row16777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16777 := by decide +kernel

theorem rowEval16777 (x : Key → ℝ) : Integer.Sparse.eval row16777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16777, Integer.Sparse.eval_collectBalanced, rawRowCheck16777]

theorem rawRowCheck16778 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form3 = rawRow16778 := by decide +kernel

theorem rowCheck16778 : row16778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16778 := by decide +kernel

theorem rowEval16778 (x : Key → ℝ) : Integer.Sparse.eval row16778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16778, Integer.Sparse.eval_collectBalanced, rawRowCheck16778]

theorem rawRowCheck16779 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form4 = rawRow16779 := by decide +kernel

theorem rowCheck16779 : row16779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16779 := by decide +kernel

theorem rowEval16779 (x : Key → ℝ) : Integer.Sparse.eval row16779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16779, Integer.Sparse.eval_collectBalanced, rawRowCheck16779]

theorem rawRowCheck16780 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form4 = rawRow16780 := by decide +kernel

theorem rowCheck16780 : row16780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16780 := by decide +kernel

theorem rowEval16780 (x : Key → ℝ) : Integer.Sparse.eval row16780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16780, Integer.Sparse.eval_collectBalanced, rawRowCheck16780]

theorem rawRowCheck16781 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form4 = rawRow16781 := by decide +kernel

theorem rowCheck16781 : row16781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16781 := by decide +kernel

theorem rowEval16781 (x : Key → ℝ) : Integer.Sparse.eval row16781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16781, Integer.Sparse.eval_collectBalanced, rawRowCheck16781]

theorem rawRowCheck16782 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form4 = rawRow16782 := by decide +kernel

theorem rowCheck16782 : row16782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16782 := by decide +kernel

theorem rowEval16782 (x : Key → ℝ) : Integer.Sparse.eval row16782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16782, Integer.Sparse.eval_collectBalanced, rawRowCheck16782]

theorem rawRowCheck16783 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form4 = rawRow16783 := by decide +kernel

theorem rowCheck16783 : row16783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16783 := by decide +kernel

theorem rowEval16783 (x : Key → ℝ) : Integer.Sparse.eval row16783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16783, Integer.Sparse.eval_collectBalanced, rawRowCheck16783]

theorem rawRowCheck16784 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form4 = rawRow16784 := by decide +kernel

theorem rowCheck16784 : row16784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16784 := by decide +kernel

theorem rowEval16784 (x : Key → ℝ) : Integer.Sparse.eval row16784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16784, Integer.Sparse.eval_collectBalanced, rawRowCheck16784]

theorem rawRowCheck16785 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form4 = rawRow16785 := by decide +kernel

theorem rowCheck16785 : row16785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16785 := by decide +kernel

theorem rowEval16785 (x : Key → ℝ) : Integer.Sparse.eval row16785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16785, Integer.Sparse.eval_collectBalanced, rawRowCheck16785]

theorem rawRowCheck16786 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form4 = rawRow16786 := by decide +kernel

theorem rowCheck16786 : row16786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16786 := by decide +kernel

theorem rowEval16786 (x : Key → ℝ) : Integer.Sparse.eval row16786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16786, Integer.Sparse.eval_collectBalanced, rawRowCheck16786]

theorem rawRowCheck16787 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form4 = rawRow16787 := by decide +kernel

theorem rowCheck16787 : row16787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16787 := by decide +kernel

theorem rowEval16787 (x : Key → ℝ) : Integer.Sparse.eval row16787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16787, Integer.Sparse.eval_collectBalanced, rawRowCheck16787]

theorem rawRowCheck16788 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form4 = rawRow16788 := by decide +kernel

theorem rowCheck16788 : row16788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16788 := by decide +kernel

theorem rowEval16788 (x : Key → ℝ) : Integer.Sparse.eval row16788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16788, Integer.Sparse.eval_collectBalanced, rawRowCheck16788]

theorem rawRowCheck16789 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form4 = rawRow16789 := by decide +kernel

theorem rowCheck16789 : row16789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16789 := by decide +kernel

theorem rowEval16789 (x : Key → ℝ) : Integer.Sparse.eval row16789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16789, Integer.Sparse.eval_collectBalanced, rawRowCheck16789]

theorem rawRowCheck16790 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form4 = rawRow16790 := by decide +kernel

theorem rowCheck16790 : row16790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16790 := by decide +kernel

theorem rowEval16790 (x : Key → ℝ) : Integer.Sparse.eval row16790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16790, Integer.Sparse.eval_collectBalanced, rawRowCheck16790]

theorem rawRowCheck16791 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form4 = rawRow16791 := by decide +kernel

theorem rowCheck16791 : row16791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16791 := by decide +kernel

theorem rowEval16791 (x : Key → ℝ) : Integer.Sparse.eval row16791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16791, Integer.Sparse.eval_collectBalanced, rawRowCheck16791]

theorem rawRowCheck16792 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form4 = rawRow16792 := by decide +kernel

theorem rowCheck16792 : row16792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16792 := by decide +kernel

theorem rowEval16792 (x : Key → ℝ) : Integer.Sparse.eval row16792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16792, Integer.Sparse.eval_collectBalanced, rawRowCheck16792]

theorem rawRowCheck16793 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form4 = rawRow16793 := by decide +kernel

theorem rowCheck16793 : row16793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16793 := by decide +kernel

theorem rowEval16793 (x : Key → ℝ) : Integer.Sparse.eval row16793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16793, Integer.Sparse.eval_collectBalanced, rawRowCheck16793]

theorem rawRowCheck16794 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form4 = rawRow16794 := by decide +kernel

theorem rowCheck16794 : row16794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16794 := by decide +kernel

theorem rowEval16794 (x : Key → ℝ) : Integer.Sparse.eval row16794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16794, Integer.Sparse.eval_collectBalanced, rawRowCheck16794]

theorem rawRowCheck16795 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form4 = rawRow16795 := by decide +kernel

theorem rowCheck16795 : row16795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16795 := by decide +kernel

theorem rowEval16795 (x : Key → ℝ) : Integer.Sparse.eval row16795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16795, Integer.Sparse.eval_collectBalanced, rawRowCheck16795]

theorem rawRowCheck16796 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form4 = rawRow16796 := by decide +kernel

theorem rowCheck16796 : row16796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16796 := by decide +kernel

theorem rowEval16796 (x : Key → ℝ) : Integer.Sparse.eval row16796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16796, Integer.Sparse.eval_collectBalanced, rawRowCheck16796]

theorem rawRowCheck16797 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form5 = rawRow16797 := by decide +kernel

theorem rowCheck16797 : row16797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16797 := by decide +kernel

theorem rowEval16797 (x : Key → ℝ) : Integer.Sparse.eval row16797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16797, Integer.Sparse.eval_collectBalanced, rawRowCheck16797]

theorem rawRowCheck16798 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form5 = rawRow16798 := by decide +kernel

theorem rowCheck16798 : row16798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16798 := by decide +kernel

theorem rowEval16798 (x : Key → ℝ) : Integer.Sparse.eval row16798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16798, Integer.Sparse.eval_collectBalanced, rawRowCheck16798]

theorem rawRowCheck16799 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form5 = rawRow16799 := by decide +kernel

theorem rowCheck16799 : row16799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16799 := by decide +kernel

theorem rowEval16799 (x : Key → ℝ) : Integer.Sparse.eval row16799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16799, Integer.Sparse.eval_collectBalanced, rawRowCheck16799]

theorem rawRowCheck16800 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form5 = rawRow16800 := by decide +kernel

theorem rowCheck16800 : row16800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16800 := by decide +kernel

theorem rowEval16800 (x : Key → ℝ) : Integer.Sparse.eval row16800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16800, Integer.Sparse.eval_collectBalanced, rawRowCheck16800]

theorem rawRowCheck16801 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form5 = rawRow16801 := by decide +kernel

theorem rowCheck16801 : row16801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16801 := by decide +kernel

theorem rowEval16801 (x : Key → ℝ) : Integer.Sparse.eval row16801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16801, Integer.Sparse.eval_collectBalanced, rawRowCheck16801]

theorem rawRowCheck16802 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form5 = rawRow16802 := by decide +kernel

theorem rowCheck16802 : row16802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16802 := by decide +kernel

theorem rowEval16802 (x : Key → ℝ) : Integer.Sparse.eval row16802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16802, Integer.Sparse.eval_collectBalanced, rawRowCheck16802]

theorem rawRowCheck16803 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form5 = rawRow16803 := by decide +kernel

theorem rowCheck16803 : row16803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16803 := by decide +kernel

theorem rowEval16803 (x : Key → ℝ) : Integer.Sparse.eval row16803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16803, Integer.Sparse.eval_collectBalanced, rawRowCheck16803]

theorem rawRowCheck16804 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form5 = rawRow16804 := by decide +kernel

theorem rowCheck16804 : row16804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16804 := by decide +kernel

theorem rowEval16804 (x : Key → ℝ) : Integer.Sparse.eval row16804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16804, Integer.Sparse.eval_collectBalanced, rawRowCheck16804]

theorem rawRowCheck16805 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form5 = rawRow16805 := by decide +kernel

theorem rowCheck16805 : row16805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16805 := by decide +kernel

theorem rowEval16805 (x : Key → ℝ) : Integer.Sparse.eval row16805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16805, Integer.Sparse.eval_collectBalanced, rawRowCheck16805]

theorem rawRowCheck16806 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form5 = rawRow16806 := by decide +kernel

theorem rowCheck16806 : row16806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16806 := by decide +kernel

theorem rowEval16806 (x : Key → ℝ) : Integer.Sparse.eval row16806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16806, Integer.Sparse.eval_collectBalanced, rawRowCheck16806]

theorem rawRowCheck16807 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form5 = rawRow16807 := by decide +kernel

theorem rowCheck16807 : row16807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16807 := by decide +kernel

theorem rowEval16807 (x : Key → ℝ) : Integer.Sparse.eval row16807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16807, Integer.Sparse.eval_collectBalanced, rawRowCheck16807]

theorem rawRowCheck16808 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form5 = rawRow16808 := by decide +kernel

theorem rowCheck16808 : row16808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16808 := by decide +kernel

theorem rowEval16808 (x : Key → ℝ) : Integer.Sparse.eval row16808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16808, Integer.Sparse.eval_collectBalanced, rawRowCheck16808]

theorem rawRowCheck16809 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form5 = rawRow16809 := by decide +kernel

theorem rowCheck16809 : row16809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16809 := by decide +kernel

theorem rowEval16809 (x : Key → ℝ) : Integer.Sparse.eval row16809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16809, Integer.Sparse.eval_collectBalanced, rawRowCheck16809]

theorem rawRowCheck16810 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form5 = rawRow16810 := by decide +kernel

theorem rowCheck16810 : row16810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16810 := by decide +kernel

theorem rowEval16810 (x : Key → ℝ) : Integer.Sparse.eval row16810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16810, Integer.Sparse.eval_collectBalanced, rawRowCheck16810]

theorem rawRowCheck16811 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form5 = rawRow16811 := by decide +kernel

theorem rowCheck16811 : row16811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16811 := by decide +kernel

theorem rowEval16811 (x : Key → ℝ) : Integer.Sparse.eval row16811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16811, Integer.Sparse.eval_collectBalanced, rawRowCheck16811]

theorem rawRowCheck16812 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form5 = rawRow16812 := by decide +kernel

theorem rowCheck16812 : row16812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16812 := by decide +kernel

theorem rowEval16812 (x : Key → ℝ) : Integer.Sparse.eval row16812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16812, Integer.Sparse.eval_collectBalanced, rawRowCheck16812]

theorem rawRowCheck16813 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form5 = rawRow16813 := by decide +kernel

theorem rowCheck16813 : row16813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16813 := by decide +kernel

theorem rowEval16813 (x : Key → ℝ) : Integer.Sparse.eval row16813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16813, Integer.Sparse.eval_collectBalanced, rawRowCheck16813]

theorem rawRowCheck16814 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form5 = rawRow16814 := by decide +kernel

theorem rowCheck16814 : row16814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16814 := by decide +kernel

theorem rowEval16814 (x : Key → ℝ) : Integer.Sparse.eval row16814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16814, Integer.Sparse.eval_collectBalanced, rawRowCheck16814]

theorem rawRowCheck16815 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form6 = rawRow16815 := by decide +kernel

theorem rowCheck16815 : row16815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16815 := by decide +kernel

theorem rowEval16815 (x : Key → ℝ) : Integer.Sparse.eval row16815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16815, Integer.Sparse.eval_collectBalanced, rawRowCheck16815]

theorem rawRowCheck16816 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form6 = rawRow16816 := by decide +kernel

theorem rowCheck16816 : row16816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16816 := by decide +kernel

theorem rowEval16816 (x : Key → ℝ) : Integer.Sparse.eval row16816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16816, Integer.Sparse.eval_collectBalanced, rawRowCheck16816]

theorem rawRowCheck16817 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form6 = rawRow16817 := by decide +kernel

theorem rowCheck16817 : row16817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16817 := by decide +kernel

theorem rowEval16817 (x : Key → ℝ) : Integer.Sparse.eval row16817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16817, Integer.Sparse.eval_collectBalanced, rawRowCheck16817]

theorem rawRowCheck16818 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form6 = rawRow16818 := by decide +kernel

theorem rowCheck16818 : row16818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16818 := by decide +kernel

theorem rowEval16818 (x : Key → ℝ) : Integer.Sparse.eval row16818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16818, Integer.Sparse.eval_collectBalanced, rawRowCheck16818]

theorem rawRowCheck16819 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form6 = rawRow16819 := by decide +kernel

theorem rowCheck16819 : row16819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16819 := by decide +kernel

theorem rowEval16819 (x : Key → ℝ) : Integer.Sparse.eval row16819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16819, Integer.Sparse.eval_collectBalanced, rawRowCheck16819]

theorem rawRowCheck16820 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form6 = rawRow16820 := by decide +kernel

theorem rowCheck16820 : row16820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16820 := by decide +kernel

theorem rowEval16820 (x : Key → ℝ) : Integer.Sparse.eval row16820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16820, Integer.Sparse.eval_collectBalanced, rawRowCheck16820]

theorem rawRowCheck16821 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form6 = rawRow16821 := by decide +kernel

theorem rowCheck16821 : row16821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16821 := by decide +kernel

theorem rowEval16821 (x : Key → ℝ) : Integer.Sparse.eval row16821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16821, Integer.Sparse.eval_collectBalanced, rawRowCheck16821]

theorem rawRowCheck16822 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form6 = rawRow16822 := by decide +kernel

theorem rowCheck16822 : row16822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16822 := by decide +kernel

theorem rowEval16822 (x : Key → ℝ) : Integer.Sparse.eval row16822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16822, Integer.Sparse.eval_collectBalanced, rawRowCheck16822]

theorem rawRowCheck16823 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form6 = rawRow16823 := by decide +kernel

theorem rowCheck16823 : row16823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16823 := by decide +kernel

theorem rowEval16823 (x : Key → ℝ) : Integer.Sparse.eval row16823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16823, Integer.Sparse.eval_collectBalanced, rawRowCheck16823]

theorem rawRowCheck16824 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form6 = rawRow16824 := by decide +kernel

theorem rowCheck16824 : row16824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16824 := by decide +kernel

theorem rowEval16824 (x : Key → ℝ) : Integer.Sparse.eval row16824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16824, Integer.Sparse.eval_collectBalanced, rawRowCheck16824]

theorem rawRowCheck16825 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form6 = rawRow16825 := by decide +kernel

theorem rowCheck16825 : row16825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16825 := by decide +kernel

theorem rowEval16825 (x : Key → ℝ) : Integer.Sparse.eval row16825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16825, Integer.Sparse.eval_collectBalanced, rawRowCheck16825]

theorem rawRowCheck16826 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form6 = rawRow16826 := by decide +kernel

theorem rowCheck16826 : row16826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16826 := by decide +kernel

theorem rowEval16826 (x : Key → ℝ) : Integer.Sparse.eval row16826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16826, Integer.Sparse.eval_collectBalanced, rawRowCheck16826]

theorem rawRowCheck16827 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form6 = rawRow16827 := by decide +kernel

theorem rowCheck16827 : row16827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16827 := by decide +kernel

theorem rowEval16827 (x : Key → ℝ) : Integer.Sparse.eval row16827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16827, Integer.Sparse.eval_collectBalanced, rawRowCheck16827]

theorem rawRowCheck16828 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form6 = rawRow16828 := by decide +kernel

theorem rowCheck16828 : row16828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16828 := by decide +kernel

theorem rowEval16828 (x : Key → ℝ) : Integer.Sparse.eval row16828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16828, Integer.Sparse.eval_collectBalanced, rawRowCheck16828]

theorem rawRowCheck16829 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form6 = rawRow16829 := by decide +kernel

theorem rowCheck16829 : row16829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16829 := by decide +kernel

theorem rowEval16829 (x : Key → ℝ) : Integer.Sparse.eval row16829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16829, Integer.Sparse.eval_collectBalanced, rawRowCheck16829]

theorem rawRowCheck16830 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form6 = rawRow16830 := by decide +kernel

theorem rowCheck16830 : row16830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16830 := by decide +kernel

theorem rowEval16830 (x : Key → ℝ) : Integer.Sparse.eval row16830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16830, Integer.Sparse.eval_collectBalanced, rawRowCheck16830]

theorem rawRowCheck16831 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form6 = rawRow16831 := by decide +kernel

theorem rowCheck16831 : row16831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16831 := by decide +kernel

theorem rowEval16831 (x : Key → ℝ) : Integer.Sparse.eval row16831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16831, Integer.Sparse.eval_collectBalanced, rawRowCheck16831]

theorem rawRowCheck16832 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form6 = rawRow16832 := by decide +kernel

theorem rowCheck16832 : row16832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16832 := by decide +kernel

theorem rowEval16832 (x : Key → ℝ) : Integer.Sparse.eval row16832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16832, Integer.Sparse.eval_collectBalanced, rawRowCheck16832]

theorem rawRowCheck16833 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form7 = rawRow16833 := by decide +kernel

theorem rowCheck16833 : row16833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16833 := by decide +kernel

theorem rowEval16833 (x : Key → ℝ) : Integer.Sparse.eval row16833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16833, Integer.Sparse.eval_collectBalanced, rawRowCheck16833]

theorem rawRowCheck16834 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form7 = rawRow16834 := by decide +kernel

theorem rowCheck16834 : row16834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16834 := by decide +kernel

theorem rowEval16834 (x : Key → ℝ) : Integer.Sparse.eval row16834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16834, Integer.Sparse.eval_collectBalanced, rawRowCheck16834]

theorem rawRowCheck16835 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form7 = rawRow16835 := by decide +kernel

theorem rowCheck16835 : row16835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16835 := by decide +kernel

theorem rowEval16835 (x : Key → ℝ) : Integer.Sparse.eval row16835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16835, Integer.Sparse.eval_collectBalanced, rawRowCheck16835]

theorem rawRowCheck16836 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form7 = rawRow16836 := by decide +kernel

theorem rowCheck16836 : row16836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16836 := by decide +kernel

theorem rowEval16836 (x : Key → ℝ) : Integer.Sparse.eval row16836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16836, Integer.Sparse.eval_collectBalanced, rawRowCheck16836]

theorem rawRowCheck16837 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form7 = rawRow16837 := by decide +kernel

theorem rowCheck16837 : row16837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16837 := by decide +kernel

theorem rowEval16837 (x : Key → ℝ) : Integer.Sparse.eval row16837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16837, Integer.Sparse.eval_collectBalanced, rawRowCheck16837]

theorem rawRowCheck16838 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form7 = rawRow16838 := by decide +kernel

theorem rowCheck16838 : row16838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16838 := by decide +kernel

theorem rowEval16838 (x : Key → ℝ) : Integer.Sparse.eval row16838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16838, Integer.Sparse.eval_collectBalanced, rawRowCheck16838]

theorem rawRowCheck16839 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form7 = rawRow16839 := by decide +kernel

theorem rowCheck16839 : row16839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16839 := by decide +kernel

theorem rowEval16839 (x : Key → ℝ) : Integer.Sparse.eval row16839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16839, Integer.Sparse.eval_collectBalanced, rawRowCheck16839]

theorem rawRowCheck16840 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form7 = rawRow16840 := by decide +kernel

theorem rowCheck16840 : row16840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16840 := by decide +kernel

theorem rowEval16840 (x : Key → ℝ) : Integer.Sparse.eval row16840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16840, Integer.Sparse.eval_collectBalanced, rawRowCheck16840]

theorem rawRowCheck16841 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form7 = rawRow16841 := by decide +kernel

theorem rowCheck16841 : row16841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16841 := by decide +kernel

theorem rowEval16841 (x : Key → ℝ) : Integer.Sparse.eval row16841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16841, Integer.Sparse.eval_collectBalanced, rawRowCheck16841]

theorem rawRowCheck16842 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form7 = rawRow16842 := by decide +kernel

theorem rowCheck16842 : row16842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16842 := by decide +kernel

theorem rowEval16842 (x : Key → ℝ) : Integer.Sparse.eval row16842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16842, Integer.Sparse.eval_collectBalanced, rawRowCheck16842]

theorem rawRowCheck16843 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form7 = rawRow16843 := by decide +kernel

theorem rowCheck16843 : row16843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16843 := by decide +kernel

theorem rowEval16843 (x : Key → ℝ) : Integer.Sparse.eval row16843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16843, Integer.Sparse.eval_collectBalanced, rawRowCheck16843]

theorem rawRowCheck16844 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form7 = rawRow16844 := by decide +kernel

theorem rowCheck16844 : row16844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16844 := by decide +kernel

theorem rowEval16844 (x : Key → ℝ) : Integer.Sparse.eval row16844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16844, Integer.Sparse.eval_collectBalanced, rawRowCheck16844]

theorem rawRowCheck16845 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form7 = rawRow16845 := by decide +kernel

theorem rowCheck16845 : row16845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16845 := by decide +kernel

theorem rowEval16845 (x : Key → ℝ) : Integer.Sparse.eval row16845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16845, Integer.Sparse.eval_collectBalanced, rawRowCheck16845]

theorem rawRowCheck16846 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form7 = rawRow16846 := by decide +kernel

theorem rowCheck16846 : row16846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16846 := by decide +kernel

theorem rowEval16846 (x : Key → ℝ) : Integer.Sparse.eval row16846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16846, Integer.Sparse.eval_collectBalanced, rawRowCheck16846]

theorem rawRowCheck16847 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form7 = rawRow16847 := by decide +kernel

theorem rowCheck16847 : row16847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16847 := by decide +kernel

theorem rowEval16847 (x : Key → ℝ) : Integer.Sparse.eval row16847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16847, Integer.Sparse.eval_collectBalanced, rawRowCheck16847]

theorem rawRowCheck16848 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form7 = rawRow16848 := by decide +kernel

theorem rowCheck16848 : row16848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16848 := by decide +kernel

theorem rowEval16848 (x : Key → ℝ) : Integer.Sparse.eval row16848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16848, Integer.Sparse.eval_collectBalanced, rawRowCheck16848]

theorem rawRowCheck16849 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form7 = rawRow16849 := by decide +kernel

theorem rowCheck16849 : row16849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16849 := by decide +kernel

theorem rowEval16849 (x : Key → ℝ) : Integer.Sparse.eval row16849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16849, Integer.Sparse.eval_collectBalanced, rawRowCheck16849]

theorem rawRowCheck16850 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form7 = rawRow16850 := by decide +kernel

theorem rowCheck16850 : row16850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16850 := by decide +kernel

theorem rowEval16850 (x : Key → ℝ) : Integer.Sparse.eval row16850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16850, Integer.Sparse.eval_collectBalanced, rawRowCheck16850]

theorem rawRowCheck16851 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form8 = rawRow16851 := by decide +kernel

theorem rowCheck16851 : row16851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16851 := by decide +kernel

theorem rowEval16851 (x : Key → ℝ) : Integer.Sparse.eval row16851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16851, Integer.Sparse.eval_collectBalanced, rawRowCheck16851]

theorem rawRowCheck16852 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form8 = rawRow16852 := by decide +kernel

theorem rowCheck16852 : row16852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16852 := by decide +kernel

theorem rowEval16852 (x : Key → ℝ) : Integer.Sparse.eval row16852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16852, Integer.Sparse.eval_collectBalanced, rawRowCheck16852]

theorem rawRowCheck16853 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form8 = rawRow16853 := by decide +kernel

theorem rowCheck16853 : row16853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16853 := by decide +kernel

theorem rowEval16853 (x : Key → ℝ) : Integer.Sparse.eval row16853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16853, Integer.Sparse.eval_collectBalanced, rawRowCheck16853]

theorem rawRowCheck16854 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form8 = rawRow16854 := by decide +kernel

theorem rowCheck16854 : row16854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16854 := by decide +kernel

theorem rowEval16854 (x : Key → ℝ) : Integer.Sparse.eval row16854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16854, Integer.Sparse.eval_collectBalanced, rawRowCheck16854]

theorem rawRowCheck16855 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form8 = rawRow16855 := by decide +kernel

theorem rowCheck16855 : row16855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16855 := by decide +kernel

theorem rowEval16855 (x : Key → ℝ) : Integer.Sparse.eval row16855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16855, Integer.Sparse.eval_collectBalanced, rawRowCheck16855]

theorem rawRowCheck16856 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form8 = rawRow16856 := by decide +kernel

theorem rowCheck16856 : row16856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16856 := by decide +kernel

theorem rowEval16856 (x : Key → ℝ) : Integer.Sparse.eval row16856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16856, Integer.Sparse.eval_collectBalanced, rawRowCheck16856]

theorem rawRowCheck16857 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form8 = rawRow16857 := by decide +kernel

theorem rowCheck16857 : row16857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16857 := by decide +kernel

theorem rowEval16857 (x : Key → ℝ) : Integer.Sparse.eval row16857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16857, Integer.Sparse.eval_collectBalanced, rawRowCheck16857]

theorem rawRowCheck16858 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form8 = rawRow16858 := by decide +kernel

theorem rowCheck16858 : row16858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16858 := by decide +kernel

theorem rowEval16858 (x : Key → ℝ) : Integer.Sparse.eval row16858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16858, Integer.Sparse.eval_collectBalanced, rawRowCheck16858]

theorem rawRowCheck16859 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form8 = rawRow16859 := by decide +kernel

theorem rowCheck16859 : row16859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16859 := by decide +kernel

theorem rowEval16859 (x : Key → ℝ) : Integer.Sparse.eval row16859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16859, Integer.Sparse.eval_collectBalanced, rawRowCheck16859]

theorem rawRowCheck16860 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form8 = rawRow16860 := by decide +kernel

theorem rowCheck16860 : row16860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16860 := by decide +kernel

theorem rowEval16860 (x : Key → ℝ) : Integer.Sparse.eval row16860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16860, Integer.Sparse.eval_collectBalanced, rawRowCheck16860]

theorem rawRowCheck16861 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form8 = rawRow16861 := by decide +kernel

theorem rowCheck16861 : row16861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16861 := by decide +kernel

theorem rowEval16861 (x : Key → ℝ) : Integer.Sparse.eval row16861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16861, Integer.Sparse.eval_collectBalanced, rawRowCheck16861]

theorem rawRowCheck16862 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form8 = rawRow16862 := by decide +kernel

theorem rowCheck16862 : row16862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16862 := by decide +kernel

theorem rowEval16862 (x : Key → ℝ) : Integer.Sparse.eval row16862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16862, Integer.Sparse.eval_collectBalanced, rawRowCheck16862]

theorem rawRowCheck16863 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form8 = rawRow16863 := by decide +kernel

theorem rowCheck16863 : row16863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16863 := by decide +kernel

theorem rowEval16863 (x : Key → ℝ) : Integer.Sparse.eval row16863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16863, Integer.Sparse.eval_collectBalanced, rawRowCheck16863]

theorem rawRowCheck16864 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form8 = rawRow16864 := by decide +kernel

theorem rowCheck16864 : row16864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16864 := by decide +kernel

theorem rowEval16864 (x : Key → ℝ) : Integer.Sparse.eval row16864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16864, Integer.Sparse.eval_collectBalanced, rawRowCheck16864]

theorem rawRowCheck16865 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form8 = rawRow16865 := by decide +kernel

theorem rowCheck16865 : row16865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16865 := by decide +kernel

theorem rowEval16865 (x : Key → ℝ) : Integer.Sparse.eval row16865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16865, Integer.Sparse.eval_collectBalanced, rawRowCheck16865]

theorem rawRowCheck16866 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form8 = rawRow16866 := by decide +kernel

theorem rowCheck16866 : row16866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16866 := by decide +kernel

theorem rowEval16866 (x : Key → ℝ) : Integer.Sparse.eval row16866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16866, Integer.Sparse.eval_collectBalanced, rawRowCheck16866]

theorem rawRowCheck16867 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form8 = rawRow16867 := by decide +kernel

theorem rowCheck16867 : row16867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16867 := by decide +kernel

theorem rowEval16867 (x : Key → ℝ) : Integer.Sparse.eval row16867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16867, Integer.Sparse.eval_collectBalanced, rawRowCheck16867]

theorem rawRowCheck16868 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form8 = rawRow16868 := by decide +kernel

theorem rowCheck16868 : row16868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16868 := by decide +kernel

theorem rowEval16868 (x : Key → ℝ) : Integer.Sparse.eval row16868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16868, Integer.Sparse.eval_collectBalanced, rawRowCheck16868]

theorem rawRowCheck16869 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form9 = rawRow16869 := by decide +kernel

theorem rowCheck16869 : row16869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16869 := by decide +kernel

theorem rowEval16869 (x : Key → ℝ) : Integer.Sparse.eval row16869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16869, Integer.Sparse.eval_collectBalanced, rawRowCheck16869]

theorem rawRowCheck16870 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form9 = rawRow16870 := by decide +kernel

theorem rowCheck16870 : row16870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16870 := by decide +kernel

theorem rowEval16870 (x : Key → ℝ) : Integer.Sparse.eval row16870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16870, Integer.Sparse.eval_collectBalanced, rawRowCheck16870]

theorem rawRowCheck16871 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form9 = rawRow16871 := by decide +kernel

theorem rowCheck16871 : row16871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16871 := by decide +kernel

theorem rowEval16871 (x : Key → ℝ) : Integer.Sparse.eval row16871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16871, Integer.Sparse.eval_collectBalanced, rawRowCheck16871]

theorem rawRowCheck16872 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form9 = rawRow16872 := by decide +kernel

theorem rowCheck16872 : row16872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16872 := by decide +kernel

theorem rowEval16872 (x : Key → ℝ) : Integer.Sparse.eval row16872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16872, Integer.Sparse.eval_collectBalanced, rawRowCheck16872]

theorem rawRowCheck16873 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form9 = rawRow16873 := by decide +kernel

theorem rowCheck16873 : row16873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16873 := by decide +kernel

theorem rowEval16873 (x : Key → ℝ) : Integer.Sparse.eval row16873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16873, Integer.Sparse.eval_collectBalanced, rawRowCheck16873]

theorem rawRowCheck16874 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form9 = rawRow16874 := by decide +kernel

theorem rowCheck16874 : row16874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16874 := by decide +kernel

theorem rowEval16874 (x : Key → ℝ) : Integer.Sparse.eval row16874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16874, Integer.Sparse.eval_collectBalanced, rawRowCheck16874]

theorem rawRowCheck16875 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form9 = rawRow16875 := by decide +kernel

theorem rowCheck16875 : row16875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16875 := by decide +kernel

theorem rowEval16875 (x : Key → ℝ) : Integer.Sparse.eval row16875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16875, Integer.Sparse.eval_collectBalanced, rawRowCheck16875]

theorem rawRowCheck16876 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form9 = rawRow16876 := by decide +kernel

theorem rowCheck16876 : row16876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16876 := by decide +kernel

theorem rowEval16876 (x : Key → ℝ) : Integer.Sparse.eval row16876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16876, Integer.Sparse.eval_collectBalanced, rawRowCheck16876]

theorem rawRowCheck16877 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form9 = rawRow16877 := by decide +kernel

theorem rowCheck16877 : row16877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16877 := by decide +kernel

theorem rowEval16877 (x : Key → ℝ) : Integer.Sparse.eval row16877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16877, Integer.Sparse.eval_collectBalanced, rawRowCheck16877]

theorem rawRowCheck16878 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form9 = rawRow16878 := by decide +kernel

theorem rowCheck16878 : row16878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16878 := by decide +kernel

theorem rowEval16878 (x : Key → ℝ) : Integer.Sparse.eval row16878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16878, Integer.Sparse.eval_collectBalanced, rawRowCheck16878]

theorem rawRowCheck16879 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form9 = rawRow16879 := by decide +kernel

theorem rowCheck16879 : row16879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16879 := by decide +kernel

theorem rowEval16879 (x : Key → ℝ) : Integer.Sparse.eval row16879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16879, Integer.Sparse.eval_collectBalanced, rawRowCheck16879]

theorem rawRowCheck16880 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form9 = rawRow16880 := by decide +kernel

theorem rowCheck16880 : row16880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16880 := by decide +kernel

theorem rowEval16880 (x : Key → ℝ) : Integer.Sparse.eval row16880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16880, Integer.Sparse.eval_collectBalanced, rawRowCheck16880]

theorem rawRowCheck16881 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form9 = rawRow16881 := by decide +kernel

theorem rowCheck16881 : row16881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16881 := by decide +kernel

theorem rowEval16881 (x : Key → ℝ) : Integer.Sparse.eval row16881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16881, Integer.Sparse.eval_collectBalanced, rawRowCheck16881]

theorem rawRowCheck16882 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form9 = rawRow16882 := by decide +kernel

theorem rowCheck16882 : row16882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16882 := by decide +kernel

theorem rowEval16882 (x : Key → ℝ) : Integer.Sparse.eval row16882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16882, Integer.Sparse.eval_collectBalanced, rawRowCheck16882]

theorem rawRowCheck16883 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form9 = rawRow16883 := by decide +kernel

theorem rowCheck16883 : row16883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16883 := by decide +kernel

theorem rowEval16883 (x : Key → ℝ) : Integer.Sparse.eval row16883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16883, Integer.Sparse.eval_collectBalanced, rawRowCheck16883]

theorem rawRowCheck16884 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form9 = rawRow16884 := by decide +kernel

theorem rowCheck16884 : row16884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16884 := by decide +kernel

theorem rowEval16884 (x : Key → ℝ) : Integer.Sparse.eval row16884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16884, Integer.Sparse.eval_collectBalanced, rawRowCheck16884]

theorem rawRowCheck16885 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form9 = rawRow16885 := by decide +kernel

theorem rowCheck16885 : row16885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16885 := by decide +kernel

theorem rowEval16885 (x : Key → ℝ) : Integer.Sparse.eval row16885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16885, Integer.Sparse.eval_collectBalanced, rawRowCheck16885]

theorem rawRowCheck16886 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form9 = rawRow16886 := by decide +kernel

theorem rowCheck16886 : row16886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16886 := by decide +kernel

theorem rowEval16886 (x : Key → ℝ) : Integer.Sparse.eval row16886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16886, Integer.Sparse.eval_collectBalanced, rawRowCheck16886]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17013 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form17 = rawRow17013 := by decide +kernel

theorem rowCheck17013 : row17013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17013 := by decide +kernel

theorem rowEval17013 (x : Key → ℝ) : Integer.Sparse.eval row17013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17013, Integer.Sparse.eval_collectBalanced, rawRowCheck17013]

theorem rawRowCheck17014 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form17 = rawRow17014 := by decide +kernel

theorem rowCheck17014 : row17014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17014 := by decide +kernel

theorem rowEval17014 (x : Key → ℝ) : Integer.Sparse.eval row17014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17014, Integer.Sparse.eval_collectBalanced, rawRowCheck17014]

theorem rawRowCheck17015 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form17 = rawRow17015 := by decide +kernel

theorem rowCheck17015 : row17015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17015 := by decide +kernel

theorem rowEval17015 (x : Key → ℝ) : Integer.Sparse.eval row17015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17015, Integer.Sparse.eval_collectBalanced, rawRowCheck17015]

theorem rawRowCheck17016 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form17 = rawRow17016 := by decide +kernel

theorem rowCheck17016 : row17016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17016 := by decide +kernel

theorem rowEval17016 (x : Key → ℝ) : Integer.Sparse.eval row17016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17016, Integer.Sparse.eval_collectBalanced, rawRowCheck17016]

theorem rawRowCheck17017 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form17 = rawRow17017 := by decide +kernel

theorem rowCheck17017 : row17017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17017 := by decide +kernel

theorem rowEval17017 (x : Key → ℝ) : Integer.Sparse.eval row17017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17017, Integer.Sparse.eval_collectBalanced, rawRowCheck17017]

theorem rawRowCheck17018 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form17 = rawRow17018 := by decide +kernel

theorem rowCheck17018 : row17018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17018 := by decide +kernel

theorem rowEval17018 (x : Key → ℝ) : Integer.Sparse.eval row17018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17018, Integer.Sparse.eval_collectBalanced, rawRowCheck17018]

theorem rawRowCheck17019 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form17 = rawRow17019 := by decide +kernel

theorem rowCheck17019 : row17019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17019 := by decide +kernel

theorem rowEval17019 (x : Key → ℝ) : Integer.Sparse.eval row17019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17019, Integer.Sparse.eval_collectBalanced, rawRowCheck17019]

theorem rawRowCheck17020 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form17 = rawRow17020 := by decide +kernel

theorem rowCheck17020 : row17020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17020 := by decide +kernel

theorem rowEval17020 (x : Key → ℝ) : Integer.Sparse.eval row17020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17020, Integer.Sparse.eval_collectBalanced, rawRowCheck17020]

theorem rawRowCheck17021 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form17 = rawRow17021 := by decide +kernel

theorem rowCheck17021 : row17021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17021 := by decide +kernel

theorem rowEval17021 (x : Key → ℝ) : Integer.Sparse.eval row17021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17021, Integer.Sparse.eval_collectBalanced, rawRowCheck17021]

theorem rawRowCheck17022 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form17 = rawRow17022 := by decide +kernel

theorem rowCheck17022 : row17022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17022 := by decide +kernel

theorem rowEval17022 (x : Key → ℝ) : Integer.Sparse.eval row17022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17022, Integer.Sparse.eval_collectBalanced, rawRowCheck17022]

theorem rawRowCheck17023 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form17 = rawRow17023 := by decide +kernel

theorem rowCheck17023 : row17023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17023 := by decide +kernel

theorem rowEval17023 (x : Key → ℝ) : Integer.Sparse.eval row17023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17023, Integer.Sparse.eval_collectBalanced, rawRowCheck17023]

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

theorem rawRowCheck17024 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form17 = rawRow17024 := by decide +kernel

theorem rowCheck17024 : row17024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17024 := by decide +kernel

theorem rowEval17024 (x : Key → ℝ) : Integer.Sparse.eval row17024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17024, Integer.Sparse.eval_collectBalanced, rawRowCheck17024]

theorem rawRowCheck17025 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form17 = rawRow17025 := by decide +kernel

theorem rowCheck17025 : row17025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17025 := by decide +kernel

theorem rowEval17025 (x : Key → ℝ) : Integer.Sparse.eval row17025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17025, Integer.Sparse.eval_collectBalanced, rawRowCheck17025]

theorem rawRowCheck17026 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form17 = rawRow17026 := by decide +kernel

theorem rowCheck17026 : row17026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17026 := by decide +kernel

theorem rowEval17026 (x : Key → ℝ) : Integer.Sparse.eval row17026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17026, Integer.Sparse.eval_collectBalanced, rawRowCheck17026]

theorem rawRowCheck17027 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form17 = rawRow17027 := by decide +kernel

theorem rowCheck17027 : row17027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17027 := by decide +kernel

theorem rowEval17027 (x : Key → ℝ) : Integer.Sparse.eval row17027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17027, Integer.Sparse.eval_collectBalanced, rawRowCheck17027]

theorem rawRowCheck17028 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form17 = rawRow17028 := by decide +kernel

theorem rowCheck17028 : row17028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17028 := by decide +kernel

theorem rowEval17028 (x : Key → ℝ) : Integer.Sparse.eval row17028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17028, Integer.Sparse.eval_collectBalanced, rawRowCheck17028]

theorem rawRowCheck17029 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form17 = rawRow17029 := by decide +kernel

theorem rowCheck17029 : row17029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17029 := by decide +kernel

theorem rowEval17029 (x : Key → ℝ) : Integer.Sparse.eval row17029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17029, Integer.Sparse.eval_collectBalanced, rawRowCheck17029]

theorem rawRowCheck17030 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form17 = rawRow17030 := by decide +kernel

theorem rowCheck17030 : row17030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17030 := by decide +kernel

theorem rowEval17030 (x : Key → ℝ) : Integer.Sparse.eval row17030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17030, Integer.Sparse.eval_collectBalanced, rawRowCheck17030]

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

theorem entryCheck17_1 : entry17_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_1 k)) := by decide +kernel

theorem rowsSound17_1 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval16725 x
  · exact rowEval16726 x
  · exact rowEval16727 x
  · exact rowEval16728 x
  · exact rowEval16729 x
  · exact rowEval16730 x
  · exact rowEval16731 x
  · exact rowEval16732 x
  · exact rowEval16733 x
  · exact rowEval16734 x
  · exact rowEval16735 x
  · exact rowEval16736 x
  · exact rowEval16737 x
  · exact rowEval16738 x
  · exact rowEval16739 x
  · exact rowEval16740 x
  · exact rowEval16741 x
  · exact rowEval16742 x

theorem entryEval17_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_1 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck17_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_1]

theorem entryCheck17_2 : entry17_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_2 k)) := by decide +kernel

theorem rowsSound17_2 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval16743 x
  · exact rowEval16744 x
  · exact rowEval16745 x
  · exact rowEval16746 x
  · exact rowEval16747 x
  · exact rowEval16748 x
  · exact rowEval16749 x
  · exact rowEval16750 x
  · exact rowEval16751 x
  · exact rowEval16752 x
  · exact rowEval16753 x
  · exact rowEval16754 x
  · exact rowEval16755 x
  · exact rowEval16756 x
  · exact rowEval16757 x
  · exact rowEval16758 x
  · exact rowEval16759 x
  · exact rowEval16760 x

theorem entryEval17_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_2 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck17_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_2]

theorem entryCheck17_3 : entry17_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_3 k)) := by decide +kernel

theorem rowsSound17_3 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval16761 x
  · exact rowEval16762 x
  · exact rowEval16763 x
  · exact rowEval16764 x
  · exact rowEval16765 x
  · exact rowEval16766 x
  · exact rowEval16767 x
  · exact rowEval16768 x
  · exact rowEval16769 x
  · exact rowEval16770 x
  · exact rowEval16771 x
  · exact rowEval16772 x
  · exact rowEval16773 x
  · exact rowEval16774 x
  · exact rowEval16775 x
  · exact rowEval16776 x
  · exact rowEval16777 x
  · exact rowEval16778 x

theorem entryEval17_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_3 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck17_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_3]

theorem entryCheck17_4 : entry17_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_4 k)) := by decide +kernel

theorem rowsSound17_4 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval16779 x
  · exact rowEval16780 x
  · exact rowEval16781 x
  · exact rowEval16782 x
  · exact rowEval16783 x
  · exact rowEval16784 x
  · exact rowEval16785 x
  · exact rowEval16786 x
  · exact rowEval16787 x
  · exact rowEval16788 x
  · exact rowEval16789 x
  · exact rowEval16790 x
  · exact rowEval16791 x
  · exact rowEval16792 x
  · exact rowEval16793 x
  · exact rowEval16794 x
  · exact rowEval16795 x
  · exact rowEval16796 x

theorem entryEval17_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_4 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck17_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_4]

theorem entryCheck17_5 : entry17_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_5 k)) := by decide +kernel

theorem rowsSound17_5 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval16797 x
  · exact rowEval16798 x
  · exact rowEval16799 x
  · exact rowEval16800 x
  · exact rowEval16801 x
  · exact rowEval16802 x
  · exact rowEval16803 x
  · exact rowEval16804 x
  · exact rowEval16805 x
  · exact rowEval16806 x
  · exact rowEval16807 x
  · exact rowEval16808 x
  · exact rowEval16809 x
  · exact rowEval16810 x
  · exact rowEval16811 x
  · exact rowEval16812 x
  · exact rowEval16813 x
  · exact rowEval16814 x

theorem entryEval17_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_5 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck17_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_5]

theorem entryCheck17_6 : entry17_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_6 k)) := by decide +kernel

theorem rowsSound17_6 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval16815 x
  · exact rowEval16816 x
  · exact rowEval16817 x
  · exact rowEval16818 x
  · exact rowEval16819 x
  · exact rowEval16820 x
  · exact rowEval16821 x
  · exact rowEval16822 x
  · exact rowEval16823 x
  · exact rowEval16824 x
  · exact rowEval16825 x
  · exact rowEval16826 x
  · exact rowEval16827 x
  · exact rowEval16828 x
  · exact rowEval16829 x
  · exact rowEval16830 x
  · exact rowEval16831 x
  · exact rowEval16832 x

theorem entryEval17_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_6 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck17_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_6]

theorem entryCheck17_7 : entry17_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_7 k)) := by decide +kernel

theorem rowsSound17_7 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval16833 x
  · exact rowEval16834 x
  · exact rowEval16835 x
  · exact rowEval16836 x
  · exact rowEval16837 x
  · exact rowEval16838 x
  · exact rowEval16839 x
  · exact rowEval16840 x
  · exact rowEval16841 x
  · exact rowEval16842 x
  · exact rowEval16843 x
  · exact rowEval16844 x
  · exact rowEval16845 x
  · exact rowEval16846 x
  · exact rowEval16847 x
  · exact rowEval16848 x
  · exact rowEval16849 x
  · exact rowEval16850 x

theorem entryEval17_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_7 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck17_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_7]

theorem entryCheck17_8 : entry17_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_8 k)) := by decide +kernel

theorem rowsSound17_8 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval16851 x
  · exact rowEval16852 x
  · exact rowEval16853 x
  · exact rowEval16854 x
  · exact rowEval16855 x
  · exact rowEval16856 x
  · exact rowEval16857 x
  · exact rowEval16858 x
  · exact rowEval16859 x
  · exact rowEval16860 x
  · exact rowEval16861 x
  · exact rowEval16862 x
  · exact rowEval16863 x
  · exact rowEval16864 x
  · exact rowEval16865 x
  · exact rowEval16866 x
  · exact rowEval16867 x
  · exact rowEval16868 x

theorem entryEval17_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_8 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck17_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_8]

theorem entryCheck17_9 : entry17_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_9 k)) := by decide +kernel

theorem rowsSound17_9 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval16869 x
  · exact rowEval16870 x
  · exact rowEval16871 x
  · exact rowEval16872 x
  · exact rowEval16873 x
  · exact rowEval16874 x
  · exact rowEval16875 x
  · exact rowEval16876 x
  · exact rowEval16877 x
  · exact rowEval16878 x
  · exact rowEval16879 x
  · exact rowEval16880 x
  · exact rowEval16881 x
  · exact rowEval16882 x
  · exact rowEval16883 x
  · exact rowEval16884 x
  · exact rowEval16885 x
  · exact rowEval16886 x

theorem entryEval17_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_9 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck17_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_9]

theorem entryCheck17_17 : entry17_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_17 k)) := by decide +kernel

theorem rowsSound17_17 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval17013 x
  · exact rowEval17014 x
  · exact rowEval17015 x
  · exact rowEval17016 x
  · exact rowEval17017 x
  · exact rowEval17018 x
  · exact rowEval17019 x
  · exact rowEval17020 x
  · exact rowEval17021 x
  · exact rowEval17022 x
  · exact rowEval17023 x
  · exact rowEval17024 x
  · exact rowEval17025 x
  · exact rowEval17026 x
  · exact rowEval17027 x
  · exact rowEval17028 x
  · exact rowEval17029 x
  · exact rowEval17030 x

theorem entryEval17_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_17 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck17_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_17]

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

theorem rawRowCheck17581 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form17 = rawRow17581 := by decide +kernel

theorem rowCheck17581 : row17581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17581 := by decide +kernel

theorem rowEval17581 (x : Key → ℝ) : Integer.Sparse.eval row17581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17581, Integer.Sparse.eval_collectBalanced, rawRowCheck17581]

theorem rawRowCheck17582 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form17 = rawRow17582 := by decide +kernel

theorem rowCheck17582 : row17582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17582 := by decide +kernel

theorem rowEval17582 (x : Key → ℝ) : Integer.Sparse.eval row17582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17582, Integer.Sparse.eval_collectBalanced, rawRowCheck17582]

theorem rawRowCheck17583 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form17 = rawRow17583 := by decide +kernel

theorem rowCheck17583 : row17583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17583 := by decide +kernel

theorem rowEval17583 (x : Key → ℝ) : Integer.Sparse.eval row17583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17583, Integer.Sparse.eval_collectBalanced, rawRowCheck17583]

theorem rawRowCheck17584 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form17 = rawRow17584 := by decide +kernel

theorem rowCheck17584 : row17584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17584 := by decide +kernel

theorem rowEval17584 (x : Key → ℝ) : Integer.Sparse.eval row17584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17584, Integer.Sparse.eval_collectBalanced, rawRowCheck17584]

theorem rawRowCheck17585 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form17 = rawRow17585 := by decide +kernel

theorem rowCheck17585 : row17585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17585 := by decide +kernel

theorem rowEval17585 (x : Key → ℝ) : Integer.Sparse.eval row17585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17585, Integer.Sparse.eval_collectBalanced, rawRowCheck17585]

theorem rawRowCheck17586 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form17 = rawRow17586 := by decide +kernel

theorem rowCheck17586 : row17586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17586 := by decide +kernel

theorem rowEval17586 (x : Key → ℝ) : Integer.Sparse.eval row17586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17586, Integer.Sparse.eval_collectBalanced, rawRowCheck17586]

theorem rawRowCheck17587 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form17 = rawRow17587 := by decide +kernel

theorem rowCheck17587 : row17587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17587 := by decide +kernel

theorem rowEval17587 (x : Key → ℝ) : Integer.Sparse.eval row17587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17587, Integer.Sparse.eval_collectBalanced, rawRowCheck17587]

theorem rawRowCheck17588 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form17 = rawRow17588 := by decide +kernel

theorem rowCheck17588 : row17588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17588 := by decide +kernel

theorem rowEval17588 (x : Key → ℝ) : Integer.Sparse.eval row17588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17588, Integer.Sparse.eval_collectBalanced, rawRowCheck17588]

theorem rawRowCheck17589 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form17 = rawRow17589 := by decide +kernel

theorem rowCheck17589 : row17589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17589 := by decide +kernel

theorem rowEval17589 (x : Key → ℝ) : Integer.Sparse.eval row17589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17589, Integer.Sparse.eval_collectBalanced, rawRowCheck17589]

theorem rawRowCheck17590 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form17 = rawRow17590 := by decide +kernel

theorem rowCheck17590 : row17590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17590 := by decide +kernel

theorem rowEval17590 (x : Key → ℝ) : Integer.Sparse.eval row17590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17590, Integer.Sparse.eval_collectBalanced, rawRowCheck17590]

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

theorem entryCheck19_17 : entry19_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_17 k)) := by decide +kernel

theorem rowsSound19_17 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval17581 x
  · exact rowEval17582 x
  · exact rowEval17583 x
  · exact rowEval17584 x
  · exact rowEval17585 x
  · exact rowEval17586 x
  · exact rowEval17587 x
  · exact rowEval17588 x
  · exact rowEval17589 x
  · exact rowEval17590 x

theorem entryEval19_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_17 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck19_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_17]

end MUB6.Certificate.GramEntries.Block4

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

theorem rawRowCheck18329 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form17 = rawRow18329 := by decide +kernel

theorem rowCheck18329 : row18329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18329 := by decide +kernel

theorem rowEval18329 (x : Key → ℝ) : Integer.Sparse.eval row18329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18329, Integer.Sparse.eval_collectBalanced, rawRowCheck18329]

theorem rawRowCheck18330 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form17 = rawRow18330 := by decide +kernel

theorem rowCheck18330 : row18330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18330 := by decide +kernel

theorem rowEval18330 (x : Key → ℝ) : Integer.Sparse.eval row18330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18330, Integer.Sparse.eval_collectBalanced, rawRowCheck18330]

theorem rawRowCheck18331 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form17 = rawRow18331 := by decide +kernel

theorem rowCheck18331 : row18331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18331 := by decide +kernel

theorem rowEval18331 (x : Key → ℝ) : Integer.Sparse.eval row18331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18331, Integer.Sparse.eval_collectBalanced, rawRowCheck18331]

theorem rawRowCheck18332 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form17 = rawRow18332 := by decide +kernel

theorem rowCheck18332 : row18332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18332 := by decide +kernel

theorem rowEval18332 (x : Key → ℝ) : Integer.Sparse.eval row18332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18332, Integer.Sparse.eval_collectBalanced, rawRowCheck18332]

theorem rawRowCheck18333 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form17 = rawRow18333 := by decide +kernel

theorem rowCheck18333 : row18333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18333 := by decide +kernel

theorem rowEval18333 (x : Key → ℝ) : Integer.Sparse.eval row18333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18333, Integer.Sparse.eval_collectBalanced, rawRowCheck18333]

theorem rawRowCheck18334 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form17 = rawRow18334 := by decide +kernel

theorem rowCheck18334 : row18334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18334 := by decide +kernel

theorem rowEval18334 (x : Key → ℝ) : Integer.Sparse.eval row18334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18334, Integer.Sparse.eval_collectBalanced, rawRowCheck18334]

theorem rawRowCheck18335 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form17 = rawRow18335 := by decide +kernel

theorem rowCheck18335 : row18335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18335 := by decide +kernel

theorem rowEval18335 (x : Key → ℝ) : Integer.Sparse.eval row18335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18335, Integer.Sparse.eval_collectBalanced, rawRowCheck18335]

theorem rawRowCheck18336 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form17 = rawRow18336 := by decide +kernel

theorem rowCheck18336 : row18336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18336 := by decide +kernel

theorem rowEval18336 (x : Key → ℝ) : Integer.Sparse.eval row18336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18336, Integer.Sparse.eval_collectBalanced, rawRowCheck18336]

theorem rawRowCheck18337 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form17 = rawRow18337 := by decide +kernel

theorem rowCheck18337 : row18337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18337 := by decide +kernel

theorem rowEval18337 (x : Key → ℝ) : Integer.Sparse.eval row18337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18337, Integer.Sparse.eval_collectBalanced, rawRowCheck18337]

theorem rawRowCheck18338 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form17 = rawRow18338 := by decide +kernel

theorem rowCheck18338 : row18338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18338 := by decide +kernel

theorem rowEval18338 (x : Key → ℝ) : Integer.Sparse.eval row18338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18338, Integer.Sparse.eval_collectBalanced, rawRowCheck18338]

theorem rawRowCheck18339 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form17 = rawRow18339 := by decide +kernel

theorem rowCheck18339 : row18339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18339 := by decide +kernel

theorem rowEval18339 (x : Key → ℝ) : Integer.Sparse.eval row18339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18339, Integer.Sparse.eval_collectBalanced, rawRowCheck18339]

theorem rawRowCheck18340 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form17 = rawRow18340 := by decide +kernel

theorem rowCheck18340 : row18340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18340 := by decide +kernel

theorem rowEval18340 (x : Key → ℝ) : Integer.Sparse.eval row18340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18340, Integer.Sparse.eval_collectBalanced, rawRowCheck18340]

theorem rawRowCheck18341 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form17 = rawRow18341 := by decide +kernel

theorem rowCheck18341 : row18341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18341 := by decide +kernel

theorem rowEval18341 (x : Key → ℝ) : Integer.Sparse.eval row18341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18341, Integer.Sparse.eval_collectBalanced, rawRowCheck18341]

theorem rawRowCheck18342 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form17 = rawRow18342 := by decide +kernel

theorem rowCheck18342 : row18342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18342 := by decide +kernel

theorem rowEval18342 (x : Key → ℝ) : Integer.Sparse.eval row18342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18342, Integer.Sparse.eval_collectBalanced, rawRowCheck18342]

theorem rawRowCheck18343 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form17 = rawRow18343 := by decide +kernel

theorem rowCheck18343 : row18343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18343 := by decide +kernel

theorem rowEval18343 (x : Key → ℝ) : Integer.Sparse.eval row18343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18343, Integer.Sparse.eval_collectBalanced, rawRowCheck18343]

theorem rawRowCheck18344 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form17 = rawRow18344 := by decide +kernel

theorem rowCheck18344 : row18344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18344 := by decide +kernel

theorem rowEval18344 (x : Key → ℝ) : Integer.Sparse.eval row18344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18344, Integer.Sparse.eval_collectBalanced, rawRowCheck18344]

theorem rawRowCheck18345 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form17 = rawRow18345 := by decide +kernel

theorem rowCheck18345 : row18345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18345 := by decide +kernel

theorem rowEval18345 (x : Key → ℝ) : Integer.Sparse.eval row18345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18345, Integer.Sparse.eval_collectBalanced, rawRowCheck18345]

theorem rawRowCheck18346 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form17 = rawRow18346 := by decide +kernel

theorem rowCheck18346 : row18346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18346 := by decide +kernel

theorem rowEval18346 (x : Key → ℝ) : Integer.Sparse.eval row18346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18346, Integer.Sparse.eval_collectBalanced, rawRowCheck18346]

theorem rawRowCheck18347 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form17 = rawRow18347 := by decide +kernel

theorem rowCheck18347 : row18347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18347 := by decide +kernel

theorem rowEval18347 (x : Key → ℝ) : Integer.Sparse.eval row18347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18347, Integer.Sparse.eval_collectBalanced, rawRowCheck18347]

theorem rawRowCheck18348 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form17 = rawRow18348 := by decide +kernel

theorem rowCheck18348 : row18348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18348 := by decide +kernel

theorem rowEval18348 (x : Key → ℝ) : Integer.Sparse.eval row18348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18348, Integer.Sparse.eval_collectBalanced, rawRowCheck18348]

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

theorem entryCheck21_17 : entry21_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_17 k)) := by decide +kernel

theorem rowsSound21_17 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval18329 x
  · exact rowEval18330 x
  · exact rowEval18331 x
  · exact rowEval18332 x
  · exact rowEval18333 x
  · exact rowEval18334 x
  · exact rowEval18335 x
  · exact rowEval18336 x
  · exact rowEval18337 x
  · exact rowEval18338 x
  · exact rowEval18339 x
  · exact rowEval18340 x
  · exact rowEval18341 x
  · exact rowEval18342 x
  · exact rowEval18343 x
  · exact rowEval18344 x
  · exact rowEval18345 x
  · exact rowEval18346 x
  · exact rowEval18347 x
  · exact rowEval18348 x

theorem entryEval21_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_17 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck21_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_17]

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

theorem entryEvalRow17_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 17 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 17).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval17_0 B hB
  · exact entryEval17_1 B hB
  · exact entryEval17_2 B hB
  · exact entryEval17_3 B hB
  · exact entryEval17_4 B hB
  · exact entryEval17_5 B hB
  · exact entryEval17_6 B hB
  · exact entryEval17_7 B hB
  · exact entryEval17_8 B hB
  · exact entryEval17_9 B hB
  · exact entryEval17_10_e B hB
  · exact entryEval17_11_e B hB
  · exact entryEval17_12_e B hB
  · exact entryEval17_13_e B hB
  · exact entryEval17_14_e B hB
  · exact entryEval17_15_e B hB
  · exact entryEval17_16_e B hB
  · exact entryEval17_17 B hB
  · exact (entryEval18_17_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e_oai
