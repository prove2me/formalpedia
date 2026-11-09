-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:46:39.556202+00:00
-- url     : https://prove2.me/submissions/f476fa73-3e79-49e2-94eb-d86768ff75b8

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval10_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval8_6_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14080 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form7 = rawRow14080 := by decide +kernel

theorem rowCheck14080 : row14080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14080 := by decide +kernel

theorem rowEval14080 (x : Key → ℝ) : Integer.Sparse.eval row14080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14080, Integer.Sparse.eval_collectBalanced, rawRowCheck14080]

theorem rawRowCheck14081 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14081 := by decide +kernel

theorem rowCheck14081 : row14081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14081 := by decide +kernel

theorem rowEval14081 (x : Key → ℝ) : Integer.Sparse.eval row14081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14081, Integer.Sparse.eval_collectBalanced, rawRowCheck14081]

theorem rawRowCheck14082 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form7 = rawRow14082 := by decide +kernel

theorem rowCheck14082 : row14082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14082 := by decide +kernel

theorem rowEval14082 (x : Key → ℝ) : Integer.Sparse.eval row14082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14082, Integer.Sparse.eval_collectBalanced, rawRowCheck14082]

theorem rawRowCheck14083 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form7 = rawRow14083 := by decide +kernel

theorem rowCheck14083 : row14083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14083 := by decide +kernel

theorem rowEval14083 (x : Key → ℝ) : Integer.Sparse.eval row14083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14083, Integer.Sparse.eval_collectBalanced, rawRowCheck14083]

theorem rawRowCheck14084 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form7 = rawRow14084 := by decide +kernel

theorem rowCheck14084 : row14084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14084 := by decide +kernel

theorem rowEval14084 (x : Key → ℝ) : Integer.Sparse.eval row14084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14084, Integer.Sparse.eval_collectBalanced, rawRowCheck14084]

theorem rawRowCheck14085 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form8 = rawRow14085 := by decide +kernel

theorem rowCheck14085 : row14085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14085 := by decide +kernel

theorem rowEval14085 (x : Key → ℝ) : Integer.Sparse.eval row14085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14085, Integer.Sparse.eval_collectBalanced, rawRowCheck14085]

theorem rawRowCheck14086 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form8 = rawRow14086 := by decide +kernel

theorem rowCheck14086 : row14086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14086 := by decide +kernel

theorem rowEval14086 (x : Key → ℝ) : Integer.Sparse.eval row14086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14086, Integer.Sparse.eval_collectBalanced, rawRowCheck14086]

theorem rawRowCheck14087 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form8 = rawRow14087 := by decide +kernel

theorem rowCheck14087 : row14087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14087 := by decide +kernel

theorem rowEval14087 (x : Key → ℝ) : Integer.Sparse.eval row14087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14087, Integer.Sparse.eval_collectBalanced, rawRowCheck14087]

theorem rawRowCheck14088 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14088 := by decide +kernel

theorem rowCheck14088 : row14088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14088 := by decide +kernel

theorem rowEval14088 (x : Key → ℝ) : Integer.Sparse.eval row14088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14088, Integer.Sparse.eval_collectBalanced, rawRowCheck14088]

theorem rawRowCheck14089 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form8 = rawRow14089 := by decide +kernel

theorem rowCheck14089 : row14089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14089 := by decide +kernel

theorem rowEval14089 (x : Key → ℝ) : Integer.Sparse.eval row14089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14089, Integer.Sparse.eval_collectBalanced, rawRowCheck14089]

theorem rawRowCheck14090 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form8 = rawRow14090 := by decide +kernel

theorem rowCheck14090 : row14090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14090 := by decide +kernel

theorem rowEval14090 (x : Key → ℝ) : Integer.Sparse.eval row14090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14090, Integer.Sparse.eval_collectBalanced, rawRowCheck14090]

theorem rawRowCheck14091 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form8 = rawRow14091 := by decide +kernel

theorem rowCheck14091 : row14091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14091 := by decide +kernel

theorem rowEval14091 (x : Key → ℝ) : Integer.Sparse.eval row14091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14091, Integer.Sparse.eval_collectBalanced, rawRowCheck14091]

theorem rawRowCheck14092 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form8 = rawRow14092 := by decide +kernel

theorem rowCheck14092 : row14092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14092 := by decide +kernel

theorem rowEval14092 (x : Key → ℝ) : Integer.Sparse.eval row14092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14092, Integer.Sparse.eval_collectBalanced, rawRowCheck14092]

theorem rawRowCheck14093 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form8 = rawRow14093 := by decide +kernel

theorem rowCheck14093 : row14093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14093 := by decide +kernel

theorem rowEval14093 (x : Key → ℝ) : Integer.Sparse.eval row14093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14093, Integer.Sparse.eval_collectBalanced, rawRowCheck14093]

theorem rawRowCheck14094 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form8 = rawRow14094 := by decide +kernel

theorem rowCheck14094 : row14094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14094 := by decide +kernel

theorem rowEval14094 (x : Key → ℝ) : Integer.Sparse.eval row14094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14094, Integer.Sparse.eval_collectBalanced, rawRowCheck14094]

theorem rawRowCheck14095 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form8 = rawRow14095 := by decide +kernel

theorem rowCheck14095 : row14095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14095 := by decide +kernel

theorem rowEval14095 (x : Key → ℝ) : Integer.Sparse.eval row14095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck14095, Integer.Sparse.eval_collectBalanced, rawRowCheck14095]

theorem rawRowCheck14096 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form8 = rawRow14096 := by decide +kernel

theorem rowCheck14096 : row14096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14096 := by decide +kernel

theorem rowEval14096 (x : Key → ℝ) : Integer.Sparse.eval row14096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14096, Integer.Sparse.eval_collectBalanced, rawRowCheck14096]

theorem rawRowCheck14097 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form8 = rawRow14097 := by decide +kernel

theorem rowCheck14097 : row14097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14097 := by decide +kernel

theorem rowEval14097 (x : Key → ℝ) : Integer.Sparse.eval row14097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck14097, Integer.Sparse.eval_collectBalanced, rawRowCheck14097]

theorem rawRowCheck14098 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form8 = rawRow14098 := by decide +kernel

theorem rowCheck14098 : row14098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14098 := by decide +kernel

theorem rowEval14098 (x : Key → ℝ) : Integer.Sparse.eval row14098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14098, Integer.Sparse.eval_collectBalanced, rawRowCheck14098]

theorem rawRowCheck14099 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form8 = rawRow14099 := by decide +kernel

theorem rowCheck14099 : row14099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14099 := by decide +kernel

theorem rowEval14099 (x : Key → ℝ) : Integer.Sparse.eval row14099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14099, Integer.Sparse.eval_collectBalanced, rawRowCheck14099]

theorem rawRowCheck14100 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form8 = rawRow14100 := by decide +kernel

theorem rowCheck14100 : row14100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14100 := by decide +kernel

theorem rowEval14100 (x : Key → ℝ) : Integer.Sparse.eval row14100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck14100, Integer.Sparse.eval_collectBalanced, rawRowCheck14100]

theorem rawRowCheck14101 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14101 := by decide +kernel

theorem rowCheck14101 : row14101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14101 := by decide +kernel

theorem rowEval14101 (x : Key → ℝ) : Integer.Sparse.eval row14101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14101, Integer.Sparse.eval_collectBalanced, rawRowCheck14101]

theorem rawRowCheck14102 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form8 = rawRow14102 := by decide +kernel

theorem rowCheck14102 : row14102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14102 := by decide +kernel

theorem rowEval14102 (x : Key → ℝ) : Integer.Sparse.eval row14102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14102, Integer.Sparse.eval_collectBalanced, rawRowCheck14102]

theorem rawRowCheck14103 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form8 = rawRow14103 := by decide +kernel

theorem rowCheck14103 : row14103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14103 := by decide +kernel

theorem rowEval14103 (x : Key → ℝ) : Integer.Sparse.eval row14103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14103, Integer.Sparse.eval_collectBalanced, rawRowCheck14103]

theorem rawRowCheck14104 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form8 = rawRow14104 := by decide +kernel

theorem rowCheck14104 : row14104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14104 := by decide +kernel

theorem rowEval14104 (x : Key → ℝ) : Integer.Sparse.eval row14104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck14104, Integer.Sparse.eval_collectBalanced, rawRowCheck14104]

theorem rawRowCheck14185 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form8 = rawRow14185 := by decide +kernel

theorem rowCheck14185 : row14185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14185 := by decide +kernel

theorem rowEval14185 (x : Key → ℝ) : Integer.Sparse.eval row14185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14185, Integer.Sparse.eval_collectBalanced, rawRowCheck14185]

theorem rawRowCheck14186 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form8 = rawRow14186 := by decide +kernel

theorem rowCheck14186 : row14186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14186 := by decide +kernel

theorem rowEval14186 (x : Key → ℝ) : Integer.Sparse.eval row14186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14186, Integer.Sparse.eval_collectBalanced, rawRowCheck14186]

theorem rawRowCheck14187 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form8 = rawRow14187 := by decide +kernel

theorem rowCheck14187 : row14187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14187 := by decide +kernel

theorem rowEval14187 (x : Key → ℝ) : Integer.Sparse.eval row14187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14187, Integer.Sparse.eval_collectBalanced, rawRowCheck14187]

theorem rawRowCheck14188 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form8 = rawRow14188 := by decide +kernel

theorem rowCheck14188 : row14188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14188 := by decide +kernel

theorem rowEval14188 (x : Key → ℝ) : Integer.Sparse.eval row14188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14188, Integer.Sparse.eval_collectBalanced, rawRowCheck14188]

theorem rawRowCheck14189 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form8 = rawRow14189 := by decide +kernel

theorem rowCheck14189 : row14189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14189 := by decide +kernel

theorem rowEval14189 (x : Key → ℝ) : Integer.Sparse.eval row14189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14189, Integer.Sparse.eval_collectBalanced, rawRowCheck14189]

theorem rawRowCheck14190 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form8 = rawRow14190 := by decide +kernel

theorem rowCheck14190 : row14190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14190 := by decide +kernel

theorem rowEval14190 (x : Key → ℝ) : Integer.Sparse.eval row14190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14190, Integer.Sparse.eval_collectBalanced, rawRowCheck14190]

theorem rawRowCheck14191 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow14191 := by decide +kernel

theorem rowCheck14191 : row14191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14191 := by decide +kernel

theorem rowEval14191 (x : Key → ℝ) : Integer.Sparse.eval row14191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14191, Integer.Sparse.eval_collectBalanced, rawRowCheck14191]

theorem rawRowCheck14192 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow14192 := by decide +kernel

theorem rowCheck14192 : row14192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14192 := by decide +kernel

theorem rowEval14192 (x : Key → ℝ) : Integer.Sparse.eval row14192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14192, Integer.Sparse.eval_collectBalanced, rawRowCheck14192]

theorem rawRowCheck14193 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow14193 := by decide +kernel

theorem rowCheck14193 : row14193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14193 := by decide +kernel

theorem rowEval14193 (x : Key → ℝ) : Integer.Sparse.eval row14193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14193, Integer.Sparse.eval_collectBalanced, rawRowCheck14193]

theorem rawRowCheck14194 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form8 = rawRow14194 := by decide +kernel

theorem rowCheck14194 : row14194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14194 := by decide +kernel

theorem rowEval14194 (x : Key → ℝ) : Integer.Sparse.eval row14194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14194, Integer.Sparse.eval_collectBalanced, rawRowCheck14194]

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

theorem rawRowCheck14761 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form8 = rawRow14761 := by decide +kernel

theorem rowCheck14761 : row14761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14761 := by decide +kernel

theorem rowEval14761 (x : Key → ℝ) : Integer.Sparse.eval row14761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14761, Integer.Sparse.eval_collectBalanced, rawRowCheck14761]

theorem rawRowCheck14762 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form8 = rawRow14762 := by decide +kernel

theorem rowCheck14762 : row14762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14762 := by decide +kernel

theorem rowEval14762 (x : Key → ℝ) : Integer.Sparse.eval row14762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14762, Integer.Sparse.eval_collectBalanced, rawRowCheck14762]

theorem rawRowCheck14763 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form8 = rawRow14763 := by decide +kernel

theorem rowCheck14763 : row14763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14763 := by decide +kernel

theorem rowEval14763 (x : Key → ℝ) : Integer.Sparse.eval row14763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14763, Integer.Sparse.eval_collectBalanced, rawRowCheck14763]

theorem rawRowCheck14764 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14764 := by decide +kernel

theorem rowCheck14764 : row14764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14764 := by decide +kernel

theorem rowEval14764 (x : Key → ℝ) : Integer.Sparse.eval row14764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14764, Integer.Sparse.eval_collectBalanced, rawRowCheck14764]

theorem rawRowCheck14765 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form8 = rawRow14765 := by decide +kernel

theorem rowCheck14765 : row14765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14765 := by decide +kernel

theorem rowEval14765 (x : Key → ℝ) : Integer.Sparse.eval row14765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14765, Integer.Sparse.eval_collectBalanced, rawRowCheck14765]

theorem rawRowCheck14766 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form8 = rawRow14766 := by decide +kernel

theorem rowCheck14766 : row14766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14766 := by decide +kernel

theorem rowEval14766 (x : Key → ℝ) : Integer.Sparse.eval row14766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14766, Integer.Sparse.eval_collectBalanced, rawRowCheck14766]

theorem rawRowCheck14767 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form8 = rawRow14767 := by decide +kernel

theorem rowCheck14767 : row14767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14767 := by decide +kernel

theorem rowEval14767 (x : Key → ℝ) : Integer.Sparse.eval row14767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14767, Integer.Sparse.eval_collectBalanced, rawRowCheck14767]

theorem rawRowCheck14768 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form8 = rawRow14768 := by decide +kernel

theorem rowCheck14768 : row14768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14768 := by decide +kernel

theorem rowEval14768 (x : Key → ℝ) : Integer.Sparse.eval row14768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14768, Integer.Sparse.eval_collectBalanced, rawRowCheck14768]

theorem rawRowCheck14769 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form8 = rawRow14769 := by decide +kernel

theorem rowCheck14769 : row14769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14769 := by decide +kernel

theorem rowEval14769 (x : Key → ℝ) : Integer.Sparse.eval row14769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14769, Integer.Sparse.eval_collectBalanced, rawRowCheck14769]

theorem rawRowCheck14770 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form8 = rawRow14770 := by decide +kernel

theorem rowCheck14770 : row14770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14770 := by decide +kernel

theorem rowEval14770 (x : Key → ℝ) : Integer.Sparse.eval row14770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14770, Integer.Sparse.eval_collectBalanced, rawRowCheck14770]

theorem rawRowCheck14771 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form8 = rawRow14771 := by decide +kernel

theorem rowCheck14771 : row14771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14771 := by decide +kernel

theorem rowEval14771 (x : Key → ℝ) : Integer.Sparse.eval row14771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14771, Integer.Sparse.eval_collectBalanced, rawRowCheck14771]

theorem rawRowCheck14772 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form8 = rawRow14772 := by decide +kernel

theorem rowCheck14772 : row14772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14772 := by decide +kernel

theorem rowEval14772 (x : Key → ℝ) : Integer.Sparse.eval row14772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14772, Integer.Sparse.eval_collectBalanced, rawRowCheck14772]

theorem rawRowCheck14773 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form8 = rawRow14773 := by decide +kernel

theorem rowCheck14773 : row14773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14773 := by decide +kernel

theorem rowEval14773 (x : Key → ℝ) : Integer.Sparse.eval row14773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14773, Integer.Sparse.eval_collectBalanced, rawRowCheck14773]

theorem rawRowCheck14774 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form8 = rawRow14774 := by decide +kernel

theorem rowCheck14774 : row14774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14774 := by decide +kernel

theorem rowEval14774 (x : Key → ℝ) : Integer.Sparse.eval row14774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14774, Integer.Sparse.eval_collectBalanced, rawRowCheck14774]

theorem rawRowCheck14775 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form8 = rawRow14775 := by decide +kernel

theorem rowCheck14775 : row14775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14775 := by decide +kernel

theorem rowEval14775 (x : Key → ℝ) : Integer.Sparse.eval row14775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14775, Integer.Sparse.eval_collectBalanced, rawRowCheck14775]

theorem rawRowCheck14776 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form8 = rawRow14776 := by decide +kernel

theorem rowCheck14776 : row14776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14776 := by decide +kernel

theorem rowEval14776 (x : Key → ℝ) : Integer.Sparse.eval row14776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14776, Integer.Sparse.eval_collectBalanced, rawRowCheck14776]

theorem rawRowCheck14777 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14777 := by decide +kernel

theorem rowCheck14777 : row14777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14777 := by decide +kernel

theorem rowEval14777 (x : Key → ℝ) : Integer.Sparse.eval row14777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14777, Integer.Sparse.eval_collectBalanced, rawRowCheck14777]

theorem rawRowCheck14778 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form8 = rawRow14778 := by decide +kernel

theorem rowCheck14778 : row14778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14778 := by decide +kernel

theorem rowEval14778 (x : Key → ℝ) : Integer.Sparse.eval row14778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14778, Integer.Sparse.eval_collectBalanced, rawRowCheck14778]

theorem rawRowCheck14779 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form8 = rawRow14779 := by decide +kernel

theorem rowCheck14779 : row14779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14779 := by decide +kernel

theorem rowEval14779 (x : Key → ℝ) : Integer.Sparse.eval row14779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14779, Integer.Sparse.eval_collectBalanced, rawRowCheck14779]

theorem rawRowCheck14780 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form8 = rawRow14780 := by decide +kernel

theorem rowCheck14780 : row14780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14780 := by decide +kernel

theorem rowEval14780 (x : Key → ℝ) : Integer.Sparse.eval row14780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14780, Integer.Sparse.eval_collectBalanced, rawRowCheck14780]

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

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14761 x
  · exact rowEval14762 x
  · exact rowEval14763 x
  · exact rowEval14764 x
  · exact rowEval14765 x
  · exact rowEval14766 x
  · exact rowEval14767 x
  · exact rowEval14768 x
  · exact rowEval14769 x
  · exact rowEval14770 x
  · exact rowEval14771 x
  · exact rowEval14772 x
  · exact rowEval14773 x
  · exact rowEval14774 x
  · exact rowEval14775 x
  · exact rowEval14776 x
  · exact rowEval14777 x
  · exact rowEval14778 x
  · exact rowEval14779 x
  · exact rowEval14780 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

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

theorem rawRowCheck13945 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13945 := by decide +kernel

theorem rowCheck13945 : row13945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13945 := by decide +kernel

theorem rowEval13945 (x : Key → ℝ) : Integer.Sparse.eval row13945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13945, Integer.Sparse.eval_collectBalanced, rawRowCheck13945]

theorem rawRowCheck13946 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13946 := by decide +kernel

theorem rowCheck13946 : row13946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13946 := by decide +kernel

theorem rowEval13946 (x : Key → ℝ) : Integer.Sparse.eval row13946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13946, Integer.Sparse.eval_collectBalanced, rawRowCheck13946]

theorem rawRowCheck13947 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13947 := by decide +kernel

theorem rowCheck13947 : row13947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13947 := by decide +kernel

theorem rowEval13947 (x : Key → ℝ) : Integer.Sparse.eval row13947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13947, Integer.Sparse.eval_collectBalanced, rawRowCheck13947]

theorem rawRowCheck13948 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13948 := by decide +kernel

theorem rowCheck13948 : row13948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13948 := by decide +kernel

theorem rowEval13948 (x : Key → ℝ) : Integer.Sparse.eval row13948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13948, Integer.Sparse.eval_collectBalanced, rawRowCheck13948]

theorem rawRowCheck13949 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13949 := by decide +kernel

theorem rowCheck13949 : row13949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13949 := by decide +kernel

theorem rowEval13949 (x : Key → ℝ) : Integer.Sparse.eval row13949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13949, Integer.Sparse.eval_collectBalanced, rawRowCheck13949]

theorem rawRowCheck13950 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13950 := by decide +kernel

theorem rowCheck13950 : row13950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13950 := by decide +kernel

theorem rowEval13950 (x : Key → ℝ) : Integer.Sparse.eval row13950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13950, Integer.Sparse.eval_collectBalanced, rawRowCheck13950]

theorem rawRowCheck13951 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13951 := by decide +kernel

theorem rowCheck13951 : row13951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13951 := by decide +kernel

theorem rowEval13951 (x : Key → ℝ) : Integer.Sparse.eval row13951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13951, Integer.Sparse.eval_collectBalanced, rawRowCheck13951]

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

theorem rawRowCheck17491 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form8 = rawRow17491 := by decide +kernel

theorem rowCheck17491 : row17491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17491 := by decide +kernel

theorem rowEval17491 (x : Key → ℝ) : Integer.Sparse.eval row17491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17491, Integer.Sparse.eval_collectBalanced, rawRowCheck17491]

theorem rawRowCheck17492 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form8 = rawRow17492 := by decide +kernel

theorem rowCheck17492 : row17492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17492 := by decide +kernel

theorem rowEval17492 (x : Key → ℝ) : Integer.Sparse.eval row17492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17492, Integer.Sparse.eval_collectBalanced, rawRowCheck17492]

theorem rawRowCheck17493 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form8 = rawRow17493 := by decide +kernel

theorem rowCheck17493 : row17493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17493 := by decide +kernel

theorem rowEval17493 (x : Key → ℝ) : Integer.Sparse.eval row17493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17493, Integer.Sparse.eval_collectBalanced, rawRowCheck17493]

theorem rawRowCheck17494 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form8 = rawRow17494 := by decide +kernel

theorem rowCheck17494 : row17494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17494 := by decide +kernel

theorem rowEval17494 (x : Key → ℝ) : Integer.Sparse.eval row17494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17494, Integer.Sparse.eval_collectBalanced, rawRowCheck17494]

theorem rawRowCheck17495 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form8 = rawRow17495 := by decide +kernel

theorem rowCheck17495 : row17495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17495 := by decide +kernel

theorem rowEval17495 (x : Key → ℝ) : Integer.Sparse.eval row17495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17495, Integer.Sparse.eval_collectBalanced, rawRowCheck17495]

theorem rawRowCheck17496 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form8 = rawRow17496 := by decide +kernel

theorem rowCheck17496 : row17496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17496 := by decide +kernel

theorem rowEval17496 (x : Key → ℝ) : Integer.Sparse.eval row17496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17496, Integer.Sparse.eval_collectBalanced, rawRowCheck17496]

theorem rawRowCheck17497 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form8 = rawRow17497 := by decide +kernel

theorem rowCheck17497 : row17497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17497 := by decide +kernel

theorem rowEval17497 (x : Key → ℝ) : Integer.Sparse.eval row17497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17497, Integer.Sparse.eval_collectBalanced, rawRowCheck17497]

theorem rawRowCheck17498 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form8 = rawRow17498 := by decide +kernel

theorem rowCheck17498 : row17498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17498 := by decide +kernel

theorem rowEval17498 (x : Key → ℝ) : Integer.Sparse.eval row17498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17498, Integer.Sparse.eval_collectBalanced, rawRowCheck17498]

theorem rawRowCheck17499 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form8 = rawRow17499 := by decide +kernel

theorem rowCheck17499 : row17499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17499 := by decide +kernel

theorem rowEval17499 (x : Key → ℝ) : Integer.Sparse.eval row17499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17499, Integer.Sparse.eval_collectBalanced, rawRowCheck17499]

theorem rawRowCheck17500 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form8 = rawRow17500 := by decide +kernel

theorem rowCheck17500 : row17500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17500 := by decide +kernel

theorem rowEval17500 (x : Key → ℝ) : Integer.Sparse.eval row17500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17500, Integer.Sparse.eval_collectBalanced, rawRowCheck17500]

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

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval17491 x
  · exact rowEval17492 x
  · exact rowEval17493 x
  · exact rowEval17494 x
  · exact rowEval17495 x
  · exact rowEval17496 x
  · exact rowEval17497 x
  · exact rowEval17498 x
  · exact rowEval17499 x
  · exact rowEval17500 x

theorem entryEval19_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

end MUB6.Certificate.GramEntries.Block4

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

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18149 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form8 = rawRow18149 := by decide +kernel

theorem rowCheck18149 : row18149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18149 := by decide +kernel

theorem rowEval18149 (x : Key → ℝ) : Integer.Sparse.eval row18149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18149, Integer.Sparse.eval_collectBalanced, rawRowCheck18149]

theorem rawRowCheck18150 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form8 = rawRow18150 := by decide +kernel

theorem rowCheck18150 : row18150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18150 := by decide +kernel

theorem rowEval18150 (x : Key → ℝ) : Integer.Sparse.eval row18150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18150, Integer.Sparse.eval_collectBalanced, rawRowCheck18150]

theorem rawRowCheck18151 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form8 = rawRow18151 := by decide +kernel

theorem rowCheck18151 : row18151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18151 := by decide +kernel

theorem rowEval18151 (x : Key → ℝ) : Integer.Sparse.eval row18151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18151, Integer.Sparse.eval_collectBalanced, rawRowCheck18151]

theorem rawRowCheck18152 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form8 = rawRow18152 := by decide +kernel

theorem rowCheck18152 : row18152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18152 := by decide +kernel

theorem rowEval18152 (x : Key → ℝ) : Integer.Sparse.eval row18152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18152, Integer.Sparse.eval_collectBalanced, rawRowCheck18152]

theorem rawRowCheck18153 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form8 = rawRow18153 := by decide +kernel

theorem rowCheck18153 : row18153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18153 := by decide +kernel

theorem rowEval18153 (x : Key → ℝ) : Integer.Sparse.eval row18153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18153, Integer.Sparse.eval_collectBalanced, rawRowCheck18153]

theorem rawRowCheck18154 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form8 = rawRow18154 := by decide +kernel

theorem rowCheck18154 : row18154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18154 := by decide +kernel

theorem rowEval18154 (x : Key → ℝ) : Integer.Sparse.eval row18154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18154, Integer.Sparse.eval_collectBalanced, rawRowCheck18154]

theorem rawRowCheck18155 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form8 = rawRow18155 := by decide +kernel

theorem rowCheck18155 : row18155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18155 := by decide +kernel

theorem rowEval18155 (x : Key → ℝ) : Integer.Sparse.eval row18155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18155, Integer.Sparse.eval_collectBalanced, rawRowCheck18155]

theorem rawRowCheck18156 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form8 = rawRow18156 := by decide +kernel

theorem rowCheck18156 : row18156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18156 := by decide +kernel

theorem rowEval18156 (x : Key → ℝ) : Integer.Sparse.eval row18156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18156, Integer.Sparse.eval_collectBalanced, rawRowCheck18156]

theorem rawRowCheck18157 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form8 = rawRow18157 := by decide +kernel

theorem rowCheck18157 : row18157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18157 := by decide +kernel

theorem rowEval18157 (x : Key → ℝ) : Integer.Sparse.eval row18157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18157, Integer.Sparse.eval_collectBalanced, rawRowCheck18157]

theorem rawRowCheck18158 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow18158 := by decide +kernel

theorem rowCheck18158 : row18158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18158 := by decide +kernel

theorem rowEval18158 (x : Key → ℝ) : Integer.Sparse.eval row18158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18158, Integer.Sparse.eval_collectBalanced, rawRowCheck18158]

theorem rawRowCheck18159 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow18159 := by decide +kernel

theorem rowCheck18159 : row18159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18159 := by decide +kernel

theorem rowEval18159 (x : Key → ℝ) : Integer.Sparse.eval row18159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18159, Integer.Sparse.eval_collectBalanced, rawRowCheck18159]

theorem rawRowCheck18160 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow18160 := by decide +kernel

theorem rowCheck18160 : row18160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18160 := by decide +kernel

theorem rowEval18160 (x : Key → ℝ) : Integer.Sparse.eval row18160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18160, Integer.Sparse.eval_collectBalanced, rawRowCheck18160]

theorem rawRowCheck18161 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form8 = rawRow18161 := by decide +kernel

theorem rowCheck18161 : row18161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18161 := by decide +kernel

theorem rowEval18161 (x : Key → ℝ) : Integer.Sparse.eval row18161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18161, Integer.Sparse.eval_collectBalanced, rawRowCheck18161]

theorem rawRowCheck18162 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form8 = rawRow18162 := by decide +kernel

theorem rowCheck18162 : row18162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18162 := by decide +kernel

theorem rowEval18162 (x : Key → ℝ) : Integer.Sparse.eval row18162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18162, Integer.Sparse.eval_collectBalanced, rawRowCheck18162]

theorem rawRowCheck18163 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form8 = rawRow18163 := by decide +kernel

theorem rowCheck18163 : row18163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18163 := by decide +kernel

theorem rowEval18163 (x : Key → ℝ) : Integer.Sparse.eval row18163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18163, Integer.Sparse.eval_collectBalanced, rawRowCheck18163]

theorem rawRowCheck18164 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form8 = rawRow18164 := by decide +kernel

theorem rowCheck18164 : row18164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18164 := by decide +kernel

theorem rowEval18164 (x : Key → ℝ) : Integer.Sparse.eval row18164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18164, Integer.Sparse.eval_collectBalanced, rawRowCheck18164]

theorem rawRowCheck18165 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow18165 := by decide +kernel

theorem rowCheck18165 : row18165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18165 := by decide +kernel

theorem rowEval18165 (x : Key → ℝ) : Integer.Sparse.eval row18165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18165, Integer.Sparse.eval_collectBalanced, rawRowCheck18165]

theorem rawRowCheck18166 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow18166 := by decide +kernel

theorem rowCheck18166 : row18166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18166 := by decide +kernel

theorem rowEval18166 (x : Key → ℝ) : Integer.Sparse.eval row18166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18166, Integer.Sparse.eval_collectBalanced, rawRowCheck18166]

theorem rawRowCheck18167 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow18167 := by decide +kernel

theorem rowCheck18167 : row18167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18167 := by decide +kernel

theorem rowEval18167 (x : Key → ℝ) : Integer.Sparse.eval row18167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18167, Integer.Sparse.eval_collectBalanced, rawRowCheck18167]

theorem rawRowCheck18168 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form8 = rawRow18168 := by decide +kernel

theorem rowCheck18168 : row18168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18168 := by decide +kernel

theorem rowEval18168 (x : Key → ℝ) : Integer.Sparse.eval row18168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18168, Integer.Sparse.eval_collectBalanced, rawRowCheck18168]

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

theorem entryCheck21_8 : entry21_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_8 k)) := by decide +kernel

theorem rowsSound21_8 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval18149 x
  · exact rowEval18150 x
  · exact rowEval18151 x
  · exact rowEval18152 x
  · exact rowEval18153 x
  · exact rowEval18154 x
  · exact rowEval18155 x
  · exact rowEval18156 x
  · exact rowEval18157 x
  · exact rowEval18158 x
  · exact rowEval18159 x
  · exact rowEval18160 x
  · exact rowEval18161 x
  · exact rowEval18162 x
  · exact rowEval18163 x
  · exact rowEval18164 x
  · exact rowEval18165 x
  · exact rowEval18166 x
  · exact rowEval18167 x
  · exact rowEval18168 x

theorem entryEval21_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_8 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck21_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_8]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13952 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13952 := by decide +kernel

theorem rowCheck13952 : row13952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13952 := by decide +kernel

theorem rowEval13952 (x : Key → ℝ) : Integer.Sparse.eval row13952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13952, Integer.Sparse.eval_collectBalanced, rawRowCheck13952]

theorem rawRowCheck13953 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13953 := by decide +kernel

theorem rowCheck13953 : row13953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13953 := by decide +kernel

theorem rowEval13953 (x : Key → ℝ) : Integer.Sparse.eval row13953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13953, Integer.Sparse.eval_collectBalanced, rawRowCheck13953]

theorem rawRowCheck13954 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13954 := by decide +kernel

theorem rowCheck13954 : row13954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13954 := by decide +kernel

theorem rowEval13954 (x : Key → ℝ) : Integer.Sparse.eval row13954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13954, Integer.Sparse.eval_collectBalanced, rawRowCheck13954]

theorem rawRowCheck13955 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13955 := by decide +kernel

theorem rowCheck13955 : row13955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13955 := by decide +kernel

theorem rowEval13955 (x : Key → ℝ) : Integer.Sparse.eval row13955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13955, Integer.Sparse.eval_collectBalanced, rawRowCheck13955]

theorem rawRowCheck13956 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13956 := by decide +kernel

theorem rowCheck13956 : row13956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13956 := by decide +kernel

theorem rowEval13956 (x : Key → ℝ) : Integer.Sparse.eval row13956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13956, Integer.Sparse.eval_collectBalanced, rawRowCheck13956]

theorem rawRowCheck13957 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13957 := by decide +kernel

theorem rowCheck13957 : row13957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13957 := by decide +kernel

theorem rowEval13957 (x : Key → ℝ) : Integer.Sparse.eval row13957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13957, Integer.Sparse.eval_collectBalanced, rawRowCheck13957]

theorem rawRowCheck13958 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13958 := by decide +kernel

theorem rowCheck13958 : row13958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13958 := by decide +kernel

theorem rowEval13958 (x : Key → ℝ) : Integer.Sparse.eval row13958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13958, Integer.Sparse.eval_collectBalanced, rawRowCheck13958]

theorem rawRowCheck13959 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13959 := by decide +kernel

theorem rowCheck13959 : row13959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13959 := by decide +kernel

theorem rowEval13959 (x : Key → ℝ) : Integer.Sparse.eval row13959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13959, Integer.Sparse.eval_collectBalanced, rawRowCheck13959]

theorem rawRowCheck13960 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13960 := by decide +kernel

theorem rowCheck13960 : row13960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13960 := by decide +kernel

theorem rowEval13960 (x : Key → ℝ) : Integer.Sparse.eval row13960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13960, Integer.Sparse.eval_collectBalanced, rawRowCheck13960]

theorem rawRowCheck13961 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13961 := by decide +kernel

theorem rowCheck13961 : row13961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13961 := by decide +kernel

theorem rowEval13961 (x : Key → ℝ) : Integer.Sparse.eval row13961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13961, Integer.Sparse.eval_collectBalanced, rawRowCheck13961]

theorem rawRowCheck13962 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13962 := by decide +kernel

theorem rowCheck13962 : row13962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13962 := by decide +kernel

theorem rowEval13962 (x : Key → ℝ) : Integer.Sparse.eval row13962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13962, Integer.Sparse.eval_collectBalanced, rawRowCheck13962]

theorem rawRowCheck13963 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13963 := by decide +kernel

theorem rowCheck13963 : row13963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13963 := by decide +kernel

theorem rowEval13963 (x : Key → ℝ) : Integer.Sparse.eval row13963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13963, Integer.Sparse.eval_collectBalanced, rawRowCheck13963]

theorem rawRowCheck13964 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13964 := by decide +kernel

theorem rowCheck13964 : row13964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13964 := by decide +kernel

theorem rowEval13964 (x : Key → ℝ) : Integer.Sparse.eval row13964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13964, Integer.Sparse.eval_collectBalanced, rawRowCheck13964]

theorem rawRowCheck13965 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13965 := by decide +kernel

theorem rowCheck13965 : row13965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13965 := by decide +kernel

theorem rowEval13965 (x : Key → ℝ) : Integer.Sparse.eval row13965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13965, Integer.Sparse.eval_collectBalanced, rawRowCheck13965]

theorem rawRowCheck13966 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13966 := by decide +kernel

theorem rowCheck13966 : row13966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13966 := by decide +kernel

theorem rowEval13966 (x : Key → ℝ) : Integer.Sparse.eval row13966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13966, Integer.Sparse.eval_collectBalanced, rawRowCheck13966]

theorem rawRowCheck13967 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13967 := by decide +kernel

theorem rowCheck13967 : row13967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13967 := by decide +kernel

theorem rowEval13967 (x : Key → ℝ) : Integer.Sparse.eval row13967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13967, Integer.Sparse.eval_collectBalanced, rawRowCheck13967]

theorem rawRowCheck13968 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13968 := by decide +kernel

theorem rowCheck13968 : row13968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13968 := by decide +kernel

theorem rowEval13968 (x : Key → ℝ) : Integer.Sparse.eval row13968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13968, Integer.Sparse.eval_collectBalanced, rawRowCheck13968]

theorem rawRowCheck13969 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13969 := by decide +kernel

theorem rowCheck13969 : row13969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13969 := by decide +kernel

theorem rowEval13969 (x : Key → ℝ) : Integer.Sparse.eval row13969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13969, Integer.Sparse.eval_collectBalanced, rawRowCheck13969]

theorem rawRowCheck13970 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13970 := by decide +kernel

theorem rowCheck13970 : row13970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13970 := by decide +kernel

theorem rowEval13970 (x : Key → ℝ) : Integer.Sparse.eval row13970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13970, Integer.Sparse.eval_collectBalanced, rawRowCheck13970]

theorem rawRowCheck13971 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13971 := by decide +kernel

theorem rowCheck13971 : row13971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13971 := by decide +kernel

theorem rowEval13971 (x : Key → ℝ) : Integer.Sparse.eval row13971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13971, Integer.Sparse.eval_collectBalanced, rawRowCheck13971]

theorem rawRowCheck13972 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13972 := by decide +kernel

theorem rowCheck13972 : row13972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13972 := by decide +kernel

theorem rowEval13972 (x : Key → ℝ) : Integer.Sparse.eval row13972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13972, Integer.Sparse.eval_collectBalanced, rawRowCheck13972]

theorem rawRowCheck13973 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13973 := by decide +kernel

theorem rowCheck13973 : row13973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13973 := by decide +kernel

theorem rowEval13973 (x : Key → ℝ) : Integer.Sparse.eval row13973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13973, Integer.Sparse.eval_collectBalanced, rawRowCheck13973]

theorem rawRowCheck13974 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13974 := by decide +kernel

theorem rowCheck13974 : row13974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13974 := by decide +kernel

theorem rowEval13974 (x : Key → ℝ) : Integer.Sparse.eval row13974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13974, Integer.Sparse.eval_collectBalanced, rawRowCheck13974]

theorem rawRowCheck13975 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13975 := by decide +kernel

theorem rowCheck13975 : row13975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13975 := by decide +kernel

theorem rowEval13975 (x : Key → ℝ) : Integer.Sparse.eval row13975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13975, Integer.Sparse.eval_collectBalanced, rawRowCheck13975]

theorem rawRowCheck13976 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13976 := by decide +kernel

theorem rowCheck13976 : row13976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13976 := by decide +kernel

theorem rowEval13976 (x : Key → ℝ) : Integer.Sparse.eval row13976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13976, Integer.Sparse.eval_collectBalanced, rawRowCheck13976]

theorem rawRowCheck13977 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13977 := by decide +kernel

theorem rowCheck13977 : row13977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13977 := by decide +kernel

theorem rowEval13977 (x : Key → ℝ) : Integer.Sparse.eval row13977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13977, Integer.Sparse.eval_collectBalanced, rawRowCheck13977]

theorem rawRowCheck13978 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13978 := by decide +kernel

theorem rowCheck13978 : row13978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13978 := by decide +kernel

theorem rowEval13978 (x : Key → ℝ) : Integer.Sparse.eval row13978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13978, Integer.Sparse.eval_collectBalanced, rawRowCheck13978]

theorem rawRowCheck13979 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13979 := by decide +kernel

theorem rowCheck13979 : row13979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13979 := by decide +kernel

theorem rowEval13979 (x : Key → ℝ) : Integer.Sparse.eval row13979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13979, Integer.Sparse.eval_collectBalanced, rawRowCheck13979]

theorem rawRowCheck13980 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13980 := by decide +kernel

theorem rowCheck13980 : row13980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13980 := by decide +kernel

theorem rowEval13980 (x : Key → ℝ) : Integer.Sparse.eval row13980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13980, Integer.Sparse.eval_collectBalanced, rawRowCheck13980]

theorem rawRowCheck13981 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13981 := by decide +kernel

theorem rowCheck13981 : row13981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13981 := by decide +kernel

theorem rowEval13981 (x : Key → ℝ) : Integer.Sparse.eval row13981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13981, Integer.Sparse.eval_collectBalanced, rawRowCheck13981]

theorem rawRowCheck13982 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13982 := by decide +kernel

theorem rowCheck13982 : row13982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13982 := by decide +kernel

theorem rowEval13982 (x : Key → ℝ) : Integer.Sparse.eval row13982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13982, Integer.Sparse.eval_collectBalanced, rawRowCheck13982]

theorem rawRowCheck13983 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13983 := by decide +kernel

theorem rowCheck13983 : row13983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13983 := by decide +kernel

theorem rowEval13983 (x : Key → ℝ) : Integer.Sparse.eval row13983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13983, Integer.Sparse.eval_collectBalanced, rawRowCheck13983]

theorem rawRowCheck13984 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13984 := by decide +kernel

theorem rowCheck13984 : row13984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13984 := by decide +kernel

theorem rowEval13984 (x : Key → ℝ) : Integer.Sparse.eval row13984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13984, Integer.Sparse.eval_collectBalanced, rawRowCheck13984]

theorem rawRowCheck13985 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13985 := by decide +kernel

theorem rowCheck13985 : row13985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13985 := by decide +kernel

theorem rowEval13985 (x : Key → ℝ) : Integer.Sparse.eval row13985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13985, Integer.Sparse.eval_collectBalanced, rawRowCheck13985]

theorem rawRowCheck13986 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13986 := by decide +kernel

theorem rowCheck13986 : row13986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13986 := by decide +kernel

theorem rowEval13986 (x : Key → ℝ) : Integer.Sparse.eval row13986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13986, Integer.Sparse.eval_collectBalanced, rawRowCheck13986]

theorem rawRowCheck13987 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13987 := by decide +kernel

theorem rowCheck13987 : row13987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13987 := by decide +kernel

theorem rowEval13987 (x : Key → ℝ) : Integer.Sparse.eval row13987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13987, Integer.Sparse.eval_collectBalanced, rawRowCheck13987]

theorem rawRowCheck13988 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13988 := by decide +kernel

theorem rowCheck13988 : row13988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13988 := by decide +kernel

theorem rowEval13988 (x : Key → ℝ) : Integer.Sparse.eval row13988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13988, Integer.Sparse.eval_collectBalanced, rawRowCheck13988]

theorem rawRowCheck13989 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13989 := by decide +kernel

theorem rowCheck13989 : row13989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13989 := by decide +kernel

theorem rowEval13989 (x : Key → ℝ) : Integer.Sparse.eval row13989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13989, Integer.Sparse.eval_collectBalanced, rawRowCheck13989]

theorem rawRowCheck13990 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13990 := by decide +kernel

theorem rowCheck13990 : row13990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13990 := by decide +kernel

theorem rowEval13990 (x : Key → ℝ) : Integer.Sparse.eval row13990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13990, Integer.Sparse.eval_collectBalanced, rawRowCheck13990]

theorem rawRowCheck13991 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13991 := by decide +kernel

theorem rowCheck13991 : row13991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13991 := by decide +kernel

theorem rowEval13991 (x : Key → ℝ) : Integer.Sparse.eval row13991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13991, Integer.Sparse.eval_collectBalanced, rawRowCheck13991]

theorem rawRowCheck13992 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13992 := by decide +kernel

theorem rowCheck13992 : row13992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13992 := by decide +kernel

theorem rowEval13992 (x : Key → ℝ) : Integer.Sparse.eval row13992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13992, Integer.Sparse.eval_collectBalanced, rawRowCheck13992]

theorem rawRowCheck13993 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13993 := by decide +kernel

theorem rowCheck13993 : row13993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13993 := by decide +kernel

theorem rowEval13993 (x : Key → ℝ) : Integer.Sparse.eval row13993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13993, Integer.Sparse.eval_collectBalanced, rawRowCheck13993]

theorem rawRowCheck13994 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13994 := by decide +kernel

theorem rowCheck13994 : row13994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13994 := by decide +kernel

theorem rowEval13994 (x : Key → ℝ) : Integer.Sparse.eval row13994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13994, Integer.Sparse.eval_collectBalanced, rawRowCheck13994]

theorem rawRowCheck13995 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13995 := by decide +kernel

theorem rowCheck13995 : row13995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13995 := by decide +kernel

theorem rowEval13995 (x : Key → ℝ) : Integer.Sparse.eval row13995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13995, Integer.Sparse.eval_collectBalanced, rawRowCheck13995]

theorem rawRowCheck13996 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13996 := by decide +kernel

theorem rowCheck13996 : row13996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13996 := by decide +kernel

theorem rowEval13996 (x : Key → ℝ) : Integer.Sparse.eval row13996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13996, Integer.Sparse.eval_collectBalanced, rawRowCheck13996]

theorem rawRowCheck13997 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13997 := by decide +kernel

theorem rowCheck13997 : row13997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13997 := by decide +kernel

theorem rowEval13997 (x : Key → ℝ) : Integer.Sparse.eval row13997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13997, Integer.Sparse.eval_collectBalanced, rawRowCheck13997]

theorem rawRowCheck13998 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13998 := by decide +kernel

theorem rowCheck13998 : row13998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13998 := by decide +kernel

theorem rowEval13998 (x : Key → ℝ) : Integer.Sparse.eval row13998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13998, Integer.Sparse.eval_collectBalanced, rawRowCheck13998]

theorem rawRowCheck13999 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13999 := by decide +kernel

theorem rowCheck13999 : row13999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13999 := by decide +kernel

theorem rowEval13999 (x : Key → ℝ) : Integer.Sparse.eval row13999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13999, Integer.Sparse.eval_collectBalanced, rawRowCheck13999]

theorem rawRowCheck14000 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow14000 := by decide +kernel

theorem rowCheck14000 : row14000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14000 := by decide +kernel

theorem rowEval14000 (x : Key → ℝ) : Integer.Sparse.eval row14000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14000, Integer.Sparse.eval_collectBalanced, rawRowCheck14000]

theorem rawRowCheck14001 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3 = rawRow14001 := by decide +kernel

theorem rowCheck14001 : row14001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14001 := by decide +kernel

theorem rowEval14001 (x : Key → ℝ) : Integer.Sparse.eval row14001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14001, Integer.Sparse.eval_collectBalanced, rawRowCheck14001]

theorem rawRowCheck14002 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3 = rawRow14002 := by decide +kernel

theorem rowCheck14002 : row14002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14002 := by decide +kernel

theorem rowEval14002 (x : Key → ℝ) : Integer.Sparse.eval row14002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14002, Integer.Sparse.eval_collectBalanced, rawRowCheck14002]

theorem rawRowCheck14003 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3 = rawRow14003 := by decide +kernel

theorem rowCheck14003 : row14003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14003 := by decide +kernel

theorem rowEval14003 (x : Key → ℝ) : Integer.Sparse.eval row14003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14003, Integer.Sparse.eval_collectBalanced, rawRowCheck14003]

theorem rawRowCheck14004 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3 = rawRow14004 := by decide +kernel

theorem rowCheck14004 : row14004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14004 := by decide +kernel

theorem rowEval14004 (x : Key → ℝ) : Integer.Sparse.eval row14004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14004, Integer.Sparse.eval_collectBalanced, rawRowCheck14004]

theorem rawRowCheck14005 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14005 := by decide +kernel

theorem rowCheck14005 : row14005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14005 := by decide +kernel

theorem rowEval14005 (x : Key → ℝ) : Integer.Sparse.eval row14005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14005, Integer.Sparse.eval_collectBalanced, rawRowCheck14005]

theorem rawRowCheck14006 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14006 := by decide +kernel

theorem rowCheck14006 : row14006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14006 := by decide +kernel

theorem rowEval14006 (x : Key → ℝ) : Integer.Sparse.eval row14006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14006, Integer.Sparse.eval_collectBalanced, rawRowCheck14006]

theorem rawRowCheck14007 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14007 := by decide +kernel

theorem rowCheck14007 : row14007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14007 := by decide +kernel

theorem rowEval14007 (x : Key → ℝ) : Integer.Sparse.eval row14007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14007, Integer.Sparse.eval_collectBalanced, rawRowCheck14007]

theorem rawRowCheck14008 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14008 := by decide +kernel

theorem rowCheck14008 : row14008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14008 := by decide +kernel

theorem rowEval14008 (x : Key → ℝ) : Integer.Sparse.eval row14008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14008, Integer.Sparse.eval_collectBalanced, rawRowCheck14008]

theorem rawRowCheck14009 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14009 := by decide +kernel

theorem rowCheck14009 : row14009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14009 := by decide +kernel

theorem rowEval14009 (x : Key → ℝ) : Integer.Sparse.eval row14009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14009, Integer.Sparse.eval_collectBalanced, rawRowCheck14009]

theorem rawRowCheck14010 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14010 := by decide +kernel

theorem rowCheck14010 : row14010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14010 := by decide +kernel

theorem rowEval14010 (x : Key → ℝ) : Integer.Sparse.eval row14010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14010, Integer.Sparse.eval_collectBalanced, rawRowCheck14010]

theorem rawRowCheck14011 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14011 := by decide +kernel

theorem rowCheck14011 : row14011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14011 := by decide +kernel

theorem rowEval14011 (x : Key → ℝ) : Integer.Sparse.eval row14011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14011, Integer.Sparse.eval_collectBalanced, rawRowCheck14011]

theorem rawRowCheck14012 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14012 := by decide +kernel

theorem rowCheck14012 : row14012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14012 := by decide +kernel

theorem rowEval14012 (x : Key → ℝ) : Integer.Sparse.eval row14012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14012, Integer.Sparse.eval_collectBalanced, rawRowCheck14012]

theorem rawRowCheck14013 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14013 := by decide +kernel

theorem rowCheck14013 : row14013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14013 := by decide +kernel

theorem rowEval14013 (x : Key → ℝ) : Integer.Sparse.eval row14013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14013, Integer.Sparse.eval_collectBalanced, rawRowCheck14013]

theorem rawRowCheck14014 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14014 := by decide +kernel

theorem rowCheck14014 : row14014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14014 := by decide +kernel

theorem rowEval14014 (x : Key → ℝ) : Integer.Sparse.eval row14014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14014, Integer.Sparse.eval_collectBalanced, rawRowCheck14014]

theorem rawRowCheck14015 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14015 := by decide +kernel

theorem rowCheck14015 : row14015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14015 := by decide +kernel

theorem rowEval14015 (x : Key → ℝ) : Integer.Sparse.eval row14015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14015, Integer.Sparse.eval_collectBalanced, rawRowCheck14015]

theorem rawRowCheck14016 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14016 := by decide +kernel

theorem rowCheck14016 : row14016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14016 := by decide +kernel

theorem rowEval14016 (x : Key → ℝ) : Integer.Sparse.eval row14016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14016, Integer.Sparse.eval_collectBalanced, rawRowCheck14016]

theorem rawRowCheck14017 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14017 := by decide +kernel

theorem rowCheck14017 : row14017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14017 := by decide +kernel

theorem rowEval14017 (x : Key → ℝ) : Integer.Sparse.eval row14017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14017, Integer.Sparse.eval_collectBalanced, rawRowCheck14017]

theorem rawRowCheck14018 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14018 := by decide +kernel

theorem rowCheck14018 : row14018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14018 := by decide +kernel

theorem rowEval14018 (x : Key → ℝ) : Integer.Sparse.eval row14018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14018, Integer.Sparse.eval_collectBalanced, rawRowCheck14018]

theorem rawRowCheck14019 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14019 := by decide +kernel

theorem rowCheck14019 : row14019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14019 := by decide +kernel

theorem rowEval14019 (x : Key → ℝ) : Integer.Sparse.eval row14019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14019, Integer.Sparse.eval_collectBalanced, rawRowCheck14019]

theorem rawRowCheck14020 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14020 := by decide +kernel

theorem rowCheck14020 : row14020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14020 := by decide +kernel

theorem rowEval14020 (x : Key → ℝ) : Integer.Sparse.eval row14020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14020, Integer.Sparse.eval_collectBalanced, rawRowCheck14020]

theorem rawRowCheck14021 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14021 := by decide +kernel

theorem rowCheck14021 : row14021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14021 := by decide +kernel

theorem rowEval14021 (x : Key → ℝ) : Integer.Sparse.eval row14021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14021, Integer.Sparse.eval_collectBalanced, rawRowCheck14021]

theorem rawRowCheck14022 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14022 := by decide +kernel

theorem rowCheck14022 : row14022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14022 := by decide +kernel

theorem rowEval14022 (x : Key → ℝ) : Integer.Sparse.eval row14022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14022, Integer.Sparse.eval_collectBalanced, rawRowCheck14022]

theorem rawRowCheck14023 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14023 := by decide +kernel

theorem rowCheck14023 : row14023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14023 := by decide +kernel

theorem rowEval14023 (x : Key → ℝ) : Integer.Sparse.eval row14023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14023, Integer.Sparse.eval_collectBalanced, rawRowCheck14023]

theorem rawRowCheck14024 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14024 := by decide +kernel

theorem rowCheck14024 : row14024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14024 := by decide +kernel

theorem rowEval14024 (x : Key → ℝ) : Integer.Sparse.eval row14024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14024, Integer.Sparse.eval_collectBalanced, rawRowCheck14024]

theorem rawRowCheck14025 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14025 := by decide +kernel

theorem rowCheck14025 : row14025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14025 := by decide +kernel

theorem rowEval14025 (x : Key → ℝ) : Integer.Sparse.eval row14025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14025, Integer.Sparse.eval_collectBalanced, rawRowCheck14025]

theorem rawRowCheck14026 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14026 := by decide +kernel

theorem rowCheck14026 : row14026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14026 := by decide +kernel

theorem rowEval14026 (x : Key → ℝ) : Integer.Sparse.eval row14026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14026, Integer.Sparse.eval_collectBalanced, rawRowCheck14026]

theorem rawRowCheck14027 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14027 := by decide +kernel

theorem rowCheck14027 : row14027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14027 := by decide +kernel

theorem rowEval14027 (x : Key → ℝ) : Integer.Sparse.eval row14027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14027, Integer.Sparse.eval_collectBalanced, rawRowCheck14027]

theorem rawRowCheck14028 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14028 := by decide +kernel

theorem rowCheck14028 : row14028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14028 := by decide +kernel

theorem rowEval14028 (x : Key → ℝ) : Integer.Sparse.eval row14028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14028, Integer.Sparse.eval_collectBalanced, rawRowCheck14028]

theorem rawRowCheck14029 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14029 := by decide +kernel

theorem rowCheck14029 : row14029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14029 := by decide +kernel

theorem rowEval14029 (x : Key → ℝ) : Integer.Sparse.eval row14029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14029, Integer.Sparse.eval_collectBalanced, rawRowCheck14029]

theorem rawRowCheck14030 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14030 := by decide +kernel

theorem rowCheck14030 : row14030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14030 := by decide +kernel

theorem rowEval14030 (x : Key → ℝ) : Integer.Sparse.eval row14030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14030, Integer.Sparse.eval_collectBalanced, rawRowCheck14030]

theorem rawRowCheck14031 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14031 := by decide +kernel

theorem rowCheck14031 : row14031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14031 := by decide +kernel

theorem rowEval14031 (x : Key → ℝ) : Integer.Sparse.eval row14031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14031, Integer.Sparse.eval_collectBalanced, rawRowCheck14031]

theorem rawRowCheck14032 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14032 := by decide +kernel

theorem rowCheck14032 : row14032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14032 := by decide +kernel

theorem rowEval14032 (x : Key → ℝ) : Integer.Sparse.eval row14032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14032, Integer.Sparse.eval_collectBalanced, rawRowCheck14032]

theorem rawRowCheck14033 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14033 := by decide +kernel

theorem rowCheck14033 : row14033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14033 := by decide +kernel

theorem rowEval14033 (x : Key → ℝ) : Integer.Sparse.eval row14033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14033, Integer.Sparse.eval_collectBalanced, rawRowCheck14033]

theorem rawRowCheck14034 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14034 := by decide +kernel

theorem rowCheck14034 : row14034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14034 := by decide +kernel

theorem rowEval14034 (x : Key → ℝ) : Integer.Sparse.eval row14034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14034, Integer.Sparse.eval_collectBalanced, rawRowCheck14034]

theorem rawRowCheck14035 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14035 := by decide +kernel

theorem rowCheck14035 : row14035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14035 := by decide +kernel

theorem rowEval14035 (x : Key → ℝ) : Integer.Sparse.eval row14035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14035, Integer.Sparse.eval_collectBalanced, rawRowCheck14035]

theorem rawRowCheck14036 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14036 := by decide +kernel

theorem rowCheck14036 : row14036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14036 := by decide +kernel

theorem rowEval14036 (x : Key → ℝ) : Integer.Sparse.eval row14036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14036, Integer.Sparse.eval_collectBalanced, rawRowCheck14036]

theorem rawRowCheck14037 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14037 := by decide +kernel

theorem rowCheck14037 : row14037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14037 := by decide +kernel

theorem rowEval14037 (x : Key → ℝ) : Integer.Sparse.eval row14037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14037, Integer.Sparse.eval_collectBalanced, rawRowCheck14037]

theorem rawRowCheck14038 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14038 := by decide +kernel

theorem rowCheck14038 : row14038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14038 := by decide +kernel

theorem rowEval14038 (x : Key → ℝ) : Integer.Sparse.eval row14038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14038, Integer.Sparse.eval_collectBalanced, rawRowCheck14038]

theorem rawRowCheck14039 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14039 := by decide +kernel

theorem rowCheck14039 : row14039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14039 := by decide +kernel

theorem rowEval14039 (x : Key → ℝ) : Integer.Sparse.eval row14039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14039, Integer.Sparse.eval_collectBalanced, rawRowCheck14039]

theorem rawRowCheck14040 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14040 := by decide +kernel

theorem rowCheck14040 : row14040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14040 := by decide +kernel

theorem rowEval14040 (x : Key → ℝ) : Integer.Sparse.eval row14040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14040, Integer.Sparse.eval_collectBalanced, rawRowCheck14040]

theorem rawRowCheck14041 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14041 := by decide +kernel

theorem rowCheck14041 : row14041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14041 := by decide +kernel

theorem rowEval14041 (x : Key → ℝ) : Integer.Sparse.eval row14041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14041, Integer.Sparse.eval_collectBalanced, rawRowCheck14041]

theorem rawRowCheck14042 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14042 := by decide +kernel

theorem rowCheck14042 : row14042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14042 := by decide +kernel

theorem rowEval14042 (x : Key → ℝ) : Integer.Sparse.eval row14042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14042, Integer.Sparse.eval_collectBalanced, rawRowCheck14042]

theorem rawRowCheck14043 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14043 := by decide +kernel

theorem rowCheck14043 : row14043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14043 := by decide +kernel

theorem rowEval14043 (x : Key → ℝ) : Integer.Sparse.eval row14043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14043, Integer.Sparse.eval_collectBalanced, rawRowCheck14043]

theorem rawRowCheck14044 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14044 := by decide +kernel

theorem rowCheck14044 : row14044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14044 := by decide +kernel

theorem rowEval14044 (x : Key → ℝ) : Integer.Sparse.eval row14044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14044, Integer.Sparse.eval_collectBalanced, rawRowCheck14044]

theorem rawRowCheck14065 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form7 = rawRow14065 := by decide +kernel

theorem rowCheck14065 : row14065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14065 := by decide +kernel

theorem rowEval14065 (x : Key → ℝ) : Integer.Sparse.eval row14065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14065, Integer.Sparse.eval_collectBalanced, rawRowCheck14065]

theorem rawRowCheck14066 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form7 = rawRow14066 := by decide +kernel

theorem rowCheck14066 : row14066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14066 := by decide +kernel

theorem rowEval14066 (x : Key → ℝ) : Integer.Sparse.eval row14066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14066, Integer.Sparse.eval_collectBalanced, rawRowCheck14066]

theorem rawRowCheck14067 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form7 = rawRow14067 := by decide +kernel

theorem rowCheck14067 : row14067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14067 := by decide +kernel

theorem rowEval14067 (x : Key → ℝ) : Integer.Sparse.eval row14067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14067, Integer.Sparse.eval_collectBalanced, rawRowCheck14067]

theorem rawRowCheck14068 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14068 := by decide +kernel

theorem rowCheck14068 : row14068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14068 := by decide +kernel

theorem rowEval14068 (x : Key → ℝ) : Integer.Sparse.eval row14068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14068, Integer.Sparse.eval_collectBalanced, rawRowCheck14068]

theorem rawRowCheck14069 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form7 = rawRow14069 := by decide +kernel

theorem rowCheck14069 : row14069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14069 := by decide +kernel

theorem rowEval14069 (x : Key → ℝ) : Integer.Sparse.eval row14069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14069, Integer.Sparse.eval_collectBalanced, rawRowCheck14069]

theorem rawRowCheck14070 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form7 = rawRow14070 := by decide +kernel

theorem rowCheck14070 : row14070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14070 := by decide +kernel

theorem rowEval14070 (x : Key → ℝ) : Integer.Sparse.eval row14070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14070, Integer.Sparse.eval_collectBalanced, rawRowCheck14070]

theorem rawRowCheck14071 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form7 = rawRow14071 := by decide +kernel

theorem rowCheck14071 : row14071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14071 := by decide +kernel

theorem rowEval14071 (x : Key → ℝ) : Integer.Sparse.eval row14071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14071, Integer.Sparse.eval_collectBalanced, rawRowCheck14071]

theorem rawRowCheck14072 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form7 = rawRow14072 := by decide +kernel

theorem rowCheck14072 : row14072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14072 := by decide +kernel

theorem rowEval14072 (x : Key → ℝ) : Integer.Sparse.eval row14072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14072, Integer.Sparse.eval_collectBalanced, rawRowCheck14072]

theorem rawRowCheck14073 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form7 = rawRow14073 := by decide +kernel

theorem rowCheck14073 : row14073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14073 := by decide +kernel

theorem rowEval14073 (x : Key → ℝ) : Integer.Sparse.eval row14073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14073, Integer.Sparse.eval_collectBalanced, rawRowCheck14073]

theorem rawRowCheck14074 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form7 = rawRow14074 := by decide +kernel

theorem rowCheck14074 : row14074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14074 := by decide +kernel

theorem rowEval14074 (x : Key → ℝ) : Integer.Sparse.eval row14074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14074, Integer.Sparse.eval_collectBalanced, rawRowCheck14074]

theorem rawRowCheck14075 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form7 = rawRow14075 := by decide +kernel

theorem rowCheck14075 : row14075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14075 := by decide +kernel

theorem rowEval14075 (x : Key → ℝ) : Integer.Sparse.eval row14075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14075, Integer.Sparse.eval_collectBalanced, rawRowCheck14075]

theorem rawRowCheck14076 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form7 = rawRow14076 := by decide +kernel

theorem rowCheck14076 : row14076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14076 := by decide +kernel

theorem rowEval14076 (x : Key → ℝ) : Integer.Sparse.eval row14076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14076, Integer.Sparse.eval_collectBalanced, rawRowCheck14076]

theorem rawRowCheck14077 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form7 = rawRow14077 := by decide +kernel

theorem rowCheck14077 : row14077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14077 := by decide +kernel

theorem rowEval14077 (x : Key → ℝ) : Integer.Sparse.eval row14077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14077, Integer.Sparse.eval_collectBalanced, rawRowCheck14077]

theorem rawRowCheck14078 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form7 = rawRow14078 := by decide +kernel

theorem rowCheck14078 : row14078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14078 := by decide +kernel

theorem rowEval14078 (x : Key → ℝ) : Integer.Sparse.eval row14078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14078, Integer.Sparse.eval_collectBalanced, rawRowCheck14078]

theorem rawRowCheck14079 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form7 = rawRow14079 := by decide +kernel

theorem rowCheck14079 : row14079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14079 := by decide +kernel

theorem rowEval14079 (x : Key → ℝ) : Integer.Sparse.eval row14079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14079, Integer.Sparse.eval_collectBalanced, rawRowCheck14079]

end MUB6.Certificate.GramRows

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

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13945 x
  · exact rowEval13946 x
  · exact rowEval13947 x
  · exact rowEval13948 x
  · exact rowEval13949 x
  · exact rowEval13950 x
  · exact rowEval13951 x
  · exact rowEval13952 x
  · exact rowEval13953 x
  · exact rowEval13954 x
  · exact rowEval13955 x
  · exact rowEval13956 x
  · exact rowEval13957 x
  · exact rowEval13958 x
  · exact rowEval13959 x
  · exact rowEval13960 x
  · exact rowEval13961 x
  · exact rowEval13962 x
  · exact rowEval13963 x
  · exact rowEval13964 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

theorem entryCheck8_2 : entry8_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_2 k)) := by decide +kernel

theorem rowsSound8_2 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13965 x
  · exact rowEval13966 x
  · exact rowEval13967 x
  · exact rowEval13968 x
  · exact rowEval13969 x
  · exact rowEval13970 x
  · exact rowEval13971 x
  · exact rowEval13972 x
  · exact rowEval13973 x
  · exact rowEval13974 x
  · exact rowEval13975 x
  · exact rowEval13976 x
  · exact rowEval13977 x
  · exact rowEval13978 x
  · exact rowEval13979 x
  · exact rowEval13980 x
  · exact rowEval13981 x
  · exact rowEval13982 x
  · exact rowEval13983 x
  · exact rowEval13984 x

theorem entryEval8_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_2 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck8_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_2]

theorem entryCheck8_3 : entry8_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_3 k)) := by decide +kernel

theorem rowsSound8_3 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13985 x
  · exact rowEval13986 x
  · exact rowEval13987 x
  · exact rowEval13988 x
  · exact rowEval13989 x
  · exact rowEval13990 x
  · exact rowEval13991 x
  · exact rowEval13992 x
  · exact rowEval13993 x
  · exact rowEval13994 x
  · exact rowEval13995 x
  · exact rowEval13996 x
  · exact rowEval13997 x
  · exact rowEval13998 x
  · exact rowEval13999 x
  · exact rowEval14000 x
  · exact rowEval14001 x
  · exact rowEval14002 x
  · exact rowEval14003 x
  · exact rowEval14004 x

theorem entryEval8_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_3 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck8_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_3]

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14005 x
  · exact rowEval14006 x
  · exact rowEval14007 x
  · exact rowEval14008 x
  · exact rowEval14009 x
  · exact rowEval14010 x
  · exact rowEval14011 x
  · exact rowEval14012 x
  · exact rowEval14013 x
  · exact rowEval14014 x
  · exact rowEval14015 x
  · exact rowEval14016 x
  · exact rowEval14017 x
  · exact rowEval14018 x
  · exact rowEval14019 x
  · exact rowEval14020 x
  · exact rowEval14021 x
  · exact rowEval14022 x
  · exact rowEval14023 x
  · exact rowEval14024 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14025 x
  · exact rowEval14026 x
  · exact rowEval14027 x
  · exact rowEval14028 x
  · exact rowEval14029 x
  · exact rowEval14030 x
  · exact rowEval14031 x
  · exact rowEval14032 x
  · exact rowEval14033 x
  · exact rowEval14034 x
  · exact rowEval14035 x
  · exact rowEval14036 x
  · exact rowEval14037 x
  · exact rowEval14038 x
  · exact rowEval14039 x
  · exact rowEval14040 x
  · exact rowEval14041 x
  · exact rowEval14042 x
  · exact rowEval14043 x
  · exact rowEval14044 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval14065 x
  · exact rowEval14066 x
  · exact rowEval14067 x
  · exact rowEval14068 x
  · exact rowEval14069 x
  · exact rowEval14070 x
  · exact rowEval14071 x
  · exact rowEval14072 x
  · exact rowEval14073 x
  · exact rowEval14074 x
  · exact rowEval14075 x
  · exact rowEval14076 x
  · exact rowEval14077 x
  · exact rowEval14078 x
  · exact rowEval14079 x
  · exact rowEval14080 x
  · exact rowEval14081 x
  · exact rowEval14082 x
  · exact rowEval14083 x
  · exact rowEval14084 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

theorem entryCheck8_8 : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

theorem rowsSound8_8 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14085 x
  · exact rowEval14086 x
  · exact rowEval14087 x
  · exact rowEval14088 x
  · exact rowEval14089 x
  · exact rowEval14090 x
  · exact rowEval14091 x
  · exact rowEval14092 x
  · exact rowEval14093 x
  · exact rowEval14094 x
  · exact rowEval14095 x
  · exact rowEval14096 x
  · exact rowEval14097 x
  · exact rowEval14098 x
  · exact rowEval14099 x
  · exact rowEval14100 x
  · exact rowEval14101 x
  · exact rowEval14102 x
  · exact rowEval14103 x
  · exact rowEval14104 x

theorem entryEval8_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_8 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck8_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_8]

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

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14185 x
  · exact rowEval14186 x
  · exact rowEval14187 x
  · exact rowEval14188 x
  · exact rowEval14189 x
  · exact rowEval14190 x
  · exact rowEval14191 x
  · exact rowEval14192 x
  · exact rowEval14193 x
  · exact rowEval14194 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

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

theorem entryEvalRow8_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 8 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 8).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval8_0 B hB
  · exact entryEval8_1 B hB
  · exact entryEval8_2 B hB
  · exact entryEval8_3 B hB
  · exact entryEval8_4 B hB
  · exact entryEval8_5 B hB
  · exact entryEval8_6_e B hB
  · exact entryEval8_7 B hB
  · exact entryEval8_8 B hB
  · exact (entryEval9_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e_oai
