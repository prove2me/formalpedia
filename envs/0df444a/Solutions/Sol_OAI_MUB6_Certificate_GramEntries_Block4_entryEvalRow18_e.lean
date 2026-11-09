-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T18:05:26.407823+00:00
-- url     : https://prove2.me/submissions/7c8ef891-ef0c-4890-a4ef-aa1296255af7

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_18_e

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

theorem rawRowCheck17051 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form1 = rawRow17051 := by decide +kernel

theorem rowCheck17051 : row17051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17051 := by decide +kernel

theorem rowEval17051 (x : Key → ℝ) : Integer.Sparse.eval row17051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck17051, Integer.Sparse.eval_collectBalanced, rawRowCheck17051]

theorem rawRowCheck17052 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form1 = rawRow17052 := by decide +kernel

theorem rowCheck17052 : row17052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17052 := by decide +kernel

theorem rowEval17052 (x : Key → ℝ) : Integer.Sparse.eval row17052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17052, Integer.Sparse.eval_collectBalanced, rawRowCheck17052]

theorem rawRowCheck17053 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form1 = rawRow17053 := by decide +kernel

theorem rowCheck17053 : row17053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17053 := by decide +kernel

theorem rowEval17053 (x : Key → ℝ) : Integer.Sparse.eval row17053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck17053, Integer.Sparse.eval_collectBalanced, rawRowCheck17053]

theorem rawRowCheck17054 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form1 = rawRow17054 := by decide +kernel

theorem rowCheck17054 : row17054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17054 := by decide +kernel

theorem rowEval17054 (x : Key → ℝ) : Integer.Sparse.eval row17054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17054, Integer.Sparse.eval_collectBalanced, rawRowCheck17054]

theorem rawRowCheck17055 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form1 = rawRow17055 := by decide +kernel

theorem rowCheck17055 : row17055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17055 := by decide +kernel

theorem rowEval17055 (x : Key → ℝ) : Integer.Sparse.eval row17055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17055, Integer.Sparse.eval_collectBalanced, rawRowCheck17055]

theorem rawRowCheck17056 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form1 = rawRow17056 := by decide +kernel

theorem rowCheck17056 : row17056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17056 := by decide +kernel

theorem rowEval17056 (x : Key → ℝ) : Integer.Sparse.eval row17056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17056, Integer.Sparse.eval_collectBalanced, rawRowCheck17056]

theorem rawRowCheck17057 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form1 = rawRow17057 := by decide +kernel

theorem rowCheck17057 : row17057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17057 := by decide +kernel

theorem rowEval17057 (x : Key → ℝ) : Integer.Sparse.eval row17057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck17057, Integer.Sparse.eval_collectBalanced, rawRowCheck17057]

theorem rawRowCheck17058 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form1 = rawRow17058 := by decide +kernel

theorem rowCheck17058 : row17058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17058 := by decide +kernel

theorem rowEval17058 (x : Key → ℝ) : Integer.Sparse.eval row17058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17058, Integer.Sparse.eval_collectBalanced, rawRowCheck17058]

theorem rawRowCheck17059 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form1 = rawRow17059 := by decide +kernel

theorem rowCheck17059 : row17059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17059 := by decide +kernel

theorem rowEval17059 (x : Key → ℝ) : Integer.Sparse.eval row17059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17059, Integer.Sparse.eval_collectBalanced, rawRowCheck17059]

theorem rawRowCheck17060 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form1 = rawRow17060 := by decide +kernel

theorem rowCheck17060 : row17060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17060 := by decide +kernel

theorem rowEval17060 (x : Key → ℝ) : Integer.Sparse.eval row17060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17060, Integer.Sparse.eval_collectBalanced, rawRowCheck17060]

theorem rawRowCheck17061 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form1 = rawRow17061 := by decide +kernel

theorem rowCheck17061 : row17061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17061 := by decide +kernel

theorem rowEval17061 (x : Key → ℝ) : Integer.Sparse.eval row17061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17061, Integer.Sparse.eval_collectBalanced, rawRowCheck17061]

theorem rawRowCheck17062 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form1 = rawRow17062 := by decide +kernel

theorem rowCheck17062 : row17062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17062 := by decide +kernel

theorem rowEval17062 (x : Key → ℝ) : Integer.Sparse.eval row17062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17062, Integer.Sparse.eval_collectBalanced, rawRowCheck17062]

theorem rawRowCheck17063 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form1 = rawRow17063 := by decide +kernel

theorem rowCheck17063 : row17063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17063 := by decide +kernel

theorem rowEval17063 (x : Key → ℝ) : Integer.Sparse.eval row17063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck17063, Integer.Sparse.eval_collectBalanced, rawRowCheck17063]

theorem rawRowCheck17064 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form1 = rawRow17064 := by decide +kernel

theorem rowCheck17064 : row17064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17064 := by decide +kernel

theorem rowEval17064 (x : Key → ℝ) : Integer.Sparse.eval row17064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17064, Integer.Sparse.eval_collectBalanced, rawRowCheck17064]

theorem rawRowCheck17065 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form1 = rawRow17065 := by decide +kernel

theorem rowCheck17065 : row17065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17065 := by decide +kernel

theorem rowEval17065 (x : Key → ℝ) : Integer.Sparse.eval row17065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17065, Integer.Sparse.eval_collectBalanced, rawRowCheck17065]

theorem rawRowCheck17066 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form1 = rawRow17066 := by decide +kernel

theorem rowCheck17066 : row17066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17066 := by decide +kernel

theorem rowEval17066 (x : Key → ℝ) : Integer.Sparse.eval row17066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17066, Integer.Sparse.eval_collectBalanced, rawRowCheck17066]

theorem rawRowCheck17067 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow17067 := by decide +kernel

theorem rowCheck17067 : row17067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17067 := by decide +kernel

theorem rowEval17067 (x : Key → ℝ) : Integer.Sparse.eval row17067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17067, Integer.Sparse.eval_collectBalanced, rawRowCheck17067]

theorem rawRowCheck17068 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow17068 := by decide +kernel

theorem rowCheck17068 : row17068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17068 := by decide +kernel

theorem rowEval17068 (x : Key → ℝ) : Integer.Sparse.eval row17068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17068, Integer.Sparse.eval_collectBalanced, rawRowCheck17068]

theorem rawRowCheck17069 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow17069 := by decide +kernel

theorem rowCheck17069 : row17069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17069 := by decide +kernel

theorem rowEval17069 (x : Key → ℝ) : Integer.Sparse.eval row17069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17069, Integer.Sparse.eval_collectBalanced, rawRowCheck17069]

theorem rawRowCheck17070 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow17070 := by decide +kernel

theorem rowCheck17070 : row17070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17070 := by decide +kernel

theorem rowEval17070 (x : Key → ℝ) : Integer.Sparse.eval row17070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17070, Integer.Sparse.eval_collectBalanced, rawRowCheck17070]

theorem rawRowCheck17071 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form2 = rawRow17071 := by decide +kernel

theorem rowCheck17071 : row17071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17071 := by decide +kernel

theorem rowEval17071 (x : Key → ℝ) : Integer.Sparse.eval row17071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck17071, Integer.Sparse.eval_collectBalanced, rawRowCheck17071]

theorem rawRowCheck17072 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form2 = rawRow17072 := by decide +kernel

theorem rowCheck17072 : row17072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17072 := by decide +kernel

theorem rowEval17072 (x : Key → ℝ) : Integer.Sparse.eval row17072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17072, Integer.Sparse.eval_collectBalanced, rawRowCheck17072]

theorem rawRowCheck17073 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form2 = rawRow17073 := by decide +kernel

theorem rowCheck17073 : row17073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17073 := by decide +kernel

theorem rowEval17073 (x : Key → ℝ) : Integer.Sparse.eval row17073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck17073, Integer.Sparse.eval_collectBalanced, rawRowCheck17073]

theorem rawRowCheck17074 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form2 = rawRow17074 := by decide +kernel

theorem rowCheck17074 : row17074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17074 := by decide +kernel

theorem rowEval17074 (x : Key → ℝ) : Integer.Sparse.eval row17074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17074, Integer.Sparse.eval_collectBalanced, rawRowCheck17074]

theorem rawRowCheck17075 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form2 = rawRow17075 := by decide +kernel

theorem rowCheck17075 : row17075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17075 := by decide +kernel

theorem rowEval17075 (x : Key → ℝ) : Integer.Sparse.eval row17075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17075, Integer.Sparse.eval_collectBalanced, rawRowCheck17075]

theorem rawRowCheck17076 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form2 = rawRow17076 := by decide +kernel

theorem rowCheck17076 : row17076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17076 := by decide +kernel

theorem rowEval17076 (x : Key → ℝ) : Integer.Sparse.eval row17076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17076, Integer.Sparse.eval_collectBalanced, rawRowCheck17076]

theorem rawRowCheck17077 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form2 = rawRow17077 := by decide +kernel

theorem rowCheck17077 : row17077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17077 := by decide +kernel

theorem rowEval17077 (x : Key → ℝ) : Integer.Sparse.eval row17077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck17077, Integer.Sparse.eval_collectBalanced, rawRowCheck17077]

theorem rawRowCheck17078 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form2 = rawRow17078 := by decide +kernel

theorem rowCheck17078 : row17078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17078 := by decide +kernel

theorem rowEval17078 (x : Key → ℝ) : Integer.Sparse.eval row17078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17078, Integer.Sparse.eval_collectBalanced, rawRowCheck17078]

theorem rawRowCheck17079 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form2 = rawRow17079 := by decide +kernel

theorem rowCheck17079 : row17079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17079 := by decide +kernel

theorem rowEval17079 (x : Key → ℝ) : Integer.Sparse.eval row17079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17079, Integer.Sparse.eval_collectBalanced, rawRowCheck17079]

theorem rawRowCheck17080 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form2 = rawRow17080 := by decide +kernel

theorem rowCheck17080 : row17080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17080 := by decide +kernel

theorem rowEval17080 (x : Key → ℝ) : Integer.Sparse.eval row17080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17080, Integer.Sparse.eval_collectBalanced, rawRowCheck17080]

theorem rawRowCheck17081 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form2 = rawRow17081 := by decide +kernel

theorem rowCheck17081 : row17081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17081 := by decide +kernel

theorem rowEval17081 (x : Key → ℝ) : Integer.Sparse.eval row17081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17081, Integer.Sparse.eval_collectBalanced, rawRowCheck17081]

theorem rawRowCheck17082 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form2 = rawRow17082 := by decide +kernel

theorem rowCheck17082 : row17082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17082 := by decide +kernel

theorem rowEval17082 (x : Key → ℝ) : Integer.Sparse.eval row17082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17082, Integer.Sparse.eval_collectBalanced, rawRowCheck17082]

theorem rawRowCheck17083 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form2 = rawRow17083 := by decide +kernel

theorem rowCheck17083 : row17083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17083 := by decide +kernel

theorem rowEval17083 (x : Key → ℝ) : Integer.Sparse.eval row17083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck17083, Integer.Sparse.eval_collectBalanced, rawRowCheck17083]

theorem rawRowCheck17084 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form2 = rawRow17084 := by decide +kernel

theorem rowCheck17084 : row17084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17084 := by decide +kernel

theorem rowEval17084 (x : Key → ℝ) : Integer.Sparse.eval row17084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17084, Integer.Sparse.eval_collectBalanced, rawRowCheck17084]

theorem rawRowCheck17085 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form2 = rawRow17085 := by decide +kernel

theorem rowCheck17085 : row17085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17085 := by decide +kernel

theorem rowEval17085 (x : Key → ℝ) : Integer.Sparse.eval row17085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17085, Integer.Sparse.eval_collectBalanced, rawRowCheck17085]

theorem rawRowCheck17086 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form2 = rawRow17086 := by decide +kernel

theorem rowCheck17086 : row17086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17086 := by decide +kernel

theorem rowEval17086 (x : Key → ℝ) : Integer.Sparse.eval row17086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17086, Integer.Sparse.eval_collectBalanced, rawRowCheck17086]

theorem rawRowCheck17087 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow17087 := by decide +kernel

theorem rowCheck17087 : row17087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17087 := by decide +kernel

theorem rowEval17087 (x : Key → ℝ) : Integer.Sparse.eval row17087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17087, Integer.Sparse.eval_collectBalanced, rawRowCheck17087]

theorem rawRowCheck17088 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow17088 := by decide +kernel

theorem rowCheck17088 : row17088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17088 := by decide +kernel

theorem rowEval17088 (x : Key → ℝ) : Integer.Sparse.eval row17088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17088, Integer.Sparse.eval_collectBalanced, rawRowCheck17088]

theorem rawRowCheck17089 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow17089 := by decide +kernel

theorem rowCheck17089 : row17089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17089 := by decide +kernel

theorem rowEval17089 (x : Key → ℝ) : Integer.Sparse.eval row17089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17089, Integer.Sparse.eval_collectBalanced, rawRowCheck17089]

theorem rawRowCheck17090 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow17090 := by decide +kernel

theorem rowCheck17090 : row17090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17090 := by decide +kernel

theorem rowEval17090 (x : Key → ℝ) : Integer.Sparse.eval row17090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17090, Integer.Sparse.eval_collectBalanced, rawRowCheck17090]

theorem rawRowCheck17091 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form3 = rawRow17091 := by decide +kernel

theorem rowCheck17091 : row17091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17091 := by decide +kernel

theorem rowEval17091 (x : Key → ℝ) : Integer.Sparse.eval row17091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck17091, Integer.Sparse.eval_collectBalanced, rawRowCheck17091]

theorem rawRowCheck17092 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form3 = rawRow17092 := by decide +kernel

theorem rowCheck17092 : row17092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17092 := by decide +kernel

theorem rowEval17092 (x : Key → ℝ) : Integer.Sparse.eval row17092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17092, Integer.Sparse.eval_collectBalanced, rawRowCheck17092]

theorem rawRowCheck17093 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form3 = rawRow17093 := by decide +kernel

theorem rowCheck17093 : row17093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17093 := by decide +kernel

theorem rowEval17093 (x : Key → ℝ) : Integer.Sparse.eval row17093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck17093, Integer.Sparse.eval_collectBalanced, rawRowCheck17093]

theorem rawRowCheck17094 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form3 = rawRow17094 := by decide +kernel

theorem rowCheck17094 : row17094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17094 := by decide +kernel

theorem rowEval17094 (x : Key → ℝ) : Integer.Sparse.eval row17094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17094, Integer.Sparse.eval_collectBalanced, rawRowCheck17094]

theorem rawRowCheck17095 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form3 = rawRow17095 := by decide +kernel

theorem rowCheck17095 : row17095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17095 := by decide +kernel

theorem rowEval17095 (x : Key → ℝ) : Integer.Sparse.eval row17095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17095, Integer.Sparse.eval_collectBalanced, rawRowCheck17095]

theorem rawRowCheck17096 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form3 = rawRow17096 := by decide +kernel

theorem rowCheck17096 : row17096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17096 := by decide +kernel

theorem rowEval17096 (x : Key → ℝ) : Integer.Sparse.eval row17096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17096, Integer.Sparse.eval_collectBalanced, rawRowCheck17096]

theorem rawRowCheck17097 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form3 = rawRow17097 := by decide +kernel

theorem rowCheck17097 : row17097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17097 := by decide +kernel

theorem rowEval17097 (x : Key → ℝ) : Integer.Sparse.eval row17097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck17097, Integer.Sparse.eval_collectBalanced, rawRowCheck17097]

theorem rawRowCheck17098 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form3 = rawRow17098 := by decide +kernel

theorem rowCheck17098 : row17098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17098 := by decide +kernel

theorem rowEval17098 (x : Key → ℝ) : Integer.Sparse.eval row17098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17098, Integer.Sparse.eval_collectBalanced, rawRowCheck17098]

theorem rawRowCheck17099 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form3 = rawRow17099 := by decide +kernel

theorem rowCheck17099 : row17099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17099 := by decide +kernel

theorem rowEval17099 (x : Key → ℝ) : Integer.Sparse.eval row17099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17099, Integer.Sparse.eval_collectBalanced, rawRowCheck17099]

theorem rawRowCheck17100 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form3 = rawRow17100 := by decide +kernel

theorem rowCheck17100 : row17100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17100 := by decide +kernel

theorem rowEval17100 (x : Key → ℝ) : Integer.Sparse.eval row17100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17100, Integer.Sparse.eval_collectBalanced, rawRowCheck17100]

theorem rawRowCheck17101 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form3 = rawRow17101 := by decide +kernel

theorem rowCheck17101 : row17101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17101 := by decide +kernel

theorem rowEval17101 (x : Key → ℝ) : Integer.Sparse.eval row17101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17101, Integer.Sparse.eval_collectBalanced, rawRowCheck17101]

theorem rawRowCheck17102 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form3 = rawRow17102 := by decide +kernel

theorem rowCheck17102 : row17102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17102 := by decide +kernel

theorem rowEval17102 (x : Key → ℝ) : Integer.Sparse.eval row17102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17102, Integer.Sparse.eval_collectBalanced, rawRowCheck17102]

theorem rawRowCheck17103 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form3 = rawRow17103 := by decide +kernel

theorem rowCheck17103 : row17103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17103 := by decide +kernel

theorem rowEval17103 (x : Key → ℝ) : Integer.Sparse.eval row17103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck17103, Integer.Sparse.eval_collectBalanced, rawRowCheck17103]

theorem rawRowCheck17104 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form3 = rawRow17104 := by decide +kernel

theorem rowCheck17104 : row17104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17104 := by decide +kernel

theorem rowEval17104 (x : Key → ℝ) : Integer.Sparse.eval row17104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17104, Integer.Sparse.eval_collectBalanced, rawRowCheck17104]

theorem rawRowCheck17105 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form3 = rawRow17105 := by decide +kernel

theorem rowCheck17105 : row17105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17105 := by decide +kernel

theorem rowEval17105 (x : Key → ℝ) : Integer.Sparse.eval row17105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17105, Integer.Sparse.eval_collectBalanced, rawRowCheck17105]

theorem rawRowCheck17106 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form3 = rawRow17106 := by decide +kernel

theorem rowCheck17106 : row17106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17106 := by decide +kernel

theorem rowEval17106 (x : Key → ℝ) : Integer.Sparse.eval row17106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17106, Integer.Sparse.eval_collectBalanced, rawRowCheck17106]

theorem rawRowCheck17107 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow17107 := by decide +kernel

theorem rowCheck17107 : row17107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17107 := by decide +kernel

theorem rowEval17107 (x : Key → ℝ) : Integer.Sparse.eval row17107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17107, Integer.Sparse.eval_collectBalanced, rawRowCheck17107]

theorem rawRowCheck17108 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow17108 := by decide +kernel

theorem rowCheck17108 : row17108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17108 := by decide +kernel

theorem rowEval17108 (x : Key → ℝ) : Integer.Sparse.eval row17108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17108, Integer.Sparse.eval_collectBalanced, rawRowCheck17108]

theorem rawRowCheck17109 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow17109 := by decide +kernel

theorem rowCheck17109 : row17109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17109 := by decide +kernel

theorem rowEval17109 (x : Key → ℝ) : Integer.Sparse.eval row17109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17109, Integer.Sparse.eval_collectBalanced, rawRowCheck17109]

theorem rawRowCheck17110 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow17110 := by decide +kernel

theorem rowCheck17110 : row17110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17110 := by decide +kernel

theorem rowEval17110 (x : Key → ℝ) : Integer.Sparse.eval row17110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17110, Integer.Sparse.eval_collectBalanced, rawRowCheck17110]

theorem rawRowCheck17111 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form4 = rawRow17111 := by decide +kernel

theorem rowCheck17111 : row17111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17111 := by decide +kernel

theorem rowEval17111 (x : Key → ℝ) : Integer.Sparse.eval row17111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17111, Integer.Sparse.eval_collectBalanced, rawRowCheck17111]

theorem rawRowCheck17112 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form4 = rawRow17112 := by decide +kernel

theorem rowCheck17112 : row17112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17112 := by decide +kernel

theorem rowEval17112 (x : Key → ℝ) : Integer.Sparse.eval row17112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17112, Integer.Sparse.eval_collectBalanced, rawRowCheck17112]

theorem rawRowCheck17113 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form4 = rawRow17113 := by decide +kernel

theorem rowCheck17113 : row17113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17113 := by decide +kernel

theorem rowEval17113 (x : Key → ℝ) : Integer.Sparse.eval row17113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17113, Integer.Sparse.eval_collectBalanced, rawRowCheck17113]

theorem rawRowCheck17114 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form4 = rawRow17114 := by decide +kernel

theorem rowCheck17114 : row17114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17114 := by decide +kernel

theorem rowEval17114 (x : Key → ℝ) : Integer.Sparse.eval row17114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17114, Integer.Sparse.eval_collectBalanced, rawRowCheck17114]

theorem rawRowCheck17115 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form4 = rawRow17115 := by decide +kernel

theorem rowCheck17115 : row17115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17115 := by decide +kernel

theorem rowEval17115 (x : Key → ℝ) : Integer.Sparse.eval row17115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17115, Integer.Sparse.eval_collectBalanced, rawRowCheck17115]

theorem rawRowCheck17116 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form4 = rawRow17116 := by decide +kernel

theorem rowCheck17116 : row17116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17116 := by decide +kernel

theorem rowEval17116 (x : Key → ℝ) : Integer.Sparse.eval row17116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17116, Integer.Sparse.eval_collectBalanced, rawRowCheck17116]

theorem rawRowCheck17117 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form4 = rawRow17117 := by decide +kernel

theorem rowCheck17117 : row17117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17117 := by decide +kernel

theorem rowEval17117 (x : Key → ℝ) : Integer.Sparse.eval row17117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17117, Integer.Sparse.eval_collectBalanced, rawRowCheck17117]

theorem rawRowCheck17118 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form4 = rawRow17118 := by decide +kernel

theorem rowCheck17118 : row17118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17118 := by decide +kernel

theorem rowEval17118 (x : Key → ℝ) : Integer.Sparse.eval row17118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17118, Integer.Sparse.eval_collectBalanced, rawRowCheck17118]

theorem rawRowCheck17119 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form4 = rawRow17119 := by decide +kernel

theorem rowCheck17119 : row17119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17119 := by decide +kernel

theorem rowEval17119 (x : Key → ℝ) : Integer.Sparse.eval row17119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17119, Integer.Sparse.eval_collectBalanced, rawRowCheck17119]

theorem rawRowCheck17120 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form4 = rawRow17120 := by decide +kernel

theorem rowCheck17120 : row17120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17120 := by decide +kernel

theorem rowEval17120 (x : Key → ℝ) : Integer.Sparse.eval row17120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17120, Integer.Sparse.eval_collectBalanced, rawRowCheck17120]

theorem rawRowCheck17121 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form4 = rawRow17121 := by decide +kernel

theorem rowCheck17121 : row17121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17121 := by decide +kernel

theorem rowEval17121 (x : Key → ℝ) : Integer.Sparse.eval row17121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17121, Integer.Sparse.eval_collectBalanced, rawRowCheck17121]

theorem rawRowCheck17122 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form4 = rawRow17122 := by decide +kernel

theorem rowCheck17122 : row17122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17122 := by decide +kernel

theorem rowEval17122 (x : Key → ℝ) : Integer.Sparse.eval row17122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17122, Integer.Sparse.eval_collectBalanced, rawRowCheck17122]

theorem rawRowCheck17123 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form4 = rawRow17123 := by decide +kernel

theorem rowCheck17123 : row17123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17123 := by decide +kernel

theorem rowEval17123 (x : Key → ℝ) : Integer.Sparse.eval row17123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17123, Integer.Sparse.eval_collectBalanced, rawRowCheck17123]

theorem rawRowCheck17124 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form4 = rawRow17124 := by decide +kernel

theorem rowCheck17124 : row17124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17124 := by decide +kernel

theorem rowEval17124 (x : Key → ℝ) : Integer.Sparse.eval row17124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17124, Integer.Sparse.eval_collectBalanced, rawRowCheck17124]

theorem rawRowCheck17125 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form4 = rawRow17125 := by decide +kernel

theorem rowCheck17125 : row17125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17125 := by decide +kernel

theorem rowEval17125 (x : Key → ℝ) : Integer.Sparse.eval row17125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17125, Integer.Sparse.eval_collectBalanced, rawRowCheck17125]

theorem rawRowCheck17126 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form4 = rawRow17126 := by decide +kernel

theorem rowCheck17126 : row17126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17126 := by decide +kernel

theorem rowEval17126 (x : Key → ℝ) : Integer.Sparse.eval row17126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17126, Integer.Sparse.eval_collectBalanced, rawRowCheck17126]

theorem rawRowCheck17127 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow17127 := by decide +kernel

theorem rowCheck17127 : row17127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17127 := by decide +kernel

theorem rowEval17127 (x : Key → ℝ) : Integer.Sparse.eval row17127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17127, Integer.Sparse.eval_collectBalanced, rawRowCheck17127]

theorem rawRowCheck17128 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow17128 := by decide +kernel

theorem rowCheck17128 : row17128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17128 := by decide +kernel

theorem rowEval17128 (x : Key → ℝ) : Integer.Sparse.eval row17128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17128, Integer.Sparse.eval_collectBalanced, rawRowCheck17128]

theorem rawRowCheck17129 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow17129 := by decide +kernel

theorem rowCheck17129 : row17129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17129 := by decide +kernel

theorem rowEval17129 (x : Key → ℝ) : Integer.Sparse.eval row17129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17129, Integer.Sparse.eval_collectBalanced, rawRowCheck17129]

theorem rawRowCheck17130 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow17130 := by decide +kernel

theorem rowCheck17130 : row17130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17130 := by decide +kernel

theorem rowEval17130 (x : Key → ℝ) : Integer.Sparse.eval row17130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17130, Integer.Sparse.eval_collectBalanced, rawRowCheck17130]

theorem rawRowCheck17131 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form5 = rawRow17131 := by decide +kernel

theorem rowCheck17131 : row17131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17131 := by decide +kernel

theorem rowEval17131 (x : Key → ℝ) : Integer.Sparse.eval row17131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17131, Integer.Sparse.eval_collectBalanced, rawRowCheck17131]

theorem rawRowCheck17132 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form5 = rawRow17132 := by decide +kernel

theorem rowCheck17132 : row17132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17132 := by decide +kernel

theorem rowEval17132 (x : Key → ℝ) : Integer.Sparse.eval row17132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17132, Integer.Sparse.eval_collectBalanced, rawRowCheck17132]

theorem rawRowCheck17133 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form5 = rawRow17133 := by decide +kernel

theorem rowCheck17133 : row17133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17133 := by decide +kernel

theorem rowEval17133 (x : Key → ℝ) : Integer.Sparse.eval row17133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17133, Integer.Sparse.eval_collectBalanced, rawRowCheck17133]

theorem rawRowCheck17134 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form5 = rawRow17134 := by decide +kernel

theorem rowCheck17134 : row17134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17134 := by decide +kernel

theorem rowEval17134 (x : Key → ℝ) : Integer.Sparse.eval row17134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17134, Integer.Sparse.eval_collectBalanced, rawRowCheck17134]

theorem rawRowCheck17135 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form5 = rawRow17135 := by decide +kernel

theorem rowCheck17135 : row17135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17135 := by decide +kernel

theorem rowEval17135 (x : Key → ℝ) : Integer.Sparse.eval row17135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17135, Integer.Sparse.eval_collectBalanced, rawRowCheck17135]

theorem rawRowCheck17136 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form5 = rawRow17136 := by decide +kernel

theorem rowCheck17136 : row17136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17136 := by decide +kernel

theorem rowEval17136 (x : Key → ℝ) : Integer.Sparse.eval row17136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17136, Integer.Sparse.eval_collectBalanced, rawRowCheck17136]

theorem rawRowCheck17137 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form5 = rawRow17137 := by decide +kernel

theorem rowCheck17137 : row17137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17137 := by decide +kernel

theorem rowEval17137 (x : Key → ℝ) : Integer.Sparse.eval row17137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17137, Integer.Sparse.eval_collectBalanced, rawRowCheck17137]

theorem rawRowCheck17138 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form5 = rawRow17138 := by decide +kernel

theorem rowCheck17138 : row17138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17138 := by decide +kernel

theorem rowEval17138 (x : Key → ℝ) : Integer.Sparse.eval row17138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17138, Integer.Sparse.eval_collectBalanced, rawRowCheck17138]

theorem rawRowCheck17139 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form5 = rawRow17139 := by decide +kernel

theorem rowCheck17139 : row17139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17139 := by decide +kernel

theorem rowEval17139 (x : Key → ℝ) : Integer.Sparse.eval row17139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17139, Integer.Sparse.eval_collectBalanced, rawRowCheck17139]

theorem rawRowCheck17140 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form5 = rawRow17140 := by decide +kernel

theorem rowCheck17140 : row17140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17140 := by decide +kernel

theorem rowEval17140 (x : Key → ℝ) : Integer.Sparse.eval row17140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17140, Integer.Sparse.eval_collectBalanced, rawRowCheck17140]

theorem rawRowCheck17141 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form5 = rawRow17141 := by decide +kernel

theorem rowCheck17141 : row17141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17141 := by decide +kernel

theorem rowEval17141 (x : Key → ℝ) : Integer.Sparse.eval row17141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17141, Integer.Sparse.eval_collectBalanced, rawRowCheck17141]

theorem rawRowCheck17142 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form5 = rawRow17142 := by decide +kernel

theorem rowCheck17142 : row17142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17142 := by decide +kernel

theorem rowEval17142 (x : Key → ℝ) : Integer.Sparse.eval row17142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17142, Integer.Sparse.eval_collectBalanced, rawRowCheck17142]

theorem rawRowCheck17143 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form5 = rawRow17143 := by decide +kernel

theorem rowCheck17143 : row17143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17143 := by decide +kernel

theorem rowEval17143 (x : Key → ℝ) : Integer.Sparse.eval row17143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17143, Integer.Sparse.eval_collectBalanced, rawRowCheck17143]

theorem rawRowCheck17144 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form5 = rawRow17144 := by decide +kernel

theorem rowCheck17144 : row17144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17144 := by decide +kernel

theorem rowEval17144 (x : Key → ℝ) : Integer.Sparse.eval row17144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17144, Integer.Sparse.eval_collectBalanced, rawRowCheck17144]

theorem rawRowCheck17145 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form5 = rawRow17145 := by decide +kernel

theorem rowCheck17145 : row17145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17145 := by decide +kernel

theorem rowEval17145 (x : Key → ℝ) : Integer.Sparse.eval row17145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17145, Integer.Sparse.eval_collectBalanced, rawRowCheck17145]

theorem rawRowCheck17146 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form5 = rawRow17146 := by decide +kernel

theorem rowCheck17146 : row17146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17146 := by decide +kernel

theorem rowEval17146 (x : Key → ℝ) : Integer.Sparse.eval row17146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17146, Integer.Sparse.eval_collectBalanced, rawRowCheck17146]

theorem rawRowCheck17147 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow17147 := by decide +kernel

theorem rowCheck17147 : row17147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17147 := by decide +kernel

theorem rowEval17147 (x : Key → ℝ) : Integer.Sparse.eval row17147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17147, Integer.Sparse.eval_collectBalanced, rawRowCheck17147]

theorem rawRowCheck17148 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow17148 := by decide +kernel

theorem rowCheck17148 : row17148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17148 := by decide +kernel

theorem rowEval17148 (x : Key → ℝ) : Integer.Sparse.eval row17148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17148, Integer.Sparse.eval_collectBalanced, rawRowCheck17148]

theorem rawRowCheck17149 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow17149 := by decide +kernel

theorem rowCheck17149 : row17149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17149 := by decide +kernel

theorem rowEval17149 (x : Key → ℝ) : Integer.Sparse.eval row17149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17149, Integer.Sparse.eval_collectBalanced, rawRowCheck17149]

theorem rawRowCheck17150 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow17150 := by decide +kernel

theorem rowCheck17150 : row17150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17150 := by decide +kernel

theorem rowEval17150 (x : Key → ℝ) : Integer.Sparse.eval row17150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17150, Integer.Sparse.eval_collectBalanced, rawRowCheck17150]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17171 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form7 = rawRow17171 := by decide +kernel

theorem rowCheck17171 : row17171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17171 := by decide +kernel

theorem rowEval17171 (x : Key → ℝ) : Integer.Sparse.eval row17171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck17171, Integer.Sparse.eval_collectBalanced, rawRowCheck17171]

theorem rawRowCheck17172 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form7 = rawRow17172 := by decide +kernel

theorem rowCheck17172 : row17172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17172 := by decide +kernel

theorem rowEval17172 (x : Key → ℝ) : Integer.Sparse.eval row17172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17172, Integer.Sparse.eval_collectBalanced, rawRowCheck17172]

theorem rawRowCheck17173 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form7 = rawRow17173 := by decide +kernel

theorem rowCheck17173 : row17173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17173 := by decide +kernel

theorem rowEval17173 (x : Key → ℝ) : Integer.Sparse.eval row17173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck17173, Integer.Sparse.eval_collectBalanced, rawRowCheck17173]

theorem rawRowCheck17174 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form7 = rawRow17174 := by decide +kernel

theorem rowCheck17174 : row17174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17174 := by decide +kernel

theorem rowEval17174 (x : Key → ℝ) : Integer.Sparse.eval row17174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17174, Integer.Sparse.eval_collectBalanced, rawRowCheck17174]

theorem rawRowCheck17175 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form7 = rawRow17175 := by decide +kernel

theorem rowCheck17175 : row17175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17175 := by decide +kernel

theorem rowEval17175 (x : Key → ℝ) : Integer.Sparse.eval row17175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17175, Integer.Sparse.eval_collectBalanced, rawRowCheck17175]

theorem rawRowCheck17176 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form7 = rawRow17176 := by decide +kernel

theorem rowCheck17176 : row17176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17176 := by decide +kernel

theorem rowEval17176 (x : Key → ℝ) : Integer.Sparse.eval row17176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17176, Integer.Sparse.eval_collectBalanced, rawRowCheck17176]

theorem rawRowCheck17177 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form7 = rawRow17177 := by decide +kernel

theorem rowCheck17177 : row17177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17177 := by decide +kernel

theorem rowEval17177 (x : Key → ℝ) : Integer.Sparse.eval row17177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck17177, Integer.Sparse.eval_collectBalanced, rawRowCheck17177]

theorem rawRowCheck17178 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form7 = rawRow17178 := by decide +kernel

theorem rowCheck17178 : row17178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17178 := by decide +kernel

theorem rowEval17178 (x : Key → ℝ) : Integer.Sparse.eval row17178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17178, Integer.Sparse.eval_collectBalanced, rawRowCheck17178]

theorem rawRowCheck17179 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form7 = rawRow17179 := by decide +kernel

theorem rowCheck17179 : row17179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17179 := by decide +kernel

theorem rowEval17179 (x : Key → ℝ) : Integer.Sparse.eval row17179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17179, Integer.Sparse.eval_collectBalanced, rawRowCheck17179]

theorem rawRowCheck17180 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form7 = rawRow17180 := by decide +kernel

theorem rowCheck17180 : row17180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17180 := by decide +kernel

theorem rowEval17180 (x : Key → ℝ) : Integer.Sparse.eval row17180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17180, Integer.Sparse.eval_collectBalanced, rawRowCheck17180]

theorem rawRowCheck17181 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form7 = rawRow17181 := by decide +kernel

theorem rowCheck17181 : row17181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17181 := by decide +kernel

theorem rowEval17181 (x : Key → ℝ) : Integer.Sparse.eval row17181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17181, Integer.Sparse.eval_collectBalanced, rawRowCheck17181]

theorem rawRowCheck17182 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form7 = rawRow17182 := by decide +kernel

theorem rowCheck17182 : row17182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17182 := by decide +kernel

theorem rowEval17182 (x : Key → ℝ) : Integer.Sparse.eval row17182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17182, Integer.Sparse.eval_collectBalanced, rawRowCheck17182]

theorem rawRowCheck17183 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form7 = rawRow17183 := by decide +kernel

theorem rowCheck17183 : row17183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17183 := by decide +kernel

theorem rowEval17183 (x : Key → ℝ) : Integer.Sparse.eval row17183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck17183, Integer.Sparse.eval_collectBalanced, rawRowCheck17183]

theorem rawRowCheck17184 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form7 = rawRow17184 := by decide +kernel

theorem rowCheck17184 : row17184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17184 := by decide +kernel

theorem rowEval17184 (x : Key → ℝ) : Integer.Sparse.eval row17184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17184, Integer.Sparse.eval_collectBalanced, rawRowCheck17184]

theorem rawRowCheck17185 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form7 = rawRow17185 := by decide +kernel

theorem rowCheck17185 : row17185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17185 := by decide +kernel

theorem rowEval17185 (x : Key → ℝ) : Integer.Sparse.eval row17185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17185, Integer.Sparse.eval_collectBalanced, rawRowCheck17185]

theorem rawRowCheck17186 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form7 = rawRow17186 := by decide +kernel

theorem rowCheck17186 : row17186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17186 := by decide +kernel

theorem rowEval17186 (x : Key → ℝ) : Integer.Sparse.eval row17186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17186, Integer.Sparse.eval_collectBalanced, rawRowCheck17186]

theorem rawRowCheck17187 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow17187 := by decide +kernel

theorem rowCheck17187 : row17187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17187 := by decide +kernel

theorem rowEval17187 (x : Key → ℝ) : Integer.Sparse.eval row17187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17187, Integer.Sparse.eval_collectBalanced, rawRowCheck17187]

theorem rawRowCheck17188 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow17188 := by decide +kernel

theorem rowCheck17188 : row17188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17188 := by decide +kernel

theorem rowEval17188 (x : Key → ℝ) : Integer.Sparse.eval row17188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17188, Integer.Sparse.eval_collectBalanced, rawRowCheck17188]

theorem rawRowCheck17189 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow17189 := by decide +kernel

theorem rowCheck17189 : row17189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17189 := by decide +kernel

theorem rowEval17189 (x : Key → ℝ) : Integer.Sparse.eval row17189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17189, Integer.Sparse.eval_collectBalanced, rawRowCheck17189]

theorem rawRowCheck17190 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow17190 := by decide +kernel

theorem rowCheck17190 : row17190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17190 := by decide +kernel

theorem rowEval17190 (x : Key → ℝ) : Integer.Sparse.eval row17190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17190, Integer.Sparse.eval_collectBalanced, rawRowCheck17190]

theorem rawRowCheck17211 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form9 = rawRow17211 := by decide +kernel

theorem rowCheck17211 : row17211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17211 := by decide +kernel

theorem rowEval17211 (x : Key → ℝ) : Integer.Sparse.eval row17211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17211, Integer.Sparse.eval_collectBalanced, rawRowCheck17211]

theorem rawRowCheck17212 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form9 = rawRow17212 := by decide +kernel

theorem rowCheck17212 : row17212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17212 := by decide +kernel

theorem rowEval17212 (x : Key → ℝ) : Integer.Sparse.eval row17212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17212, Integer.Sparse.eval_collectBalanced, rawRowCheck17212]

theorem rawRowCheck17213 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form9 = rawRow17213 := by decide +kernel

theorem rowCheck17213 : row17213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17213 := by decide +kernel

theorem rowEval17213 (x : Key → ℝ) : Integer.Sparse.eval row17213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17213, Integer.Sparse.eval_collectBalanced, rawRowCheck17213]

theorem rawRowCheck17214 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form9 = rawRow17214 := by decide +kernel

theorem rowCheck17214 : row17214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17214 := by decide +kernel

theorem rowEval17214 (x : Key → ℝ) : Integer.Sparse.eval row17214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17214, Integer.Sparse.eval_collectBalanced, rawRowCheck17214]

theorem rawRowCheck17215 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form9 = rawRow17215 := by decide +kernel

theorem rowCheck17215 : row17215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17215 := by decide +kernel

theorem rowEval17215 (x : Key → ℝ) : Integer.Sparse.eval row17215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17215, Integer.Sparse.eval_collectBalanced, rawRowCheck17215]

theorem rawRowCheck17216 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form9 = rawRow17216 := by decide +kernel

theorem rowCheck17216 : row17216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17216 := by decide +kernel

theorem rowEval17216 (x : Key → ℝ) : Integer.Sparse.eval row17216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17216, Integer.Sparse.eval_collectBalanced, rawRowCheck17216]

theorem rawRowCheck17217 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form9 = rawRow17217 := by decide +kernel

theorem rowCheck17217 : row17217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17217 := by decide +kernel

theorem rowEval17217 (x : Key → ℝ) : Integer.Sparse.eval row17217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17217, Integer.Sparse.eval_collectBalanced, rawRowCheck17217]

theorem rawRowCheck17218 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form9 = rawRow17218 := by decide +kernel

theorem rowCheck17218 : row17218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17218 := by decide +kernel

theorem rowEval17218 (x : Key → ℝ) : Integer.Sparse.eval row17218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17218, Integer.Sparse.eval_collectBalanced, rawRowCheck17218]

theorem rawRowCheck17219 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form9 = rawRow17219 := by decide +kernel

theorem rowCheck17219 : row17219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17219 := by decide +kernel

theorem rowEval17219 (x : Key → ℝ) : Integer.Sparse.eval row17219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17219, Integer.Sparse.eval_collectBalanced, rawRowCheck17219]

theorem rawRowCheck17220 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form9 = rawRow17220 := by decide +kernel

theorem rowCheck17220 : row17220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17220 := by decide +kernel

theorem rowEval17220 (x : Key → ℝ) : Integer.Sparse.eval row17220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17220, Integer.Sparse.eval_collectBalanced, rawRowCheck17220]

theorem rawRowCheck17221 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form9 = rawRow17221 := by decide +kernel

theorem rowCheck17221 : row17221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17221 := by decide +kernel

theorem rowEval17221 (x : Key → ℝ) : Integer.Sparse.eval row17221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17221, Integer.Sparse.eval_collectBalanced, rawRowCheck17221]

theorem rawRowCheck17222 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form9 = rawRow17222 := by decide +kernel

theorem rowCheck17222 : row17222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17222 := by decide +kernel

theorem rowEval17222 (x : Key → ℝ) : Integer.Sparse.eval row17222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17222, Integer.Sparse.eval_collectBalanced, rawRowCheck17222]

theorem rawRowCheck17223 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form9 = rawRow17223 := by decide +kernel

theorem rowCheck17223 : row17223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17223 := by decide +kernel

theorem rowEval17223 (x : Key → ℝ) : Integer.Sparse.eval row17223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17223, Integer.Sparse.eval_collectBalanced, rawRowCheck17223]

theorem rawRowCheck17224 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form9 = rawRow17224 := by decide +kernel

theorem rowCheck17224 : row17224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17224 := by decide +kernel

theorem rowEval17224 (x : Key → ℝ) : Integer.Sparse.eval row17224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17224, Integer.Sparse.eval_collectBalanced, rawRowCheck17224]

theorem rawRowCheck17225 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form9 = rawRow17225 := by decide +kernel

theorem rowCheck17225 : row17225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17225 := by decide +kernel

theorem rowEval17225 (x : Key → ℝ) : Integer.Sparse.eval row17225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17225, Integer.Sparse.eval_collectBalanced, rawRowCheck17225]

theorem rawRowCheck17226 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form9 = rawRow17226 := by decide +kernel

theorem rowCheck17226 : row17226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17226 := by decide +kernel

theorem rowEval17226 (x : Key → ℝ) : Integer.Sparse.eval row17226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17226, Integer.Sparse.eval_collectBalanced, rawRowCheck17226]

theorem rawRowCheck17227 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow17227 := by decide +kernel

theorem rowCheck17227 : row17227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17227 := by decide +kernel

theorem rowEval17227 (x : Key → ℝ) : Integer.Sparse.eval row17227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17227, Integer.Sparse.eval_collectBalanced, rawRowCheck17227]

theorem rawRowCheck17228 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow17228 := by decide +kernel

theorem rowCheck17228 : row17228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17228 := by decide +kernel

theorem rowEval17228 (x : Key → ℝ) : Integer.Sparse.eval row17228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17228, Integer.Sparse.eval_collectBalanced, rawRowCheck17228]

theorem rawRowCheck17229 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow17229 := by decide +kernel

theorem rowCheck17229 : row17229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17229 := by decide +kernel

theorem rowEval17229 (x : Key → ℝ) : Integer.Sparse.eval row17229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17229, Integer.Sparse.eval_collectBalanced, rawRowCheck17229]

theorem rawRowCheck17230 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form9 = rawRow17230 := by decide +kernel

theorem rowCheck17230 : row17230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17230 := by decide +kernel

theorem rowEval17230 (x : Key → ℝ) : Integer.Sparse.eval row17230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17230, Integer.Sparse.eval_collectBalanced, rawRowCheck17230]

theorem rawRowCheck17251 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form11 = rawRow17251 := by decide +kernel

theorem rowCheck17251 : row17251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17251 := by decide +kernel

theorem rowEval17251 (x : Key → ℝ) : Integer.Sparse.eval row17251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17251, Integer.Sparse.eval_collectBalanced, rawRowCheck17251]

theorem rawRowCheck17252 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form11 = rawRow17252 := by decide +kernel

theorem rowCheck17252 : row17252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17252 := by decide +kernel

theorem rowEval17252 (x : Key → ℝ) : Integer.Sparse.eval row17252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17252, Integer.Sparse.eval_collectBalanced, rawRowCheck17252]

theorem rawRowCheck17253 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form11 = rawRow17253 := by decide +kernel

theorem rowCheck17253 : row17253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17253 := by decide +kernel

theorem rowEval17253 (x : Key → ℝ) : Integer.Sparse.eval row17253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17253, Integer.Sparse.eval_collectBalanced, rawRowCheck17253]

theorem rawRowCheck17254 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form11 = rawRow17254 := by decide +kernel

theorem rowCheck17254 : row17254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17254 := by decide +kernel

theorem rowEval17254 (x : Key → ℝ) : Integer.Sparse.eval row17254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17254, Integer.Sparse.eval_collectBalanced, rawRowCheck17254]

theorem rawRowCheck17255 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form11 = rawRow17255 := by decide +kernel

theorem rowCheck17255 : row17255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17255 := by decide +kernel

theorem rowEval17255 (x : Key → ℝ) : Integer.Sparse.eval row17255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17255, Integer.Sparse.eval_collectBalanced, rawRowCheck17255]

theorem rawRowCheck17256 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form11 = rawRow17256 := by decide +kernel

theorem rowCheck17256 : row17256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17256 := by decide +kernel

theorem rowEval17256 (x : Key → ℝ) : Integer.Sparse.eval row17256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17256, Integer.Sparse.eval_collectBalanced, rawRowCheck17256]

theorem rawRowCheck17257 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form11 = rawRow17257 := by decide +kernel

theorem rowCheck17257 : row17257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17257 := by decide +kernel

theorem rowEval17257 (x : Key → ℝ) : Integer.Sparse.eval row17257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17257, Integer.Sparse.eval_collectBalanced, rawRowCheck17257]

theorem rawRowCheck17258 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form11 = rawRow17258 := by decide +kernel

theorem rowCheck17258 : row17258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17258 := by decide +kernel

theorem rowEval17258 (x : Key → ℝ) : Integer.Sparse.eval row17258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17258, Integer.Sparse.eval_collectBalanced, rawRowCheck17258]

theorem rawRowCheck17259 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form11 = rawRow17259 := by decide +kernel

theorem rowCheck17259 : row17259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17259 := by decide +kernel

theorem rowEval17259 (x : Key → ℝ) : Integer.Sparse.eval row17259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17259, Integer.Sparse.eval_collectBalanced, rawRowCheck17259]

theorem rawRowCheck17260 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form11 = rawRow17260 := by decide +kernel

theorem rowCheck17260 : row17260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17260 := by decide +kernel

theorem rowEval17260 (x : Key → ℝ) : Integer.Sparse.eval row17260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17260, Integer.Sparse.eval_collectBalanced, rawRowCheck17260]

theorem rawRowCheck17261 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form11 = rawRow17261 := by decide +kernel

theorem rowCheck17261 : row17261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17261 := by decide +kernel

theorem rowEval17261 (x : Key → ℝ) : Integer.Sparse.eval row17261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17261, Integer.Sparse.eval_collectBalanced, rawRowCheck17261]

theorem rawRowCheck17262 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form11 = rawRow17262 := by decide +kernel

theorem rowCheck17262 : row17262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17262 := by decide +kernel

theorem rowEval17262 (x : Key → ℝ) : Integer.Sparse.eval row17262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17262, Integer.Sparse.eval_collectBalanced, rawRowCheck17262]

theorem rawRowCheck17263 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form11 = rawRow17263 := by decide +kernel

theorem rowCheck17263 : row17263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17263 := by decide +kernel

theorem rowEval17263 (x : Key → ℝ) : Integer.Sparse.eval row17263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17263, Integer.Sparse.eval_collectBalanced, rawRowCheck17263]

theorem rawRowCheck17264 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form11 = rawRow17264 := by decide +kernel

theorem rowCheck17264 : row17264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17264 := by decide +kernel

theorem rowEval17264 (x : Key → ℝ) : Integer.Sparse.eval row17264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17264, Integer.Sparse.eval_collectBalanced, rawRowCheck17264]

theorem rawRowCheck17265 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form11 = rawRow17265 := by decide +kernel

theorem rowCheck17265 : row17265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17265 := by decide +kernel

theorem rowEval17265 (x : Key → ℝ) : Integer.Sparse.eval row17265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17265, Integer.Sparse.eval_collectBalanced, rawRowCheck17265]

theorem rawRowCheck17266 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form11 = rawRow17266 := by decide +kernel

theorem rowCheck17266 : row17266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17266 := by decide +kernel

theorem rowEval17266 (x : Key → ℝ) : Integer.Sparse.eval row17266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17266, Integer.Sparse.eval_collectBalanced, rawRowCheck17266]

theorem rawRowCheck17267 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form11 = rawRow17267 := by decide +kernel

theorem rowCheck17267 : row17267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17267 := by decide +kernel

theorem rowEval17267 (x : Key → ℝ) : Integer.Sparse.eval row17267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17267, Integer.Sparse.eval_collectBalanced, rawRowCheck17267]

theorem rawRowCheck17268 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form11 = rawRow17268 := by decide +kernel

theorem rowCheck17268 : row17268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17268 := by decide +kernel

theorem rowEval17268 (x : Key → ℝ) : Integer.Sparse.eval row17268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17268, Integer.Sparse.eval_collectBalanced, rawRowCheck17268]

theorem rawRowCheck17269 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form11 = rawRow17269 := by decide +kernel

theorem rowCheck17269 : row17269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17269 := by decide +kernel

theorem rowEval17269 (x : Key → ℝ) : Integer.Sparse.eval row17269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17269, Integer.Sparse.eval_collectBalanced, rawRowCheck17269]

theorem rawRowCheck17270 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form11 = rawRow17270 := by decide +kernel

theorem rowCheck17270 : row17270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17270 := by decide +kernel

theorem rowEval17270 (x : Key → ℝ) : Integer.Sparse.eval row17270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17270, Integer.Sparse.eval_collectBalanced, rawRowCheck17270]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17391 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form18 = rawRow17391 := by decide +kernel

theorem rowCheck17391 : row17391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17391 := by decide +kernel

theorem rowEval17391 (x : Key → ℝ) : Integer.Sparse.eval row17391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form18) x := by
  rw [rowCheck17391, Integer.Sparse.eval_collectBalanced, rawRowCheck17391]

theorem rawRowCheck17392 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form18 = rawRow17392 := by decide +kernel

theorem rowCheck17392 : row17392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17392 := by decide +kernel

theorem rowEval17392 (x : Key → ℝ) : Integer.Sparse.eval row17392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17392, Integer.Sparse.eval_collectBalanced, rawRowCheck17392]

theorem rawRowCheck17393 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form18 = rawRow17393 := by decide +kernel

theorem rowCheck17393 : row17393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17393 := by decide +kernel

theorem rowEval17393 (x : Key → ℝ) : Integer.Sparse.eval row17393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form18) x := by
  rw [rowCheck17393, Integer.Sparse.eval_collectBalanced, rawRowCheck17393]

theorem rawRowCheck17394 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form18 = rawRow17394 := by decide +kernel

theorem rowCheck17394 : row17394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17394 := by decide +kernel

theorem rowEval17394 (x : Key → ℝ) : Integer.Sparse.eval row17394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17394, Integer.Sparse.eval_collectBalanced, rawRowCheck17394]

theorem rawRowCheck17395 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form18 = rawRow17395 := by decide +kernel

theorem rowCheck17395 : row17395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17395 := by decide +kernel

theorem rowEval17395 (x : Key → ℝ) : Integer.Sparse.eval row17395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17395, Integer.Sparse.eval_collectBalanced, rawRowCheck17395]

theorem rawRowCheck17396 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form18 = rawRow17396 := by decide +kernel

theorem rowCheck17396 : row17396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17396 := by decide +kernel

theorem rowEval17396 (x : Key → ℝ) : Integer.Sparse.eval row17396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17396, Integer.Sparse.eval_collectBalanced, rawRowCheck17396]

theorem rawRowCheck17397 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form18 = rawRow17397 := by decide +kernel

theorem rowCheck17397 : row17397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17397 := by decide +kernel

theorem rowEval17397 (x : Key → ℝ) : Integer.Sparse.eval row17397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form18) x := by
  rw [rowCheck17397, Integer.Sparse.eval_collectBalanced, rawRowCheck17397]

theorem rawRowCheck17398 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form18 = rawRow17398 := by decide +kernel

theorem rowCheck17398 : row17398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17398 := by decide +kernel

theorem rowEval17398 (x : Key → ℝ) : Integer.Sparse.eval row17398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17398, Integer.Sparse.eval_collectBalanced, rawRowCheck17398]

theorem rawRowCheck17399 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form18 = rawRow17399 := by decide +kernel

theorem rowCheck17399 : row17399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17399 := by decide +kernel

theorem rowEval17399 (x : Key → ℝ) : Integer.Sparse.eval row17399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17399, Integer.Sparse.eval_collectBalanced, rawRowCheck17399]

theorem rawRowCheck17400 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form18 = rawRow17400 := by decide +kernel

theorem rowCheck17400 : row17400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17400 := by decide +kernel

theorem rowEval17400 (x : Key → ℝ) : Integer.Sparse.eval row17400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17400, Integer.Sparse.eval_collectBalanced, rawRowCheck17400]

theorem rawRowCheck17401 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form18 = rawRow17401 := by decide +kernel

theorem rowCheck17401 : row17401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17401 := by decide +kernel

theorem rowEval17401 (x : Key → ℝ) : Integer.Sparse.eval row17401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17401, Integer.Sparse.eval_collectBalanced, rawRowCheck17401]

theorem rawRowCheck17402 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form18 = rawRow17402 := by decide +kernel

theorem rowCheck17402 : row17402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17402 := by decide +kernel

theorem rowEval17402 (x : Key → ℝ) : Integer.Sparse.eval row17402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17402, Integer.Sparse.eval_collectBalanced, rawRowCheck17402]

theorem rawRowCheck17403 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form18 = rawRow17403 := by decide +kernel

theorem rowCheck17403 : row17403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17403 := by decide +kernel

theorem rowEval17403 (x : Key → ℝ) : Integer.Sparse.eval row17403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form18) x := by
  rw [rowCheck17403, Integer.Sparse.eval_collectBalanced, rawRowCheck17403]

theorem rawRowCheck17404 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form18 = rawRow17404 := by decide +kernel

theorem rowCheck17404 : row17404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17404 := by decide +kernel

theorem rowEval17404 (x : Key → ℝ) : Integer.Sparse.eval row17404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17404, Integer.Sparse.eval_collectBalanced, rawRowCheck17404]

theorem rawRowCheck17405 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form18 = rawRow17405 := by decide +kernel

theorem rowCheck17405 : row17405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17405 := by decide +kernel

theorem rowEval17405 (x : Key → ℝ) : Integer.Sparse.eval row17405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17405, Integer.Sparse.eval_collectBalanced, rawRowCheck17405]

theorem rawRowCheck17406 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form18 = rawRow17406 := by decide +kernel

theorem rowCheck17406 : row17406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17406 := by decide +kernel

theorem rowEval17406 (x : Key → ℝ) : Integer.Sparse.eval row17406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17406, Integer.Sparse.eval_collectBalanced, rawRowCheck17406]

theorem rawRowCheck17407 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form18 = rawRow17407 := by decide +kernel

theorem rowCheck17407 : row17407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17407 := by decide +kernel

theorem rowEval17407 (x : Key → ℝ) : Integer.Sparse.eval row17407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17407, Integer.Sparse.eval_collectBalanced, rawRowCheck17407]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck17408 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form18 = rawRow17408 := by decide +kernel

theorem rowCheck17408 : row17408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17408 := by decide +kernel

theorem rowEval17408 (x : Key → ℝ) : Integer.Sparse.eval row17408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17408, Integer.Sparse.eval_collectBalanced, rawRowCheck17408]

theorem rawRowCheck17409 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form18 = rawRow17409 := by decide +kernel

theorem rowCheck17409 : row17409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17409 := by decide +kernel

theorem rowEval17409 (x : Key → ℝ) : Integer.Sparse.eval row17409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17409, Integer.Sparse.eval_collectBalanced, rawRowCheck17409]

theorem rawRowCheck17410 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form18 = rawRow17410 := by decide +kernel

theorem rowCheck17410 : row17410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17410 := by decide +kernel

theorem rowEval17410 (x : Key → ℝ) : Integer.Sparse.eval row17410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17410, Integer.Sparse.eval_collectBalanced, rawRowCheck17410]

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

theorem entryCheck18_1 : entry18_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_1 k)) := by decide +kernel

theorem rowsSound18_1 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval17051 x
  · exact rowEval17052 x
  · exact rowEval17053 x
  · exact rowEval17054 x
  · exact rowEval17055 x
  · exact rowEval17056 x
  · exact rowEval17057 x
  · exact rowEval17058 x
  · exact rowEval17059 x
  · exact rowEval17060 x
  · exact rowEval17061 x
  · exact rowEval17062 x
  · exact rowEval17063 x
  · exact rowEval17064 x
  · exact rowEval17065 x
  · exact rowEval17066 x
  · exact rowEval17067 x
  · exact rowEval17068 x
  · exact rowEval17069 x
  · exact rowEval17070 x

theorem entryEval18_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_1 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck18_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_1]

theorem entryCheck18_2 : entry18_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_2 k)) := by decide +kernel

theorem rowsSound18_2 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval17071 x
  · exact rowEval17072 x
  · exact rowEval17073 x
  · exact rowEval17074 x
  · exact rowEval17075 x
  · exact rowEval17076 x
  · exact rowEval17077 x
  · exact rowEval17078 x
  · exact rowEval17079 x
  · exact rowEval17080 x
  · exact rowEval17081 x
  · exact rowEval17082 x
  · exact rowEval17083 x
  · exact rowEval17084 x
  · exact rowEval17085 x
  · exact rowEval17086 x
  · exact rowEval17087 x
  · exact rowEval17088 x
  · exact rowEval17089 x
  · exact rowEval17090 x

theorem entryEval18_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_2 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck18_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_2]

theorem entryCheck18_3 : entry18_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_3 k)) := by decide +kernel

theorem rowsSound18_3 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval17091 x
  · exact rowEval17092 x
  · exact rowEval17093 x
  · exact rowEval17094 x
  · exact rowEval17095 x
  · exact rowEval17096 x
  · exact rowEval17097 x
  · exact rowEval17098 x
  · exact rowEval17099 x
  · exact rowEval17100 x
  · exact rowEval17101 x
  · exact rowEval17102 x
  · exact rowEval17103 x
  · exact rowEval17104 x
  · exact rowEval17105 x
  · exact rowEval17106 x
  · exact rowEval17107 x
  · exact rowEval17108 x
  · exact rowEval17109 x
  · exact rowEval17110 x

theorem entryEval18_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_3 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck18_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_3]

theorem entryCheck18_4 : entry18_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_4 k)) := by decide +kernel

theorem rowsSound18_4 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17111 x
  · exact rowEval17112 x
  · exact rowEval17113 x
  · exact rowEval17114 x
  · exact rowEval17115 x
  · exact rowEval17116 x
  · exact rowEval17117 x
  · exact rowEval17118 x
  · exact rowEval17119 x
  · exact rowEval17120 x
  · exact rowEval17121 x
  · exact rowEval17122 x
  · exact rowEval17123 x
  · exact rowEval17124 x
  · exact rowEval17125 x
  · exact rowEval17126 x
  · exact rowEval17127 x
  · exact rowEval17128 x
  · exact rowEval17129 x
  · exact rowEval17130 x

theorem entryEval18_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_4 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck18_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_4]

theorem entryCheck18_5 : entry18_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_5 k)) := by decide +kernel

theorem rowsSound18_5 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17131 x
  · exact rowEval17132 x
  · exact rowEval17133 x
  · exact rowEval17134 x
  · exact rowEval17135 x
  · exact rowEval17136 x
  · exact rowEval17137 x
  · exact rowEval17138 x
  · exact rowEval17139 x
  · exact rowEval17140 x
  · exact rowEval17141 x
  · exact rowEval17142 x
  · exact rowEval17143 x
  · exact rowEval17144 x
  · exact rowEval17145 x
  · exact rowEval17146 x
  · exact rowEval17147 x
  · exact rowEval17148 x
  · exact rowEval17149 x
  · exact rowEval17150 x

theorem entryEval18_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_5 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck18_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_5]

theorem entryCheck18_7 : entry18_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_7 k)) := by decide +kernel

theorem rowsSound18_7 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval17171 x
  · exact rowEval17172 x
  · exact rowEval17173 x
  · exact rowEval17174 x
  · exact rowEval17175 x
  · exact rowEval17176 x
  · exact rowEval17177 x
  · exact rowEval17178 x
  · exact rowEval17179 x
  · exact rowEval17180 x
  · exact rowEval17181 x
  · exact rowEval17182 x
  · exact rowEval17183 x
  · exact rowEval17184 x
  · exact rowEval17185 x
  · exact rowEval17186 x
  · exact rowEval17187 x
  · exact rowEval17188 x
  · exact rowEval17189 x
  · exact rowEval17190 x

theorem entryEval18_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_7 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck18_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_7]

theorem entryCheck18_9 : entry18_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_9 k)) := by decide +kernel

theorem rowsSound18_9 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17211 x
  · exact rowEval17212 x
  · exact rowEval17213 x
  · exact rowEval17214 x
  · exact rowEval17215 x
  · exact rowEval17216 x
  · exact rowEval17217 x
  · exact rowEval17218 x
  · exact rowEval17219 x
  · exact rowEval17220 x
  · exact rowEval17221 x
  · exact rowEval17222 x
  · exact rowEval17223 x
  · exact rowEval17224 x
  · exact rowEval17225 x
  · exact rowEval17226 x
  · exact rowEval17227 x
  · exact rowEval17228 x
  · exact rowEval17229 x
  · exact rowEval17230 x

theorem entryEval18_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_9 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck18_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_9]

theorem entryCheck18_11 : entry18_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_11 k)) := by decide +kernel

theorem rowsSound18_11 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval17251 x
  · exact rowEval17252 x
  · exact rowEval17253 x
  · exact rowEval17254 x
  · exact rowEval17255 x
  · exact rowEval17256 x
  · exact rowEval17257 x
  · exact rowEval17258 x
  · exact rowEval17259 x
  · exact rowEval17260 x
  · exact rowEval17261 x
  · exact rowEval17262 x
  · exact rowEval17263 x
  · exact rowEval17264 x
  · exact rowEval17265 x
  · exact rowEval17266 x
  · exact rowEval17267 x
  · exact rowEval17268 x
  · exact rowEval17269 x
  · exact rowEval17270 x

theorem entryEval18_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_11 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck18_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_11]

theorem entryCheck18_18 : entry18_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_18 k)) := by decide +kernel

theorem rowsSound18_18 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form18) x := by
  fin_cases k
  · exact rowEval17391 x
  · exact rowEval17392 x
  · exact rowEval17393 x
  · exact rowEval17394 x
  · exact rowEval17395 x
  · exact rowEval17396 x
  · exact rowEval17397 x
  · exact rowEval17398 x
  · exact rowEval17399 x
  · exact rowEval17400 x
  · exact rowEval17401 x
  · exact rowEval17402 x
  · exact rowEval17403 x
  · exact rowEval17404 x
  · exact rowEval17405 x
  · exact rowEval17406 x
  · exact rowEval17407 x
  · exact rowEval17408 x
  · exact rowEval17409 x
  · exact rowEval17410 x

theorem entryEval18_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_18 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form18 B := by
  rw [entryCheck18_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_18]

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

theorem rawRowCheck17591 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form18 = rawRow17591 := by decide +kernel

theorem rowCheck17591 : row17591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17591 := by decide +kernel

theorem rowEval17591 (x : Key → ℝ) : Integer.Sparse.eval row17591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17591, Integer.Sparse.eval_collectBalanced, rawRowCheck17591]

theorem rawRowCheck17592 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form18 = rawRow17592 := by decide +kernel

theorem rowCheck17592 : row17592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17592 := by decide +kernel

theorem rowEval17592 (x : Key → ℝ) : Integer.Sparse.eval row17592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17592, Integer.Sparse.eval_collectBalanced, rawRowCheck17592]

theorem rawRowCheck17593 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form18 = rawRow17593 := by decide +kernel

theorem rowCheck17593 : row17593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17593 := by decide +kernel

theorem rowEval17593 (x : Key → ℝ) : Integer.Sparse.eval row17593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17593, Integer.Sparse.eval_collectBalanced, rawRowCheck17593]

theorem rawRowCheck17594 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form18 = rawRow17594 := by decide +kernel

theorem rowCheck17594 : row17594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17594 := by decide +kernel

theorem rowEval17594 (x : Key → ℝ) : Integer.Sparse.eval row17594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17594, Integer.Sparse.eval_collectBalanced, rawRowCheck17594]

theorem rawRowCheck17595 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form18 = rawRow17595 := by decide +kernel

theorem rowCheck17595 : row17595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17595 := by decide +kernel

theorem rowEval17595 (x : Key → ℝ) : Integer.Sparse.eval row17595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17595, Integer.Sparse.eval_collectBalanced, rawRowCheck17595]

theorem rawRowCheck17596 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form18 = rawRow17596 := by decide +kernel

theorem rowCheck17596 : row17596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17596 := by decide +kernel

theorem rowEval17596 (x : Key → ℝ) : Integer.Sparse.eval row17596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17596, Integer.Sparse.eval_collectBalanced, rawRowCheck17596]

theorem rawRowCheck17597 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form18 = rawRow17597 := by decide +kernel

theorem rowCheck17597 : row17597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17597 := by decide +kernel

theorem rowEval17597 (x : Key → ℝ) : Integer.Sparse.eval row17597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17597, Integer.Sparse.eval_collectBalanced, rawRowCheck17597]

theorem rawRowCheck17598 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form18 = rawRow17598 := by decide +kernel

theorem rowCheck17598 : row17598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17598 := by decide +kernel

theorem rowEval17598 (x : Key → ℝ) : Integer.Sparse.eval row17598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17598, Integer.Sparse.eval_collectBalanced, rawRowCheck17598]

theorem rawRowCheck17599 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form18 = rawRow17599 := by decide +kernel

theorem rowCheck17599 : row17599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17599 := by decide +kernel

theorem rowEval17599 (x : Key → ℝ) : Integer.Sparse.eval row17599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17599, Integer.Sparse.eval_collectBalanced, rawRowCheck17599]

theorem rawRowCheck17600 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form18 = rawRow17600 := by decide +kernel

theorem rowCheck17600 : row17600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17600 := by decide +kernel

theorem rowEval17600 (x : Key → ℝ) : Integer.Sparse.eval row17600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17600, Integer.Sparse.eval_collectBalanced, rawRowCheck17600]

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

theorem entryCheck19_18 : entry19_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_18 k)) := by decide +kernel

theorem rowsSound19_18 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form18) x := by
  fin_cases k
  · exact rowEval17591 x
  · exact rowEval17592 x
  · exact rowEval17593 x
  · exact rowEval17594 x
  · exact rowEval17595 x
  · exact rowEval17596 x
  · exact rowEval17597 x
  · exact rowEval17598 x
  · exact rowEval17599 x
  · exact rowEval17600 x

theorem entryEval19_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_18 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form18 B := by
  rw [entryCheck19_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_18]

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

theorem entryEvalRow18_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 18 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 18).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval18_0 B hB
  · exact entryEval18_1 B hB
  · exact entryEval18_2 B hB
  · exact entryEval18_3 B hB
  · exact entryEval18_4 B hB
  · exact entryEval18_5 B hB
  · exact entryEval18_6_e B hB
  · exact entryEval18_7 B hB
  · exact entryEval18_8_e B hB
  · exact entryEval18_9 B hB
  · exact entryEval18_10_e B hB
  · exact entryEval18_11 B hB
  · exact entryEval18_12_e B hB
  · exact entryEval18_13_e B hB
  · exact entryEval18_14_e B hB
  · exact entryEval18_15_e B hB
  · exact entryEval18_16_e B hB
  · exact entryEval18_17_e B hB
  · exact entryEval18_18 B hB
  · exact (entryEval19_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_18_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e_oai
