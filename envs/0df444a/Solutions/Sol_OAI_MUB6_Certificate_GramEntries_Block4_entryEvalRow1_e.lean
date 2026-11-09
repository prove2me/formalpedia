-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:54:25.620799+00:00
-- url     : https://prove2.me/submissions/549e77ba-f97a-458f-bf60-c095035a6a1d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E034
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval10_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval6_1_e

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

theorem rawRowCheck13225 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form1 = rawRow13225 := by decide +kernel

theorem rowCheck13225 : row13225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13225 := by decide +kernel

theorem rowEval13225 (x : Key → ℝ) : Integer.Sparse.eval row13225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13225, Integer.Sparse.eval_collectBalanced, rawRowCheck13225]

theorem rawRowCheck13226 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form1 = rawRow13226 := by decide +kernel

theorem rowCheck13226 : row13226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13226 := by decide +kernel

theorem rowEval13226 (x : Key → ℝ) : Integer.Sparse.eval row13226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13226, Integer.Sparse.eval_collectBalanced, rawRowCheck13226]

theorem rawRowCheck13227 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form1 = rawRow13227 := by decide +kernel

theorem rowCheck13227 : row13227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13227 := by decide +kernel

theorem rowEval13227 (x : Key → ℝ) : Integer.Sparse.eval row13227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13227, Integer.Sparse.eval_collectBalanced, rawRowCheck13227]

theorem rawRowCheck13228 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13228 := by decide +kernel

theorem rowCheck13228 : row13228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13228 := by decide +kernel

theorem rowEval13228 (x : Key → ℝ) : Integer.Sparse.eval row13228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13228, Integer.Sparse.eval_collectBalanced, rawRowCheck13228]

theorem rawRowCheck13229 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form1 = rawRow13229 := by decide +kernel

theorem rowCheck13229 : row13229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13229 := by decide +kernel

theorem rowEval13229 (x : Key → ℝ) : Integer.Sparse.eval row13229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13229, Integer.Sparse.eval_collectBalanced, rawRowCheck13229]

theorem rawRowCheck13230 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form1 = rawRow13230 := by decide +kernel

theorem rowCheck13230 : row13230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13230 := by decide +kernel

theorem rowEval13230 (x : Key → ℝ) : Integer.Sparse.eval row13230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13230, Integer.Sparse.eval_collectBalanced, rawRowCheck13230]

theorem rawRowCheck13231 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form1 = rawRow13231 := by decide +kernel

theorem rowCheck13231 : row13231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13231 := by decide +kernel

theorem rowEval13231 (x : Key → ℝ) : Integer.Sparse.eval row13231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13231, Integer.Sparse.eval_collectBalanced, rawRowCheck13231]

theorem rawRowCheck13232 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form1 = rawRow13232 := by decide +kernel

theorem rowCheck13232 : row13232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13232 := by decide +kernel

theorem rowEval13232 (x : Key → ℝ) : Integer.Sparse.eval row13232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13232, Integer.Sparse.eval_collectBalanced, rawRowCheck13232]

theorem rawRowCheck13233 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form1 = rawRow13233 := by decide +kernel

theorem rowCheck13233 : row13233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13233 := by decide +kernel

theorem rowEval13233 (x : Key → ℝ) : Integer.Sparse.eval row13233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13233, Integer.Sparse.eval_collectBalanced, rawRowCheck13233]

theorem rawRowCheck13234 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form1 = rawRow13234 := by decide +kernel

theorem rowCheck13234 : row13234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13234 := by decide +kernel

theorem rowEval13234 (x : Key → ℝ) : Integer.Sparse.eval row13234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13234, Integer.Sparse.eval_collectBalanced, rawRowCheck13234]

theorem rawRowCheck13235 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form1 = rawRow13235 := by decide +kernel

theorem rowCheck13235 : row13235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13235 := by decide +kernel

theorem rowEval13235 (x : Key → ℝ) : Integer.Sparse.eval row13235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13235, Integer.Sparse.eval_collectBalanced, rawRowCheck13235]

theorem rawRowCheck13236 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form1 = rawRow13236 := by decide +kernel

theorem rowCheck13236 : row13236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13236 := by decide +kernel

theorem rowEval13236 (x : Key → ℝ) : Integer.Sparse.eval row13236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13236, Integer.Sparse.eval_collectBalanced, rawRowCheck13236]

theorem rawRowCheck13237 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form1 = rawRow13237 := by decide +kernel

theorem rowCheck13237 : row13237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13237 := by decide +kernel

theorem rowEval13237 (x : Key → ℝ) : Integer.Sparse.eval row13237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13237, Integer.Sparse.eval_collectBalanced, rawRowCheck13237]

theorem rawRowCheck13238 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13238 := by decide +kernel

theorem rowCheck13238 : row13238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13238 := by decide +kernel

theorem rowEval13238 (x : Key → ℝ) : Integer.Sparse.eval row13238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13238, Integer.Sparse.eval_collectBalanced, rawRowCheck13238]

theorem rawRowCheck13239 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13239 := by decide +kernel

theorem rowCheck13239 : row13239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13239 := by decide +kernel

theorem rowEval13239 (x : Key → ℝ) : Integer.Sparse.eval row13239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13239, Integer.Sparse.eval_collectBalanced, rawRowCheck13239]

theorem rawRowCheck13240 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13240 := by decide +kernel

theorem rowCheck13240 : row13240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13240 := by decide +kernel

theorem rowEval13240 (x : Key → ℝ) : Integer.Sparse.eval row13240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13240, Integer.Sparse.eval_collectBalanced, rawRowCheck13240]

theorem rawRowCheck13241 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13241 := by decide +kernel

theorem rowCheck13241 : row13241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13241 := by decide +kernel

theorem rowEval13241 (x : Key → ℝ) : Integer.Sparse.eval row13241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13241, Integer.Sparse.eval_collectBalanced, rawRowCheck13241]

theorem rawRowCheck13242 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13242 := by decide +kernel

theorem rowCheck13242 : row13242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13242 := by decide +kernel

theorem rowEval13242 (x : Key → ℝ) : Integer.Sparse.eval row13242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13242, Integer.Sparse.eval_collectBalanced, rawRowCheck13242]

theorem rawRowCheck13243 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13243 := by decide +kernel

theorem rowCheck13243 : row13243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13243 := by decide +kernel

theorem rowEval13243 (x : Key → ℝ) : Integer.Sparse.eval row13243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13243, Integer.Sparse.eval_collectBalanced, rawRowCheck13243]

theorem rawRowCheck13244 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13244 := by decide +kernel

theorem rowCheck13244 : row13244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13244 := by decide +kernel

theorem rowEval13244 (x : Key → ℝ) : Integer.Sparse.eval row13244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13244, Integer.Sparse.eval_collectBalanced, rawRowCheck13244]

theorem rawRowCheck13265 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form1 = rawRow13265 := by decide +kernel

theorem rowCheck13265 : row13265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13265 := by decide +kernel

theorem rowEval13265 (x : Key → ℝ) : Integer.Sparse.eval row13265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13265, Integer.Sparse.eval_collectBalanced, rawRowCheck13265]

theorem rawRowCheck13266 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form1 = rawRow13266 := by decide +kernel

theorem rowCheck13266 : row13266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13266 := by decide +kernel

theorem rowEval13266 (x : Key → ℝ) : Integer.Sparse.eval row13266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13266, Integer.Sparse.eval_collectBalanced, rawRowCheck13266]

theorem rawRowCheck13267 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form1 = rawRow13267 := by decide +kernel

theorem rowCheck13267 : row13267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13267 := by decide +kernel

theorem rowEval13267 (x : Key → ℝ) : Integer.Sparse.eval row13267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13267, Integer.Sparse.eval_collectBalanced, rawRowCheck13267]

theorem rawRowCheck13268 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13268 := by decide +kernel

theorem rowCheck13268 : row13268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13268 := by decide +kernel

theorem rowEval13268 (x : Key → ℝ) : Integer.Sparse.eval row13268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13268, Integer.Sparse.eval_collectBalanced, rawRowCheck13268]

theorem rawRowCheck13269 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form1 = rawRow13269 := by decide +kernel

theorem rowCheck13269 : row13269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13269 := by decide +kernel

theorem rowEval13269 (x : Key → ℝ) : Integer.Sparse.eval row13269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13269, Integer.Sparse.eval_collectBalanced, rawRowCheck13269]

theorem rawRowCheck13270 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form1 = rawRow13270 := by decide +kernel

theorem rowCheck13270 : row13270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13270 := by decide +kernel

theorem rowEval13270 (x : Key → ℝ) : Integer.Sparse.eval row13270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13270, Integer.Sparse.eval_collectBalanced, rawRowCheck13270]

theorem rawRowCheck13271 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form1 = rawRow13271 := by decide +kernel

theorem rowCheck13271 : row13271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13271 := by decide +kernel

theorem rowEval13271 (x : Key → ℝ) : Integer.Sparse.eval row13271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13271, Integer.Sparse.eval_collectBalanced, rawRowCheck13271]

theorem rawRowCheck13272 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form1 = rawRow13272 := by decide +kernel

theorem rowCheck13272 : row13272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13272 := by decide +kernel

theorem rowEval13272 (x : Key → ℝ) : Integer.Sparse.eval row13272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13272, Integer.Sparse.eval_collectBalanced, rawRowCheck13272]

theorem rawRowCheck13273 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form1 = rawRow13273 := by decide +kernel

theorem rowCheck13273 : row13273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13273 := by decide +kernel

theorem rowEval13273 (x : Key → ℝ) : Integer.Sparse.eval row13273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13273, Integer.Sparse.eval_collectBalanced, rawRowCheck13273]

theorem rawRowCheck13274 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form1 = rawRow13274 := by decide +kernel

theorem rowCheck13274 : row13274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13274 := by decide +kernel

theorem rowEval13274 (x : Key → ℝ) : Integer.Sparse.eval row13274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13274, Integer.Sparse.eval_collectBalanced, rawRowCheck13274]

theorem rawRowCheck13275 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form1 = rawRow13275 := by decide +kernel

theorem rowCheck13275 : row13275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13275 := by decide +kernel

theorem rowEval13275 (x : Key → ℝ) : Integer.Sparse.eval row13275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13275, Integer.Sparse.eval_collectBalanced, rawRowCheck13275]

theorem rawRowCheck13276 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form1 = rawRow13276 := by decide +kernel

theorem rowCheck13276 : row13276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13276 := by decide +kernel

theorem rowEval13276 (x : Key → ℝ) : Integer.Sparse.eval row13276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13276, Integer.Sparse.eval_collectBalanced, rawRowCheck13276]

theorem rawRowCheck13277 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form1 = rawRow13277 := by decide +kernel

theorem rowCheck13277 : row13277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13277 := by decide +kernel

theorem rowEval13277 (x : Key → ℝ) : Integer.Sparse.eval row13277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13277, Integer.Sparse.eval_collectBalanced, rawRowCheck13277]

theorem rawRowCheck13278 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13278 := by decide +kernel

theorem rowCheck13278 : row13278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13278 := by decide +kernel

theorem rowEval13278 (x : Key → ℝ) : Integer.Sparse.eval row13278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13278, Integer.Sparse.eval_collectBalanced, rawRowCheck13278]

theorem rawRowCheck13279 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13279 := by decide +kernel

theorem rowCheck13279 : row13279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13279 := by decide +kernel

theorem rowEval13279 (x : Key → ℝ) : Integer.Sparse.eval row13279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13279, Integer.Sparse.eval_collectBalanced, rawRowCheck13279]

theorem rawRowCheck13280 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13280 := by decide +kernel

theorem rowCheck13280 : row13280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13280 := by decide +kernel

theorem rowEval13280 (x : Key → ℝ) : Integer.Sparse.eval row13280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13280, Integer.Sparse.eval_collectBalanced, rawRowCheck13280]

theorem rawRowCheck13281 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13281 := by decide +kernel

theorem rowCheck13281 : row13281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13281 := by decide +kernel

theorem rowEval13281 (x : Key → ℝ) : Integer.Sparse.eval row13281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13281, Integer.Sparse.eval_collectBalanced, rawRowCheck13281]

theorem rawRowCheck13282 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13282 := by decide +kernel

theorem rowCheck13282 : row13282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13282 := by decide +kernel

theorem rowEval13282 (x : Key → ℝ) : Integer.Sparse.eval row13282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13282, Integer.Sparse.eval_collectBalanced, rawRowCheck13282]

theorem rawRowCheck13283 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13283 := by decide +kernel

theorem rowCheck13283 : row13283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13283 := by decide +kernel

theorem rowEval13283 (x : Key → ℝ) : Integer.Sparse.eval row13283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13283, Integer.Sparse.eval_collectBalanced, rawRowCheck13283]

theorem rawRowCheck13284 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13284 := by decide +kernel

theorem rowCheck13284 : row13284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13284 := by decide +kernel

theorem rowEval13284 (x : Key → ℝ) : Integer.Sparse.eval row13284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13284, Integer.Sparse.eval_collectBalanced, rawRowCheck13284]

end MUB6.Certificate.GramRows

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

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block4.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form1.terms k).tag (GramFunctions.Block4.form1.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13225 x
  · exact rowEval13226 x
  · exact rowEval13227 x
  · exact rowEval13228 x
  · exact rowEval13229 x
  · exact rowEval13230 x
  · exact rowEval13231 x
  · exact rowEval13232 x
  · exact rowEval13233 x
  · exact rowEval13234 x
  · exact rowEval13235 x
  · exact rowEval13236 x
  · exact rowEval13237 x
  · exact rowEval13238 x
  · exact rowEval13239 x
  · exact rowEval13240 x
  · exact rowEval13241 x
  · exact rowEval13242 x
  · exact rowEval13243 x
  · exact rowEval13244 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block4.form1.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form1 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

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

theorem rawRowCheck14115 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form1 = rawRow14115 := by decide +kernel

theorem rowCheck14115 : row14115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14115 := by decide +kernel

theorem rowEval14115 (x : Key → ℝ) : Integer.Sparse.eval row14115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14115, Integer.Sparse.eval_collectBalanced, rawRowCheck14115]

theorem rawRowCheck14116 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form1 = rawRow14116 := by decide +kernel

theorem rowCheck14116 : row14116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14116 := by decide +kernel

theorem rowEval14116 (x : Key → ℝ) : Integer.Sparse.eval row14116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14116, Integer.Sparse.eval_collectBalanced, rawRowCheck14116]

theorem rawRowCheck14117 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form1 = rawRow14117 := by decide +kernel

theorem rowCheck14117 : row14117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14117 := by decide +kernel

theorem rowEval14117 (x : Key → ℝ) : Integer.Sparse.eval row14117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14117, Integer.Sparse.eval_collectBalanced, rawRowCheck14117]

theorem rawRowCheck14118 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form1 = rawRow14118 := by decide +kernel

theorem rowCheck14118 : row14118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14118 := by decide +kernel

theorem rowEval14118 (x : Key → ℝ) : Integer.Sparse.eval row14118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14118, Integer.Sparse.eval_collectBalanced, rawRowCheck14118]

theorem rawRowCheck14119 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form1 = rawRow14119 := by decide +kernel

theorem rowCheck14119 : row14119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14119 := by decide +kernel

theorem rowEval14119 (x : Key → ℝ) : Integer.Sparse.eval row14119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14119, Integer.Sparse.eval_collectBalanced, rawRowCheck14119]

theorem rawRowCheck14120 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form1 = rawRow14120 := by decide +kernel

theorem rowCheck14120 : row14120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14120 := by decide +kernel

theorem rowEval14120 (x : Key → ℝ) : Integer.Sparse.eval row14120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14120, Integer.Sparse.eval_collectBalanced, rawRowCheck14120]

theorem rawRowCheck14121 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow14121 := by decide +kernel

theorem rowCheck14121 : row14121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14121 := by decide +kernel

theorem rowEval14121 (x : Key → ℝ) : Integer.Sparse.eval row14121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14121, Integer.Sparse.eval_collectBalanced, rawRowCheck14121]

theorem rawRowCheck14122 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow14122 := by decide +kernel

theorem rowCheck14122 : row14122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14122 := by decide +kernel

theorem rowEval14122 (x : Key → ℝ) : Integer.Sparse.eval row14122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14122, Integer.Sparse.eval_collectBalanced, rawRowCheck14122]

theorem rawRowCheck14123 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow14123 := by decide +kernel

theorem rowCheck14123 : row14123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14123 := by decide +kernel

theorem rowEval14123 (x : Key → ℝ) : Integer.Sparse.eval row14123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14123, Integer.Sparse.eval_collectBalanced, rawRowCheck14123]

theorem rawRowCheck14124 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow14124 := by decide +kernel

theorem rowCheck14124 : row14124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14124 := by decide +kernel

theorem rowEval14124 (x : Key → ℝ) : Integer.Sparse.eval row14124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck14124, Integer.Sparse.eval_collectBalanced, rawRowCheck14124]

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

theorem rawRowCheck14621 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form1 = rawRow14621 := by decide +kernel

theorem rowCheck14621 : row14621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14621 := by decide +kernel

theorem rowEval14621 (x : Key → ℝ) : Integer.Sparse.eval row14621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14621, Integer.Sparse.eval_collectBalanced, rawRowCheck14621]

theorem rawRowCheck14622 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form1 = rawRow14622 := by decide +kernel

theorem rowCheck14622 : row14622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14622 := by decide +kernel

theorem rowEval14622 (x : Key → ℝ) : Integer.Sparse.eval row14622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14622, Integer.Sparse.eval_collectBalanced, rawRowCheck14622]

theorem rawRowCheck14623 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form1 = rawRow14623 := by decide +kernel

theorem rowCheck14623 : row14623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14623 := by decide +kernel

theorem rowEval14623 (x : Key → ℝ) : Integer.Sparse.eval row14623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14623, Integer.Sparse.eval_collectBalanced, rawRowCheck14623]

theorem rawRowCheck14624 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow14624 := by decide +kernel

theorem rowCheck14624 : row14624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14624 := by decide +kernel

theorem rowEval14624 (x : Key → ℝ) : Integer.Sparse.eval row14624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14624, Integer.Sparse.eval_collectBalanced, rawRowCheck14624]

theorem rawRowCheck14625 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form1 = rawRow14625 := by decide +kernel

theorem rowCheck14625 : row14625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14625 := by decide +kernel

theorem rowEval14625 (x : Key → ℝ) : Integer.Sparse.eval row14625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14625, Integer.Sparse.eval_collectBalanced, rawRowCheck14625]

theorem rawRowCheck14626 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form1 = rawRow14626 := by decide +kernel

theorem rowCheck14626 : row14626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14626 := by decide +kernel

theorem rowEval14626 (x : Key → ℝ) : Integer.Sparse.eval row14626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14626, Integer.Sparse.eval_collectBalanced, rawRowCheck14626]

theorem rawRowCheck14627 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form1 = rawRow14627 := by decide +kernel

theorem rowCheck14627 : row14627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14627 := by decide +kernel

theorem rowEval14627 (x : Key → ℝ) : Integer.Sparse.eval row14627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14627, Integer.Sparse.eval_collectBalanced, rawRowCheck14627]

theorem rawRowCheck14628 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form1 = rawRow14628 := by decide +kernel

theorem rowCheck14628 : row14628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14628 := by decide +kernel

theorem rowEval14628 (x : Key → ℝ) : Integer.Sparse.eval row14628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14628, Integer.Sparse.eval_collectBalanced, rawRowCheck14628]

theorem rawRowCheck14629 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form1 = rawRow14629 := by decide +kernel

theorem rowCheck14629 : row14629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14629 := by decide +kernel

theorem rowEval14629 (x : Key → ℝ) : Integer.Sparse.eval row14629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14629, Integer.Sparse.eval_collectBalanced, rawRowCheck14629]

theorem rawRowCheck14630 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form1 = rawRow14630 := by decide +kernel

theorem rowCheck14630 : row14630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14630 := by decide +kernel

theorem rowEval14630 (x : Key → ℝ) : Integer.Sparse.eval row14630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14630, Integer.Sparse.eval_collectBalanced, rawRowCheck14630]

theorem rawRowCheck14631 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form1 = rawRow14631 := by decide +kernel

theorem rowCheck14631 : row14631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14631 := by decide +kernel

theorem rowEval14631 (x : Key → ℝ) : Integer.Sparse.eval row14631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14631, Integer.Sparse.eval_collectBalanced, rawRowCheck14631]

theorem rawRowCheck14632 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form1 = rawRow14632 := by decide +kernel

theorem rowCheck14632 : row14632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14632 := by decide +kernel

theorem rowEval14632 (x : Key → ℝ) : Integer.Sparse.eval row14632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14632, Integer.Sparse.eval_collectBalanced, rawRowCheck14632]

theorem rawRowCheck14633 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form1 = rawRow14633 := by decide +kernel

theorem rowCheck14633 : row14633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14633 := by decide +kernel

theorem rowEval14633 (x : Key → ℝ) : Integer.Sparse.eval row14633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14633, Integer.Sparse.eval_collectBalanced, rawRowCheck14633]

theorem rawRowCheck14634 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form1 = rawRow14634 := by decide +kernel

theorem rowCheck14634 : row14634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14634 := by decide +kernel

theorem rowEval14634 (x : Key → ℝ) : Integer.Sparse.eval row14634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14634, Integer.Sparse.eval_collectBalanced, rawRowCheck14634]

theorem rawRowCheck14635 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form1 = rawRow14635 := by decide +kernel

theorem rowCheck14635 : row14635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14635 := by decide +kernel

theorem rowEval14635 (x : Key → ℝ) : Integer.Sparse.eval row14635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14635, Integer.Sparse.eval_collectBalanced, rawRowCheck14635]

theorem rawRowCheck14636 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form1 = rawRow14636 := by decide +kernel

theorem rowCheck14636 : row14636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14636 := by decide +kernel

theorem rowEval14636 (x : Key → ℝ) : Integer.Sparse.eval row14636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14636, Integer.Sparse.eval_collectBalanced, rawRowCheck14636]

theorem rawRowCheck14637 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow14637 := by decide +kernel

theorem rowCheck14637 : row14637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14637 := by decide +kernel

theorem rowEval14637 (x : Key → ℝ) : Integer.Sparse.eval row14637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14637, Integer.Sparse.eval_collectBalanced, rawRowCheck14637]

theorem rawRowCheck14638 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form1 = rawRow14638 := by decide +kernel

theorem rowCheck14638 : row14638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14638 := by decide +kernel

theorem rowEval14638 (x : Key → ℝ) : Integer.Sparse.eval row14638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14638, Integer.Sparse.eval_collectBalanced, rawRowCheck14638]

theorem rawRowCheck14639 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form1 = rawRow14639 := by decide +kernel

theorem rowCheck14639 : row14639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14639 := by decide +kernel

theorem rowEval14639 (x : Key → ℝ) : Integer.Sparse.eval row14639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14639, Integer.Sparse.eval_collectBalanced, rawRowCheck14639]

theorem rawRowCheck14640 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form1 = rawRow14640 := by decide +kernel

theorem rowCheck14640 : row14640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14640 := by decide +kernel

theorem rowEval14640 (x : Key → ℝ) : Integer.Sparse.eval row14640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14640, Integer.Sparse.eval_collectBalanced, rawRowCheck14640]

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

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval14621 x
  · exact rowEval14622 x
  · exact rowEval14623 x
  · exact rowEval14624 x
  · exact rowEval14625 x
  · exact rowEval14626 x
  · exact rowEval14627 x
  · exact rowEval14628 x
  · exact rowEval14629 x
  · exact rowEval14630 x
  · exact rowEval14631 x
  · exact rowEval14632 x
  · exact rowEval14633 x
  · exact rowEval14634 x
  · exact rowEval14635 x
  · exact rowEval14636 x
  · exact rowEval14637 x
  · exact rowEval14638 x
  · exact rowEval14639 x
  · exact rowEval14640 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

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

theorem rawRowCheck13855 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form1 = rawRow13855 := by decide +kernel

theorem rowCheck13855 : row13855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13855 := by decide +kernel

theorem rowEval13855 (x : Key → ℝ) : Integer.Sparse.eval row13855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13855, Integer.Sparse.eval_collectBalanced, rawRowCheck13855]

theorem rawRowCheck13856 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form1 = rawRow13856 := by decide +kernel

theorem rowCheck13856 : row13856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13856 := by decide +kernel

theorem rowEval13856 (x : Key → ℝ) : Integer.Sparse.eval row13856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13856, Integer.Sparse.eval_collectBalanced, rawRowCheck13856]

theorem rawRowCheck13857 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form1 = rawRow13857 := by decide +kernel

theorem rowCheck13857 : row13857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13857 := by decide +kernel

theorem rowEval13857 (x : Key → ℝ) : Integer.Sparse.eval row13857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13857, Integer.Sparse.eval_collectBalanced, rawRowCheck13857]

theorem rawRowCheck13858 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form1 = rawRow13858 := by decide +kernel

theorem rowCheck13858 : row13858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13858 := by decide +kernel

theorem rowEval13858 (x : Key → ℝ) : Integer.Sparse.eval row13858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13858, Integer.Sparse.eval_collectBalanced, rawRowCheck13858]

theorem rawRowCheck13859 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form1 = rawRow13859 := by decide +kernel

theorem rowCheck13859 : row13859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13859 := by decide +kernel

theorem rowEval13859 (x : Key → ℝ) : Integer.Sparse.eval row13859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13859, Integer.Sparse.eval_collectBalanced, rawRowCheck13859]

theorem rawRowCheck13860 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form1 = rawRow13860 := by decide +kernel

theorem rowCheck13860 : row13860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13860 := by decide +kernel

theorem rowEval13860 (x : Key → ℝ) : Integer.Sparse.eval row13860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13860, Integer.Sparse.eval_collectBalanced, rawRowCheck13860]

theorem rawRowCheck13861 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow13861 := by decide +kernel

theorem rowCheck13861 : row13861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13861 := by decide +kernel

theorem rowEval13861 (x : Key → ℝ) : Integer.Sparse.eval row13861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13861, Integer.Sparse.eval_collectBalanced, rawRowCheck13861]

theorem rawRowCheck13862 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow13862 := by decide +kernel

theorem rowCheck13862 : row13862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13862 := by decide +kernel

theorem rowEval13862 (x : Key → ℝ) : Integer.Sparse.eval row13862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13862, Integer.Sparse.eval_collectBalanced, rawRowCheck13862]

theorem rawRowCheck13863 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow13863 := by decide +kernel

theorem rowCheck13863 : row13863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13863 := by decide +kernel

theorem rowEval13863 (x : Key → ℝ) : Integer.Sparse.eval row13863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13863, Integer.Sparse.eval_collectBalanced, rawRowCheck13863]

theorem rawRowCheck13864 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow13864 := by decide +kernel

theorem rowCheck13864 : row13864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13864 := by decide +kernel

theorem rowEval13864 (x : Key → ℝ) : Integer.Sparse.eval row13864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13864, Integer.Sparse.eval_collectBalanced, rawRowCheck13864]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

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

theorem rawRowCheck17421 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form1 = rawRow17421 := by decide +kernel

theorem rowCheck17421 : row17421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17421 := by decide +kernel

theorem rowEval17421 (x : Key → ℝ) : Integer.Sparse.eval row17421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17421, Integer.Sparse.eval_collectBalanced, rawRowCheck17421]

theorem rawRowCheck17422 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form1 = rawRow17422 := by decide +kernel

theorem rowCheck17422 : row17422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17422 := by decide +kernel

theorem rowEval17422 (x : Key → ℝ) : Integer.Sparse.eval row17422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17422, Integer.Sparse.eval_collectBalanced, rawRowCheck17422]

theorem rawRowCheck17423 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form1 = rawRow17423 := by decide +kernel

theorem rowCheck17423 : row17423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17423 := by decide +kernel

theorem rowEval17423 (x : Key → ℝ) : Integer.Sparse.eval row17423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17423, Integer.Sparse.eval_collectBalanced, rawRowCheck17423]

theorem rawRowCheck17424 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form1 = rawRow17424 := by decide +kernel

theorem rowCheck17424 : row17424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17424 := by decide +kernel

theorem rowEval17424 (x : Key → ℝ) : Integer.Sparse.eval row17424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17424, Integer.Sparse.eval_collectBalanced, rawRowCheck17424]

theorem rawRowCheck17425 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form1 = rawRow17425 := by decide +kernel

theorem rowCheck17425 : row17425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17425 := by decide +kernel

theorem rowEval17425 (x : Key → ℝ) : Integer.Sparse.eval row17425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17425, Integer.Sparse.eval_collectBalanced, rawRowCheck17425]

theorem rawRowCheck17426 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form1 = rawRow17426 := by decide +kernel

theorem rowCheck17426 : row17426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17426 := by decide +kernel

theorem rowEval17426 (x : Key → ℝ) : Integer.Sparse.eval row17426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17426, Integer.Sparse.eval_collectBalanced, rawRowCheck17426]

theorem rawRowCheck17427 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form1 = rawRow17427 := by decide +kernel

theorem rowCheck17427 : row17427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17427 := by decide +kernel

theorem rowEval17427 (x : Key → ℝ) : Integer.Sparse.eval row17427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17427, Integer.Sparse.eval_collectBalanced, rawRowCheck17427]

theorem rawRowCheck17428 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form1 = rawRow17428 := by decide +kernel

theorem rowCheck17428 : row17428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17428 := by decide +kernel

theorem rowEval17428 (x : Key → ℝ) : Integer.Sparse.eval row17428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17428, Integer.Sparse.eval_collectBalanced, rawRowCheck17428]

theorem rawRowCheck17429 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form1 = rawRow17429 := by decide +kernel

theorem rowCheck17429 : row17429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17429 := by decide +kernel

theorem rowEval17429 (x : Key → ℝ) : Integer.Sparse.eval row17429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17429, Integer.Sparse.eval_collectBalanced, rawRowCheck17429]

theorem rawRowCheck17430 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow17430 := by decide +kernel

theorem rowCheck17430 : row17430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17430 := by decide +kernel

theorem rowEval17430 (x : Key → ℝ) : Integer.Sparse.eval row17430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17430, Integer.Sparse.eval_collectBalanced, rawRowCheck17430]

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

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval17421 x
  · exact rowEval17422 x
  · exact rowEval17423 x
  · exact rowEval17424 x
  · exact rowEval17425 x
  · exact rowEval17426 x
  · exact rowEval17427 x
  · exact rowEval17428 x
  · exact rowEval17429 x
  · exact rowEval17430 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

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

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block4.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form2.terms k).tag (GramFunctions.Block4.form2.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13265 x
  · exact rowEval13266 x
  · exact rowEval13267 x
  · exact rowEval13268 x
  · exact rowEval13269 x
  · exact rowEval13270 x
  · exact rowEval13271 x
  · exact rowEval13272 x
  · exact rowEval13273 x
  · exact rowEval13274 x
  · exact rowEval13275 x
  · exact rowEval13276 x
  · exact rowEval13277 x
  · exact rowEval13278 x
  · exact rowEval13279 x
  · exact rowEval13280 x
  · exact rowEval13281 x
  · exact rowEval13282 x
  · exact rowEval13283 x
  · exact rowEval13284 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block4.form2.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form2 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

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

theorem rawRowCheck18009 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form1 = rawRow18009 := by decide +kernel

theorem rowCheck18009 : row18009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18009 := by decide +kernel

theorem rowEval18009 (x : Key → ℝ) : Integer.Sparse.eval row18009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18009, Integer.Sparse.eval_collectBalanced, rawRowCheck18009]

theorem rawRowCheck18010 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form1 = rawRow18010 := by decide +kernel

theorem rowCheck18010 : row18010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18010 := by decide +kernel

theorem rowEval18010 (x : Key → ℝ) : Integer.Sparse.eval row18010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18010, Integer.Sparse.eval_collectBalanced, rawRowCheck18010]

theorem rawRowCheck18011 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form1 = rawRow18011 := by decide +kernel

theorem rowCheck18011 : row18011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18011 := by decide +kernel

theorem rowEval18011 (x : Key → ℝ) : Integer.Sparse.eval row18011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18011, Integer.Sparse.eval_collectBalanced, rawRowCheck18011]

theorem rawRowCheck18012 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form1 = rawRow18012 := by decide +kernel

theorem rowCheck18012 : row18012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18012 := by decide +kernel

theorem rowEval18012 (x : Key → ℝ) : Integer.Sparse.eval row18012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18012, Integer.Sparse.eval_collectBalanced, rawRowCheck18012]

theorem rawRowCheck18013 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form1 = rawRow18013 := by decide +kernel

theorem rowCheck18013 : row18013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18013 := by decide +kernel

theorem rowEval18013 (x : Key → ℝ) : Integer.Sparse.eval row18013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18013, Integer.Sparse.eval_collectBalanced, rawRowCheck18013]

theorem rawRowCheck18014 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form1 = rawRow18014 := by decide +kernel

theorem rowCheck18014 : row18014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18014 := by decide +kernel

theorem rowEval18014 (x : Key → ℝ) : Integer.Sparse.eval row18014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18014, Integer.Sparse.eval_collectBalanced, rawRowCheck18014]

theorem rawRowCheck18015 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form1 = rawRow18015 := by decide +kernel

theorem rowCheck18015 : row18015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18015 := by decide +kernel

theorem rowEval18015 (x : Key → ℝ) : Integer.Sparse.eval row18015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18015, Integer.Sparse.eval_collectBalanced, rawRowCheck18015]

theorem rawRowCheck18016 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form1 = rawRow18016 := by decide +kernel

theorem rowCheck18016 : row18016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18016 := by decide +kernel

theorem rowEval18016 (x : Key → ℝ) : Integer.Sparse.eval row18016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18016, Integer.Sparse.eval_collectBalanced, rawRowCheck18016]

theorem rawRowCheck18017 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form1 = rawRow18017 := by decide +kernel

theorem rowCheck18017 : row18017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18017 := by decide +kernel

theorem rowEval18017 (x : Key → ℝ) : Integer.Sparse.eval row18017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18017, Integer.Sparse.eval_collectBalanced, rawRowCheck18017]

theorem rawRowCheck18018 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow18018 := by decide +kernel

theorem rowCheck18018 : row18018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18018 := by decide +kernel

theorem rowEval18018 (x : Key → ℝ) : Integer.Sparse.eval row18018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18018, Integer.Sparse.eval_collectBalanced, rawRowCheck18018]

theorem rawRowCheck18019 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow18019 := by decide +kernel

theorem rowCheck18019 : row18019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18019 := by decide +kernel

theorem rowEval18019 (x : Key → ℝ) : Integer.Sparse.eval row18019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18019, Integer.Sparse.eval_collectBalanced, rawRowCheck18019]

theorem rawRowCheck18020 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow18020 := by decide +kernel

theorem rowCheck18020 : row18020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18020 := by decide +kernel

theorem rowEval18020 (x : Key → ℝ) : Integer.Sparse.eval row18020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18020, Integer.Sparse.eval_collectBalanced, rawRowCheck18020]

theorem rawRowCheck18021 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form1 = rawRow18021 := by decide +kernel

theorem rowCheck18021 : row18021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18021 := by decide +kernel

theorem rowEval18021 (x : Key → ℝ) : Integer.Sparse.eval row18021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18021, Integer.Sparse.eval_collectBalanced, rawRowCheck18021]

theorem rawRowCheck18022 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form1 = rawRow18022 := by decide +kernel

theorem rowCheck18022 : row18022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18022 := by decide +kernel

theorem rowEval18022 (x : Key → ℝ) : Integer.Sparse.eval row18022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18022, Integer.Sparse.eval_collectBalanced, rawRowCheck18022]

theorem rawRowCheck18023 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form1 = rawRow18023 := by decide +kernel

theorem rowCheck18023 : row18023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18023 := by decide +kernel

theorem rowEval18023 (x : Key → ℝ) : Integer.Sparse.eval row18023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18023, Integer.Sparse.eval_collectBalanced, rawRowCheck18023]

theorem rawRowCheck18024 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form1 = rawRow18024 := by decide +kernel

theorem rowCheck18024 : row18024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18024 := by decide +kernel

theorem rowEval18024 (x : Key → ℝ) : Integer.Sparse.eval row18024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18024, Integer.Sparse.eval_collectBalanced, rawRowCheck18024]

theorem rawRowCheck18025 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow18025 := by decide +kernel

theorem rowCheck18025 : row18025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18025 := by decide +kernel

theorem rowEval18025 (x : Key → ℝ) : Integer.Sparse.eval row18025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18025, Integer.Sparse.eval_collectBalanced, rawRowCheck18025]

theorem rawRowCheck18026 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow18026 := by decide +kernel

theorem rowCheck18026 : row18026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18026 := by decide +kernel

theorem rowEval18026 (x : Key → ℝ) : Integer.Sparse.eval row18026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18026, Integer.Sparse.eval_collectBalanced, rawRowCheck18026]

theorem rawRowCheck18027 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow18027 := by decide +kernel

theorem rowCheck18027 : row18027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18027 := by decide +kernel

theorem rowEval18027 (x : Key → ℝ) : Integer.Sparse.eval row18027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18027, Integer.Sparse.eval_collectBalanced, rawRowCheck18027]

theorem rawRowCheck18028 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow18028 := by decide +kernel

theorem rowCheck18028 : row18028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18028 := by decide +kernel

theorem rowEval18028 (x : Key → ℝ) : Integer.Sparse.eval row18028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18028, Integer.Sparse.eval_collectBalanced, rawRowCheck18028]

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

theorem entryCheck21_1 : entry21_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_1 k)) := by decide +kernel

theorem rowsSound21_1 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval18009 x
  · exact rowEval18010 x
  · exact rowEval18011 x
  · exact rowEval18012 x
  · exact rowEval18013 x
  · exact rowEval18014 x
  · exact rowEval18015 x
  · exact rowEval18016 x
  · exact rowEval18017 x
  · exact rowEval18018 x
  · exact rowEval18019 x
  · exact rowEval18020 x
  · exact rowEval18021 x
  · exact rowEval18022 x
  · exact rowEval18023 x
  · exact rowEval18024 x
  · exact rowEval18025 x
  · exact rowEval18026 x
  · exact rowEval18027 x
  · exact rowEval18028 x

theorem entryEval21_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_1 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck21_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_1]

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

theorem rawRowCheck13325 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13325 := by decide +kernel

theorem rowCheck13325 : row13325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13325 := by decide +kernel

theorem rowEval13325 (x : Key → ℝ) : Integer.Sparse.eval row13325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13325, Integer.Sparse.eval_collectBalanced, rawRowCheck13325]

theorem rawRowCheck13326 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form1 = rawRow13326 := by decide +kernel

theorem rowCheck13326 : row13326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13326 := by decide +kernel

theorem rowEval13326 (x : Key → ℝ) : Integer.Sparse.eval row13326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13326, Integer.Sparse.eval_collectBalanced, rawRowCheck13326]

theorem rawRowCheck13327 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form1 = rawRow13327 := by decide +kernel

theorem rowCheck13327 : row13327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13327 := by decide +kernel

theorem rowEval13327 (x : Key → ℝ) : Integer.Sparse.eval row13327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13327, Integer.Sparse.eval_collectBalanced, rawRowCheck13327]

theorem rawRowCheck13328 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form1 = rawRow13328 := by decide +kernel

theorem rowCheck13328 : row13328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13328 := by decide +kernel

theorem rowEval13328 (x : Key → ℝ) : Integer.Sparse.eval row13328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13328, Integer.Sparse.eval_collectBalanced, rawRowCheck13328]

theorem rawRowCheck13329 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13329 := by decide +kernel

theorem rowCheck13329 : row13329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13329 := by decide +kernel

theorem rowEval13329 (x : Key → ℝ) : Integer.Sparse.eval row13329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13329, Integer.Sparse.eval_collectBalanced, rawRowCheck13329]

theorem rawRowCheck13330 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form1 = rawRow13330 := by decide +kernel

theorem rowCheck13330 : row13330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13330 := by decide +kernel

theorem rowEval13330 (x : Key → ℝ) : Integer.Sparse.eval row13330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13330, Integer.Sparse.eval_collectBalanced, rawRowCheck13330]

theorem rawRowCheck13331 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form1 = rawRow13331 := by decide +kernel

theorem rowCheck13331 : row13331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13331 := by decide +kernel

theorem rowEval13331 (x : Key → ℝ) : Integer.Sparse.eval row13331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13331, Integer.Sparse.eval_collectBalanced, rawRowCheck13331]

theorem rawRowCheck13332 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form1 = rawRow13332 := by decide +kernel

theorem rowCheck13332 : row13332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13332 := by decide +kernel

theorem rowEval13332 (x : Key → ℝ) : Integer.Sparse.eval row13332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13332, Integer.Sparse.eval_collectBalanced, rawRowCheck13332]

theorem rawRowCheck13333 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form1 = rawRow13333 := by decide +kernel

theorem rowCheck13333 : row13333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13333 := by decide +kernel

theorem rowEval13333 (x : Key → ℝ) : Integer.Sparse.eval row13333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13333, Integer.Sparse.eval_collectBalanced, rawRowCheck13333]

theorem rawRowCheck13334 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form1 = rawRow13334 := by decide +kernel

theorem rowCheck13334 : row13334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13334 := by decide +kernel

theorem rowEval13334 (x : Key → ℝ) : Integer.Sparse.eval row13334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13334, Integer.Sparse.eval_collectBalanced, rawRowCheck13334]

theorem rawRowCheck13335 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form1 = rawRow13335 := by decide +kernel

theorem rowCheck13335 : row13335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13335 := by decide +kernel

theorem rowEval13335 (x : Key → ℝ) : Integer.Sparse.eval row13335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13335, Integer.Sparse.eval_collectBalanced, rawRowCheck13335]

theorem rawRowCheck13336 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form1 = rawRow13336 := by decide +kernel

theorem rowCheck13336 : row13336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13336 := by decide +kernel

theorem rowEval13336 (x : Key → ℝ) : Integer.Sparse.eval row13336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13336, Integer.Sparse.eval_collectBalanced, rawRowCheck13336]

theorem rawRowCheck13337 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form1 = rawRow13337 := by decide +kernel

theorem rowCheck13337 : row13337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13337 := by decide +kernel

theorem rowEval13337 (x : Key → ℝ) : Integer.Sparse.eval row13337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13337, Integer.Sparse.eval_collectBalanced, rawRowCheck13337]

theorem rawRowCheck13338 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form1 = rawRow13338 := by decide +kernel

theorem rowCheck13338 : row13338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13338 := by decide +kernel

theorem rowEval13338 (x : Key → ℝ) : Integer.Sparse.eval row13338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13338, Integer.Sparse.eval_collectBalanced, rawRowCheck13338]

theorem rawRowCheck13339 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form1 = rawRow13339 := by decide +kernel

theorem rowCheck13339 : row13339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13339 := by decide +kernel

theorem rowEval13339 (x : Key → ℝ) : Integer.Sparse.eval row13339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13339, Integer.Sparse.eval_collectBalanced, rawRowCheck13339]

theorem rawRowCheck13340 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form1 = rawRow13340 := by decide +kernel

theorem rowCheck13340 : row13340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13340 := by decide +kernel

theorem rowEval13340 (x : Key → ℝ) : Integer.Sparse.eval row13340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13340, Integer.Sparse.eval_collectBalanced, rawRowCheck13340]

theorem rawRowCheck13341 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form1 = rawRow13341 := by decide +kernel

theorem rowCheck13341 : row13341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13341 := by decide +kernel

theorem rowEval13341 (x : Key → ℝ) : Integer.Sparse.eval row13341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13341, Integer.Sparse.eval_collectBalanced, rawRowCheck13341]

theorem rawRowCheck13342 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form1 = rawRow13342 := by decide +kernel

theorem rowCheck13342 : row13342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13342 := by decide +kernel

theorem rowEval13342 (x : Key → ℝ) : Integer.Sparse.eval row13342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13342, Integer.Sparse.eval_collectBalanced, rawRowCheck13342]

theorem rawRowCheck13343 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form1 = rawRow13343 := by decide +kernel

theorem rowCheck13343 : row13343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13343 := by decide +kernel

theorem rowEval13343 (x : Key → ℝ) : Integer.Sparse.eval row13343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13343, Integer.Sparse.eval_collectBalanced, rawRowCheck13343]

theorem rawRowCheck13344 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form1 = rawRow13344 := by decide +kernel

theorem rowCheck13344 : row13344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13344 := by decide +kernel

theorem rowEval13344 (x : Key → ℝ) : Integer.Sparse.eval row13344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13344, Integer.Sparse.eval_collectBalanced, rawRowCheck13344]

theorem rawRowCheck13405 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13405 := by decide +kernel

theorem rowCheck13405 : row13405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13405 := by decide +kernel

theorem rowEval13405 (x : Key → ℝ) : Integer.Sparse.eval row13405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13405, Integer.Sparse.eval_collectBalanced, rawRowCheck13405]

theorem rawRowCheck13406 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13406 := by decide +kernel

theorem rowCheck13406 : row13406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13406 := by decide +kernel

theorem rowEval13406 (x : Key → ℝ) : Integer.Sparse.eval row13406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13406, Integer.Sparse.eval_collectBalanced, rawRowCheck13406]

theorem rawRowCheck13407 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13407 := by decide +kernel

theorem rowCheck13407 : row13407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13407 := by decide +kernel

theorem rowEval13407 (x : Key → ℝ) : Integer.Sparse.eval row13407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13407, Integer.Sparse.eval_collectBalanced, rawRowCheck13407]

theorem rawRowCheck13408 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13408 := by decide +kernel

theorem rowCheck13408 : row13408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13408 := by decide +kernel

theorem rowEval13408 (x : Key → ℝ) : Integer.Sparse.eval row13408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13408, Integer.Sparse.eval_collectBalanced, rawRowCheck13408]

theorem rawRowCheck13409 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13409 := by decide +kernel

theorem rowCheck13409 : row13409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13409 := by decide +kernel

theorem rowEval13409 (x : Key → ℝ) : Integer.Sparse.eval row13409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13409, Integer.Sparse.eval_collectBalanced, rawRowCheck13409]

theorem rawRowCheck13410 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13410 := by decide +kernel

theorem rowCheck13410 : row13410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13410 := by decide +kernel

theorem rowEval13410 (x : Key → ℝ) : Integer.Sparse.eval row13410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13410, Integer.Sparse.eval_collectBalanced, rawRowCheck13410]

theorem rawRowCheck13411 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13411 := by decide +kernel

theorem rowCheck13411 : row13411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13411 := by decide +kernel

theorem rowEval13411 (x : Key → ℝ) : Integer.Sparse.eval row13411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13411, Integer.Sparse.eval_collectBalanced, rawRowCheck13411]

theorem rawRowCheck13412 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13412 := by decide +kernel

theorem rowCheck13412 : row13412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13412 := by decide +kernel

theorem rowEval13412 (x : Key → ℝ) : Integer.Sparse.eval row13412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13412, Integer.Sparse.eval_collectBalanced, rawRowCheck13412]

theorem rawRowCheck13413 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13413 := by decide +kernel

theorem rowCheck13413 : row13413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13413 := by decide +kernel

theorem rowEval13413 (x : Key → ℝ) : Integer.Sparse.eval row13413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13413, Integer.Sparse.eval_collectBalanced, rawRowCheck13413]

theorem rawRowCheck13414 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13414 := by decide +kernel

theorem rowCheck13414 : row13414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13414 := by decide +kernel

theorem rowEval13414 (x : Key → ℝ) : Integer.Sparse.eval row13414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13414, Integer.Sparse.eval_collectBalanced, rawRowCheck13414]

theorem rawRowCheck13415 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13415 := by decide +kernel

theorem rowCheck13415 : row13415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13415 := by decide +kernel

theorem rowEval13415 (x : Key → ℝ) : Integer.Sparse.eval row13415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13415, Integer.Sparse.eval_collectBalanced, rawRowCheck13415]

theorem rawRowCheck13416 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13416 := by decide +kernel

theorem rowCheck13416 : row13416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13416 := by decide +kernel

theorem rowEval13416 (x : Key → ℝ) : Integer.Sparse.eval row13416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13416, Integer.Sparse.eval_collectBalanced, rawRowCheck13416]

theorem rawRowCheck13417 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13417 := by decide +kernel

theorem rowCheck13417 : row13417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13417 := by decide +kernel

theorem rowEval13417 (x : Key → ℝ) : Integer.Sparse.eval row13417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13417, Integer.Sparse.eval_collectBalanced, rawRowCheck13417]

theorem rawRowCheck13418 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13418 := by decide +kernel

theorem rowCheck13418 : row13418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13418 := by decide +kernel

theorem rowEval13418 (x : Key → ℝ) : Integer.Sparse.eval row13418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13418, Integer.Sparse.eval_collectBalanced, rawRowCheck13418]

theorem rawRowCheck13419 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13419 := by decide +kernel

theorem rowCheck13419 : row13419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13419 := by decide +kernel

theorem rowEval13419 (x : Key → ℝ) : Integer.Sparse.eval row13419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13419, Integer.Sparse.eval_collectBalanced, rawRowCheck13419]

theorem rawRowCheck13420 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13420 := by decide +kernel

theorem rowCheck13420 : row13420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13420 := by decide +kernel

theorem rowEval13420 (x : Key → ℝ) : Integer.Sparse.eval row13420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13420, Integer.Sparse.eval_collectBalanced, rawRowCheck13420]

theorem rawRowCheck13421 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13421 := by decide +kernel

theorem rowCheck13421 : row13421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13421 := by decide +kernel

theorem rowEval13421 (x : Key → ℝ) : Integer.Sparse.eval row13421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13421, Integer.Sparse.eval_collectBalanced, rawRowCheck13421]

theorem rawRowCheck13422 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13422 := by decide +kernel

theorem rowCheck13422 : row13422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13422 := by decide +kernel

theorem rowEval13422 (x : Key → ℝ) : Integer.Sparse.eval row13422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13422, Integer.Sparse.eval_collectBalanced, rawRowCheck13422]

theorem rawRowCheck13423 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13423 := by decide +kernel

theorem rowCheck13423 : row13423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13423 := by decide +kernel

theorem rowEval13423 (x : Key → ℝ) : Integer.Sparse.eval row13423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13423, Integer.Sparse.eval_collectBalanced, rawRowCheck13423]

theorem rawRowCheck13424 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13424 := by decide +kernel

theorem rowCheck13424 : row13424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13424 := by decide +kernel

theorem rowEval13424 (x : Key → ℝ) : Integer.Sparse.eval row13424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13424, Integer.Sparse.eval_collectBalanced, rawRowCheck13424]

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

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block4.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form3.terms k).tag (GramFunctions.Block4.form3.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13325 x
  · exact rowEval13326 x
  · exact rowEval13327 x
  · exact rowEval13328 x
  · exact rowEval13329 x
  · exact rowEval13330 x
  · exact rowEval13331 x
  · exact rowEval13332 x
  · exact rowEval13333 x
  · exact rowEval13334 x
  · exact rowEval13335 x
  · exact rowEval13336 x
  · exact rowEval13337 x
  · exact rowEval13338 x
  · exact rowEval13339 x
  · exact rowEval13340 x
  · exact rowEval13341 x
  · exact rowEval13342 x
  · exact rowEval13343 x
  · exact rowEval13344 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block4.form3.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form3 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

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

theorem rawRowCheck13503 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form1 = rawRow13503 := by decide +kernel

theorem rowCheck13503 : row13503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13503 := by decide +kernel

theorem rowEval13503 (x : Key → ℝ) : Integer.Sparse.eval row13503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13503, Integer.Sparse.eval_collectBalanced, rawRowCheck13503]

theorem rawRowCheck13504 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form1 = rawRow13504 := by decide +kernel

theorem rowCheck13504 : row13504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13504 := by decide +kernel

theorem rowEval13504 (x : Key → ℝ) : Integer.Sparse.eval row13504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13504, Integer.Sparse.eval_collectBalanced, rawRowCheck13504]

theorem rawRowCheck13505 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form1 = rawRow13505 := by decide +kernel

theorem rowCheck13505 : row13505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13505 := by decide +kernel

theorem rowEval13505 (x : Key → ℝ) : Integer.Sparse.eval row13505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13505, Integer.Sparse.eval_collectBalanced, rawRowCheck13505]

theorem rawRowCheck13506 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13506 := by decide +kernel

theorem rowCheck13506 : row13506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13506 := by decide +kernel

theorem rowEval13506 (x : Key → ℝ) : Integer.Sparse.eval row13506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13506, Integer.Sparse.eval_collectBalanced, rawRowCheck13506]

theorem rawRowCheck13507 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13507 := by decide +kernel

theorem rowCheck13507 : row13507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13507 := by decide +kernel

theorem rowEval13507 (x : Key → ℝ) : Integer.Sparse.eval row13507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13507, Integer.Sparse.eval_collectBalanced, rawRowCheck13507]

theorem rawRowCheck13508 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13508 := by decide +kernel

theorem rowCheck13508 : row13508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13508 := by decide +kernel

theorem rowEval13508 (x : Key → ℝ) : Integer.Sparse.eval row13508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13508, Integer.Sparse.eval_collectBalanced, rawRowCheck13508]

theorem rawRowCheck13509 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13509 := by decide +kernel

theorem rowCheck13509 : row13509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13509 := by decide +kernel

theorem rowEval13509 (x : Key → ℝ) : Integer.Sparse.eval row13509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13509, Integer.Sparse.eval_collectBalanced, rawRowCheck13509]

theorem rawRowCheck13510 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13510 := by decide +kernel

theorem rowCheck13510 : row13510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13510 := by decide +kernel

theorem rowEval13510 (x : Key → ℝ) : Integer.Sparse.eval row13510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13510, Integer.Sparse.eval_collectBalanced, rawRowCheck13510]

theorem rawRowCheck13511 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13511 := by decide +kernel

theorem rowCheck13511 : row13511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13511 := by decide +kernel

theorem rowEval13511 (x : Key → ℝ) : Integer.Sparse.eval row13511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13511, Integer.Sparse.eval_collectBalanced, rawRowCheck13511]

theorem rawRowCheck13512 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13512 := by decide +kernel

theorem rowCheck13512 : row13512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13512 := by decide +kernel

theorem rowEval13512 (x : Key → ℝ) : Integer.Sparse.eval row13512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13512, Integer.Sparse.eval_collectBalanced, rawRowCheck13512]

theorem rawRowCheck13513 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13513 := by decide +kernel

theorem rowCheck13513 : row13513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13513 := by decide +kernel

theorem rowEval13513 (x : Key → ℝ) : Integer.Sparse.eval row13513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13513, Integer.Sparse.eval_collectBalanced, rawRowCheck13513]

theorem rawRowCheck13514 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13514 := by decide +kernel

theorem rowCheck13514 : row13514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13514 := by decide +kernel

theorem rowEval13514 (x : Key → ℝ) : Integer.Sparse.eval row13514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13514, Integer.Sparse.eval_collectBalanced, rawRowCheck13514]

theorem rawRowCheck13515 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13515 := by decide +kernel

theorem rowCheck13515 : row13515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13515 := by decide +kernel

theorem rowEval13515 (x : Key → ℝ) : Integer.Sparse.eval row13515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13515, Integer.Sparse.eval_collectBalanced, rawRowCheck13515]

theorem rawRowCheck13516 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13516 := by decide +kernel

theorem rowCheck13516 : row13516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13516 := by decide +kernel

theorem rowEval13516 (x : Key → ℝ) : Integer.Sparse.eval row13516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13516, Integer.Sparse.eval_collectBalanced, rawRowCheck13516]

theorem rawRowCheck13517 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13517 := by decide +kernel

theorem rowCheck13517 : row13517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13517 := by decide +kernel

theorem rowEval13517 (x : Key → ℝ) : Integer.Sparse.eval row13517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13517, Integer.Sparse.eval_collectBalanced, rawRowCheck13517]

theorem rawRowCheck13518 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13518 := by decide +kernel

theorem rowCheck13518 : row13518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13518 := by decide +kernel

theorem rowEval13518 (x : Key → ℝ) : Integer.Sparse.eval row13518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13518, Integer.Sparse.eval_collectBalanced, rawRowCheck13518]

theorem rawRowCheck13519 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13519 := by decide +kernel

theorem rowCheck13519 : row13519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13519 := by decide +kernel

theorem rowEval13519 (x : Key → ℝ) : Integer.Sparse.eval row13519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13519, Integer.Sparse.eval_collectBalanced, rawRowCheck13519]

theorem rawRowCheck13520 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13520 := by decide +kernel

theorem rowCheck13520 : row13520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13520 := by decide +kernel

theorem rowEval13520 (x : Key → ℝ) : Integer.Sparse.eval row13520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13520, Integer.Sparse.eval_collectBalanced, rawRowCheck13520]

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

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13405 x
  · exact rowEval13406 x
  · exact rowEval13407 x
  · exact rowEval13408 x
  · exact rowEval13409 x
  · exact rowEval13410 x
  · exact rowEval13411 x
  · exact rowEval13412 x
  · exact rowEval13413 x
  · exact rowEval13414 x
  · exact rowEval13415 x
  · exact rowEval13416 x
  · exact rowEval13417 x
  · exact rowEval13418 x
  · exact rowEval13419 x
  · exact rowEval13420 x
  · exact rowEval13421 x
  · exact rowEval13422 x
  · exact rowEval13423 x
  · exact rowEval13424 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

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

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13503 x
  · exact rowEval13504 x
  · exact rowEval13505 x
  · exact rowEval13506 x
  · exact rowEval13507 x
  · exact rowEval13508 x
  · exact rowEval13509 x
  · exact rowEval13510 x
  · exact rowEval13511 x
  · exact rowEval13512 x
  · exact rowEval13513 x
  · exact rowEval13514 x
  · exact rowEval13515 x
  · exact rowEval13516 x
  · exact rowEval13517 x
  · exact rowEval13518 x
  · exact rowEval13519 x
  · exact rowEval13520 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

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

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13855 x
  · exact rowEval13856 x
  · exact rowEval13857 x
  · exact rowEval13858 x
  · exact rowEval13859 x
  · exact rowEval13860 x
  · exact rowEval13861 x
  · exact rowEval13862 x
  · exact rowEval13863 x
  · exact rowEval13864 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

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

theorem entryCheck9_1 : entry9_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_1 k)) := by decide +kernel

theorem rowsSound9_1 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval14115 x
  · exact rowEval14116 x
  · exact rowEval14117 x
  · exact rowEval14118 x
  · exact rowEval14119 x
  · exact rowEval14120 x
  · exact rowEval14121 x
  · exact rowEval14122 x
  · exact rowEval14123 x
  · exact rowEval14124 x

theorem entryEval9_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_1 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck9_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_1]

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

theorem entryEvalRow1_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 1).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval1_0 B hB
  · exact entryEval1_1 B hB
  · exact (entryEval2_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e_oai
