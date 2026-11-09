-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T18:07:16.585202+00:00
-- url     : https://prove2.me/submissions/74dfffe1-50f0-40e2-bbc6-e966df504e00

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval10_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval6_3_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14135 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form3 = rawRow14135 := by decide +kernel

theorem rowCheck14135 : row14135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14135 := by decide +kernel

theorem rowEval14135 (x : Key → ℝ) : Integer.Sparse.eval row14135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14135, Integer.Sparse.eval_collectBalanced, rawRowCheck14135]

theorem rawRowCheck14136 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form3 = rawRow14136 := by decide +kernel

theorem rowCheck14136 : row14136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14136 := by decide +kernel

theorem rowEval14136 (x : Key → ℝ) : Integer.Sparse.eval row14136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14136, Integer.Sparse.eval_collectBalanced, rawRowCheck14136]

theorem rawRowCheck14137 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form3 = rawRow14137 := by decide +kernel

theorem rowCheck14137 : row14137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14137 := by decide +kernel

theorem rowEval14137 (x : Key → ℝ) : Integer.Sparse.eval row14137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14137, Integer.Sparse.eval_collectBalanced, rawRowCheck14137]

theorem rawRowCheck14138 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form3 = rawRow14138 := by decide +kernel

theorem rowCheck14138 : row14138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14138 := by decide +kernel

theorem rowEval14138 (x : Key → ℝ) : Integer.Sparse.eval row14138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14138, Integer.Sparse.eval_collectBalanced, rawRowCheck14138]

theorem rawRowCheck14139 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form3 = rawRow14139 := by decide +kernel

theorem rowCheck14139 : row14139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14139 := by decide +kernel

theorem rowEval14139 (x : Key → ℝ) : Integer.Sparse.eval row14139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14139, Integer.Sparse.eval_collectBalanced, rawRowCheck14139]

theorem rawRowCheck14140 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form3 = rawRow14140 := by decide +kernel

theorem rowCheck14140 : row14140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14140 := by decide +kernel

theorem rowEval14140 (x : Key → ℝ) : Integer.Sparse.eval row14140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14140, Integer.Sparse.eval_collectBalanced, rawRowCheck14140]

theorem rawRowCheck14141 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow14141 := by decide +kernel

theorem rowCheck14141 : row14141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14141 := by decide +kernel

theorem rowEval14141 (x : Key → ℝ) : Integer.Sparse.eval row14141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14141, Integer.Sparse.eval_collectBalanced, rawRowCheck14141]

theorem rawRowCheck14142 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow14142 := by decide +kernel

theorem rowCheck14142 : row14142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14142 := by decide +kernel

theorem rowEval14142 (x : Key → ℝ) : Integer.Sparse.eval row14142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14142, Integer.Sparse.eval_collectBalanced, rawRowCheck14142]

theorem rawRowCheck14143 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow14143 := by decide +kernel

theorem rowCheck14143 : row14143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14143 := by decide +kernel

theorem rowEval14143 (x : Key → ℝ) : Integer.Sparse.eval row14143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14143, Integer.Sparse.eval_collectBalanced, rawRowCheck14143]

theorem rawRowCheck14144 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow14144 := by decide +kernel

theorem rowCheck14144 : row14144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14144 := by decide +kernel

theorem rowEval14144 (x : Key → ℝ) : Integer.Sparse.eval row14144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck14144, Integer.Sparse.eval_collectBalanced, rawRowCheck14144]

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

theorem rawRowCheck14661 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form3 = rawRow14661 := by decide +kernel

theorem rowCheck14661 : row14661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14661 := by decide +kernel

theorem rowEval14661 (x : Key → ℝ) : Integer.Sparse.eval row14661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14661, Integer.Sparse.eval_collectBalanced, rawRowCheck14661]

theorem rawRowCheck14662 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form3 = rawRow14662 := by decide +kernel

theorem rowCheck14662 : row14662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14662 := by decide +kernel

theorem rowEval14662 (x : Key → ℝ) : Integer.Sparse.eval row14662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14662, Integer.Sparse.eval_collectBalanced, rawRowCheck14662]

theorem rawRowCheck14663 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form3 = rawRow14663 := by decide +kernel

theorem rowCheck14663 : row14663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14663 := by decide +kernel

theorem rowEval14663 (x : Key → ℝ) : Integer.Sparse.eval row14663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14663, Integer.Sparse.eval_collectBalanced, rawRowCheck14663]

theorem rawRowCheck14664 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form3 = rawRow14664 := by decide +kernel

theorem rowCheck14664 : row14664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14664 := by decide +kernel

theorem rowEval14664 (x : Key → ℝ) : Integer.Sparse.eval row14664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14664, Integer.Sparse.eval_collectBalanced, rawRowCheck14664]

theorem rawRowCheck14665 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form3 = rawRow14665 := by decide +kernel

theorem rowCheck14665 : row14665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14665 := by decide +kernel

theorem rowEval14665 (x : Key → ℝ) : Integer.Sparse.eval row14665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14665, Integer.Sparse.eval_collectBalanced, rawRowCheck14665]

theorem rawRowCheck14666 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form3 = rawRow14666 := by decide +kernel

theorem rowCheck14666 : row14666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14666 := by decide +kernel

theorem rowEval14666 (x : Key → ℝ) : Integer.Sparse.eval row14666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14666, Integer.Sparse.eval_collectBalanced, rawRowCheck14666]

theorem rawRowCheck14667 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form3 = rawRow14667 := by decide +kernel

theorem rowCheck14667 : row14667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14667 := by decide +kernel

theorem rowEval14667 (x : Key → ℝ) : Integer.Sparse.eval row14667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14667, Integer.Sparse.eval_collectBalanced, rawRowCheck14667]

theorem rawRowCheck14668 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form3 = rawRow14668 := by decide +kernel

theorem rowCheck14668 : row14668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14668 := by decide +kernel

theorem rowEval14668 (x : Key → ℝ) : Integer.Sparse.eval row14668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14668, Integer.Sparse.eval_collectBalanced, rawRowCheck14668]

theorem rawRowCheck14669 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form3 = rawRow14669 := by decide +kernel

theorem rowCheck14669 : row14669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14669 := by decide +kernel

theorem rowEval14669 (x : Key → ℝ) : Integer.Sparse.eval row14669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14669, Integer.Sparse.eval_collectBalanced, rawRowCheck14669]

theorem rawRowCheck14670 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form3 = rawRow14670 := by decide +kernel

theorem rowCheck14670 : row14670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14670 := by decide +kernel

theorem rowEval14670 (x : Key → ℝ) : Integer.Sparse.eval row14670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14670, Integer.Sparse.eval_collectBalanced, rawRowCheck14670]

theorem rawRowCheck14671 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form3 = rawRow14671 := by decide +kernel

theorem rowCheck14671 : row14671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14671 := by decide +kernel

theorem rowEval14671 (x : Key → ℝ) : Integer.Sparse.eval row14671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14671, Integer.Sparse.eval_collectBalanced, rawRowCheck14671]

theorem rawRowCheck14672 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form3 = rawRow14672 := by decide +kernel

theorem rowCheck14672 : row14672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14672 := by decide +kernel

theorem rowEval14672 (x : Key → ℝ) : Integer.Sparse.eval row14672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14672, Integer.Sparse.eval_collectBalanced, rawRowCheck14672]

theorem rawRowCheck14673 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form3 = rawRow14673 := by decide +kernel

theorem rowCheck14673 : row14673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14673 := by decide +kernel

theorem rowEval14673 (x : Key → ℝ) : Integer.Sparse.eval row14673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14673, Integer.Sparse.eval_collectBalanced, rawRowCheck14673]

theorem rawRowCheck14674 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form3 = rawRow14674 := by decide +kernel

theorem rowCheck14674 : row14674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14674 := by decide +kernel

theorem rowEval14674 (x : Key → ℝ) : Integer.Sparse.eval row14674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14674, Integer.Sparse.eval_collectBalanced, rawRowCheck14674]

theorem rawRowCheck14675 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form3 = rawRow14675 := by decide +kernel

theorem rowCheck14675 : row14675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14675 := by decide +kernel

theorem rowEval14675 (x : Key → ℝ) : Integer.Sparse.eval row14675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14675, Integer.Sparse.eval_collectBalanced, rawRowCheck14675]

theorem rawRowCheck14676 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form3 = rawRow14676 := by decide +kernel

theorem rowCheck14676 : row14676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14676 := by decide +kernel

theorem rowEval14676 (x : Key → ℝ) : Integer.Sparse.eval row14676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14676, Integer.Sparse.eval_collectBalanced, rawRowCheck14676]

theorem rawRowCheck14677 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form3 = rawRow14677 := by decide +kernel

theorem rowCheck14677 : row14677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14677 := by decide +kernel

theorem rowEval14677 (x : Key → ℝ) : Integer.Sparse.eval row14677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14677, Integer.Sparse.eval_collectBalanced, rawRowCheck14677]

theorem rawRowCheck14678 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form3 = rawRow14678 := by decide +kernel

theorem rowCheck14678 : row14678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14678 := by decide +kernel

theorem rowEval14678 (x : Key → ℝ) : Integer.Sparse.eval row14678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14678, Integer.Sparse.eval_collectBalanced, rawRowCheck14678]

theorem rawRowCheck14679 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form3 = rawRow14679 := by decide +kernel

theorem rowCheck14679 : row14679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14679 := by decide +kernel

theorem rowEval14679 (x : Key → ℝ) : Integer.Sparse.eval row14679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14679, Integer.Sparse.eval_collectBalanced, rawRowCheck14679]

theorem rawRowCheck14680 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form3 = rawRow14680 := by decide +kernel

theorem rowCheck14680 : row14680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14680 := by decide +kernel

theorem rowEval14680 (x : Key → ℝ) : Integer.Sparse.eval row14680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck14680, Integer.Sparse.eval_collectBalanced, rawRowCheck14680]

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

theorem entryCheck11_3 : entry11_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_3 k)) := by decide +kernel

theorem rowsSound11_3 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval14661 x
  · exact rowEval14662 x
  · exact rowEval14663 x
  · exact rowEval14664 x
  · exact rowEval14665 x
  · exact rowEval14666 x
  · exact rowEval14667 x
  · exact rowEval14668 x
  · exact rowEval14669 x
  · exact rowEval14670 x
  · exact rowEval14671 x
  · exact rowEval14672 x
  · exact rowEval14673 x
  · exact rowEval14674 x
  · exact rowEval14675 x
  · exact rowEval14676 x
  · exact rowEval14677 x
  · exact rowEval14678 x
  · exact rowEval14679 x
  · exact rowEval14680 x

theorem entryEval11_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_3 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck11_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_3]

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

theorem rawRowCheck13875 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form3 = rawRow13875 := by decide +kernel

theorem rowCheck13875 : row13875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13875 := by decide +kernel

theorem rowEval13875 (x : Key → ℝ) : Integer.Sparse.eval row13875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13875, Integer.Sparse.eval_collectBalanced, rawRowCheck13875]

theorem rawRowCheck13876 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form3 = rawRow13876 := by decide +kernel

theorem rowCheck13876 : row13876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13876 := by decide +kernel

theorem rowEval13876 (x : Key → ℝ) : Integer.Sparse.eval row13876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13876, Integer.Sparse.eval_collectBalanced, rawRowCheck13876]

theorem rawRowCheck13877 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form3 = rawRow13877 := by decide +kernel

theorem rowCheck13877 : row13877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13877 := by decide +kernel

theorem rowEval13877 (x : Key → ℝ) : Integer.Sparse.eval row13877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13877, Integer.Sparse.eval_collectBalanced, rawRowCheck13877]

theorem rawRowCheck13878 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form3 = rawRow13878 := by decide +kernel

theorem rowCheck13878 : row13878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13878 := by decide +kernel

theorem rowEval13878 (x : Key → ℝ) : Integer.Sparse.eval row13878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13878, Integer.Sparse.eval_collectBalanced, rawRowCheck13878]

theorem rawRowCheck13879 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form3 = rawRow13879 := by decide +kernel

theorem rowCheck13879 : row13879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13879 := by decide +kernel

theorem rowEval13879 (x : Key → ℝ) : Integer.Sparse.eval row13879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13879, Integer.Sparse.eval_collectBalanced, rawRowCheck13879]

theorem rawRowCheck13880 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form3 = rawRow13880 := by decide +kernel

theorem rowCheck13880 : row13880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13880 := by decide +kernel

theorem rowEval13880 (x : Key → ℝ) : Integer.Sparse.eval row13880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13880, Integer.Sparse.eval_collectBalanced, rawRowCheck13880]

theorem rawRowCheck13881 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow13881 := by decide +kernel

theorem rowCheck13881 : row13881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13881 := by decide +kernel

theorem rowEval13881 (x : Key → ℝ) : Integer.Sparse.eval row13881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13881, Integer.Sparse.eval_collectBalanced, rawRowCheck13881]

theorem rawRowCheck13882 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow13882 := by decide +kernel

theorem rowCheck13882 : row13882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13882 := by decide +kernel

theorem rowEval13882 (x : Key → ℝ) : Integer.Sparse.eval row13882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13882, Integer.Sparse.eval_collectBalanced, rawRowCheck13882]

theorem rawRowCheck13883 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow13883 := by decide +kernel

theorem rowCheck13883 : row13883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13883 := by decide +kernel

theorem rowEval13883 (x : Key → ℝ) : Integer.Sparse.eval row13883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13883, Integer.Sparse.eval_collectBalanced, rawRowCheck13883]

theorem rawRowCheck13884 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow13884 := by decide +kernel

theorem rowCheck13884 : row13884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13884 := by decide +kernel

theorem rowEval13884 (x : Key → ℝ) : Integer.Sparse.eval row13884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13884, Integer.Sparse.eval_collectBalanced, rawRowCheck13884]

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

theorem rawRowCheck17441 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form3 = rawRow17441 := by decide +kernel

theorem rowCheck17441 : row17441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17441 := by decide +kernel

theorem rowEval17441 (x : Key → ℝ) : Integer.Sparse.eval row17441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17441, Integer.Sparse.eval_collectBalanced, rawRowCheck17441]

theorem rawRowCheck17442 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form3 = rawRow17442 := by decide +kernel

theorem rowCheck17442 : row17442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17442 := by decide +kernel

theorem rowEval17442 (x : Key → ℝ) : Integer.Sparse.eval row17442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17442, Integer.Sparse.eval_collectBalanced, rawRowCheck17442]

theorem rawRowCheck17443 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form3 = rawRow17443 := by decide +kernel

theorem rowCheck17443 : row17443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17443 := by decide +kernel

theorem rowEval17443 (x : Key → ℝ) : Integer.Sparse.eval row17443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17443, Integer.Sparse.eval_collectBalanced, rawRowCheck17443]

theorem rawRowCheck17444 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form3 = rawRow17444 := by decide +kernel

theorem rowCheck17444 : row17444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17444 := by decide +kernel

theorem rowEval17444 (x : Key → ℝ) : Integer.Sparse.eval row17444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17444, Integer.Sparse.eval_collectBalanced, rawRowCheck17444]

theorem rawRowCheck17445 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form3 = rawRow17445 := by decide +kernel

theorem rowCheck17445 : row17445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17445 := by decide +kernel

theorem rowEval17445 (x : Key → ℝ) : Integer.Sparse.eval row17445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17445, Integer.Sparse.eval_collectBalanced, rawRowCheck17445]

theorem rawRowCheck17446 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form3 = rawRow17446 := by decide +kernel

theorem rowCheck17446 : row17446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17446 := by decide +kernel

theorem rowEval17446 (x : Key → ℝ) : Integer.Sparse.eval row17446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17446, Integer.Sparse.eval_collectBalanced, rawRowCheck17446]

theorem rawRowCheck17447 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form3 = rawRow17447 := by decide +kernel

theorem rowCheck17447 : row17447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17447 := by decide +kernel

theorem rowEval17447 (x : Key → ℝ) : Integer.Sparse.eval row17447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17447, Integer.Sparse.eval_collectBalanced, rawRowCheck17447]

theorem rawRowCheck17448 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form3 = rawRow17448 := by decide +kernel

theorem rowCheck17448 : row17448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17448 := by decide +kernel

theorem rowEval17448 (x : Key → ℝ) : Integer.Sparse.eval row17448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17448, Integer.Sparse.eval_collectBalanced, rawRowCheck17448]

theorem rawRowCheck17449 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form3 = rawRow17449 := by decide +kernel

theorem rowCheck17449 : row17449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17449 := by decide +kernel

theorem rowEval17449 (x : Key → ℝ) : Integer.Sparse.eval row17449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17449, Integer.Sparse.eval_collectBalanced, rawRowCheck17449]

theorem rawRowCheck17450 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow17450 := by decide +kernel

theorem rowCheck17450 : row17450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17450 := by decide +kernel

theorem rowEval17450 (x : Key → ℝ) : Integer.Sparse.eval row17450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17450, Integer.Sparse.eval_collectBalanced, rawRowCheck17450]

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

end MUB6.Certificate.GramEntries.Block4

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

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval17441 x
  · exact rowEval17442 x
  · exact rowEval17443 x
  · exact rowEval17444 x
  · exact rowEval17445 x
  · exact rowEval17446 x
  · exact rowEval17447 x
  · exact rowEval17448 x
  · exact rowEval17449 x
  · exact rowEval17450 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

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

theorem rawRowCheck18049 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form3 = rawRow18049 := by decide +kernel

theorem rowCheck18049 : row18049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18049 := by decide +kernel

theorem rowEval18049 (x : Key → ℝ) : Integer.Sparse.eval row18049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18049, Integer.Sparse.eval_collectBalanced, rawRowCheck18049]

theorem rawRowCheck18050 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form3 = rawRow18050 := by decide +kernel

theorem rowCheck18050 : row18050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18050 := by decide +kernel

theorem rowEval18050 (x : Key → ℝ) : Integer.Sparse.eval row18050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18050, Integer.Sparse.eval_collectBalanced, rawRowCheck18050]

theorem rawRowCheck18051 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form3 = rawRow18051 := by decide +kernel

theorem rowCheck18051 : row18051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18051 := by decide +kernel

theorem rowEval18051 (x : Key → ℝ) : Integer.Sparse.eval row18051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18051, Integer.Sparse.eval_collectBalanced, rawRowCheck18051]

theorem rawRowCheck18052 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form3 = rawRow18052 := by decide +kernel

theorem rowCheck18052 : row18052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18052 := by decide +kernel

theorem rowEval18052 (x : Key → ℝ) : Integer.Sparse.eval row18052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18052, Integer.Sparse.eval_collectBalanced, rawRowCheck18052]

theorem rawRowCheck18053 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form3 = rawRow18053 := by decide +kernel

theorem rowCheck18053 : row18053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18053 := by decide +kernel

theorem rowEval18053 (x : Key → ℝ) : Integer.Sparse.eval row18053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18053, Integer.Sparse.eval_collectBalanced, rawRowCheck18053]

theorem rawRowCheck18054 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form3 = rawRow18054 := by decide +kernel

theorem rowCheck18054 : row18054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18054 := by decide +kernel

theorem rowEval18054 (x : Key → ℝ) : Integer.Sparse.eval row18054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18054, Integer.Sparse.eval_collectBalanced, rawRowCheck18054]

theorem rawRowCheck18055 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form3 = rawRow18055 := by decide +kernel

theorem rowCheck18055 : row18055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18055 := by decide +kernel

theorem rowEval18055 (x : Key → ℝ) : Integer.Sparse.eval row18055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18055, Integer.Sparse.eval_collectBalanced, rawRowCheck18055]

theorem rawRowCheck18056 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form3 = rawRow18056 := by decide +kernel

theorem rowCheck18056 : row18056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18056 := by decide +kernel

theorem rowEval18056 (x : Key → ℝ) : Integer.Sparse.eval row18056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18056, Integer.Sparse.eval_collectBalanced, rawRowCheck18056]

theorem rawRowCheck18057 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form3 = rawRow18057 := by decide +kernel

theorem rowCheck18057 : row18057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18057 := by decide +kernel

theorem rowEval18057 (x : Key → ℝ) : Integer.Sparse.eval row18057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18057, Integer.Sparse.eval_collectBalanced, rawRowCheck18057]

theorem rawRowCheck18058 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow18058 := by decide +kernel

theorem rowCheck18058 : row18058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18058 := by decide +kernel

theorem rowEval18058 (x : Key → ℝ) : Integer.Sparse.eval row18058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18058, Integer.Sparse.eval_collectBalanced, rawRowCheck18058]

theorem rawRowCheck18059 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow18059 := by decide +kernel

theorem rowCheck18059 : row18059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18059 := by decide +kernel

theorem rowEval18059 (x : Key → ℝ) : Integer.Sparse.eval row18059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18059, Integer.Sparse.eval_collectBalanced, rawRowCheck18059]

theorem rawRowCheck18060 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow18060 := by decide +kernel

theorem rowCheck18060 : row18060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18060 := by decide +kernel

theorem rowEval18060 (x : Key → ℝ) : Integer.Sparse.eval row18060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18060, Integer.Sparse.eval_collectBalanced, rawRowCheck18060]

theorem rawRowCheck18061 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form3 = rawRow18061 := by decide +kernel

theorem rowCheck18061 : row18061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18061 := by decide +kernel

theorem rowEval18061 (x : Key → ℝ) : Integer.Sparse.eval row18061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18061, Integer.Sparse.eval_collectBalanced, rawRowCheck18061]

theorem rawRowCheck18062 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form3 = rawRow18062 := by decide +kernel

theorem rowCheck18062 : row18062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18062 := by decide +kernel

theorem rowEval18062 (x : Key → ℝ) : Integer.Sparse.eval row18062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18062, Integer.Sparse.eval_collectBalanced, rawRowCheck18062]

theorem rawRowCheck18063 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form3 = rawRow18063 := by decide +kernel

theorem rowCheck18063 : row18063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18063 := by decide +kernel

theorem rowEval18063 (x : Key → ℝ) : Integer.Sparse.eval row18063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18063, Integer.Sparse.eval_collectBalanced, rawRowCheck18063]

theorem rawRowCheck18064 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form3 = rawRow18064 := by decide +kernel

theorem rowCheck18064 : row18064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18064 := by decide +kernel

theorem rowEval18064 (x : Key → ℝ) : Integer.Sparse.eval row18064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18064, Integer.Sparse.eval_collectBalanced, rawRowCheck18064]

theorem rawRowCheck18065 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow18065 := by decide +kernel

theorem rowCheck18065 : row18065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18065 := by decide +kernel

theorem rowEval18065 (x : Key → ℝ) : Integer.Sparse.eval row18065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18065, Integer.Sparse.eval_collectBalanced, rawRowCheck18065]

theorem rawRowCheck18066 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow18066 := by decide +kernel

theorem rowCheck18066 : row18066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18066 := by decide +kernel

theorem rowEval18066 (x : Key → ℝ) : Integer.Sparse.eval row18066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18066, Integer.Sparse.eval_collectBalanced, rawRowCheck18066]

theorem rawRowCheck18067 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow18067 := by decide +kernel

theorem rowCheck18067 : row18067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18067 := by decide +kernel

theorem rowEval18067 (x : Key → ℝ) : Integer.Sparse.eval row18067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18067, Integer.Sparse.eval_collectBalanced, rawRowCheck18067]

theorem rawRowCheck18068 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow18068 := by decide +kernel

theorem rowCheck18068 : row18068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18068 := by decide +kernel

theorem rowEval18068 (x : Key → ℝ) : Integer.Sparse.eval row18068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18068, Integer.Sparse.eval_collectBalanced, rawRowCheck18068]

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

theorem entryCheck21_3 : entry21_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_3 k)) := by decide +kernel

theorem rowsSound21_3 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval18049 x
  · exact rowEval18050 x
  · exact rowEval18051 x
  · exact rowEval18052 x
  · exact rowEval18053 x
  · exact rowEval18054 x
  · exact rowEval18055 x
  · exact rowEval18056 x
  · exact rowEval18057 x
  · exact rowEval18058 x
  · exact rowEval18059 x
  · exact rowEval18060 x
  · exact rowEval18061 x
  · exact rowEval18062 x
  · exact rowEval18063 x
  · exact rowEval18064 x
  · exact rowEval18065 x
  · exact rowEval18066 x
  · exact rowEval18067 x
  · exact rowEval18068 x

theorem entryEval21_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_3 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck21_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_3]

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

theorem rawRowCheck13345 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13345 := by decide +kernel

theorem rowCheck13345 : row13345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13345 := by decide +kernel

theorem rowEval13345 (x : Key → ℝ) : Integer.Sparse.eval row13345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13345, Integer.Sparse.eval_collectBalanced, rawRowCheck13345]

theorem rawRowCheck13346 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form2 = rawRow13346 := by decide +kernel

theorem rowCheck13346 : row13346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13346 := by decide +kernel

theorem rowEval13346 (x : Key → ℝ) : Integer.Sparse.eval row13346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13346, Integer.Sparse.eval_collectBalanced, rawRowCheck13346]

theorem rawRowCheck13347 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form2 = rawRow13347 := by decide +kernel

theorem rowCheck13347 : row13347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13347 := by decide +kernel

theorem rowEval13347 (x : Key → ℝ) : Integer.Sparse.eval row13347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13347, Integer.Sparse.eval_collectBalanced, rawRowCheck13347]

theorem rawRowCheck13348 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form2 = rawRow13348 := by decide +kernel

theorem rowCheck13348 : row13348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13348 := by decide +kernel

theorem rowEval13348 (x : Key → ℝ) : Integer.Sparse.eval row13348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13348, Integer.Sparse.eval_collectBalanced, rawRowCheck13348]

theorem rawRowCheck13349 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13349 := by decide +kernel

theorem rowCheck13349 : row13349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13349 := by decide +kernel

theorem rowEval13349 (x : Key → ℝ) : Integer.Sparse.eval row13349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13349, Integer.Sparse.eval_collectBalanced, rawRowCheck13349]

theorem rawRowCheck13350 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form2 = rawRow13350 := by decide +kernel

theorem rowCheck13350 : row13350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13350 := by decide +kernel

theorem rowEval13350 (x : Key → ℝ) : Integer.Sparse.eval row13350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13350, Integer.Sparse.eval_collectBalanced, rawRowCheck13350]

theorem rawRowCheck13351 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form2 = rawRow13351 := by decide +kernel

theorem rowCheck13351 : row13351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13351 := by decide +kernel

theorem rowEval13351 (x : Key → ℝ) : Integer.Sparse.eval row13351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13351, Integer.Sparse.eval_collectBalanced, rawRowCheck13351]

theorem rawRowCheck13352 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form2 = rawRow13352 := by decide +kernel

theorem rowCheck13352 : row13352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13352 := by decide +kernel

theorem rowEval13352 (x : Key → ℝ) : Integer.Sparse.eval row13352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13352, Integer.Sparse.eval_collectBalanced, rawRowCheck13352]

theorem rawRowCheck13353 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form2 = rawRow13353 := by decide +kernel

theorem rowCheck13353 : row13353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13353 := by decide +kernel

theorem rowEval13353 (x : Key → ℝ) : Integer.Sparse.eval row13353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13353, Integer.Sparse.eval_collectBalanced, rawRowCheck13353]

theorem rawRowCheck13354 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form2 = rawRow13354 := by decide +kernel

theorem rowCheck13354 : row13354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13354 := by decide +kernel

theorem rowEval13354 (x : Key → ℝ) : Integer.Sparse.eval row13354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13354, Integer.Sparse.eval_collectBalanced, rawRowCheck13354]

theorem rawRowCheck13355 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form2 = rawRow13355 := by decide +kernel

theorem rowCheck13355 : row13355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13355 := by decide +kernel

theorem rowEval13355 (x : Key → ℝ) : Integer.Sparse.eval row13355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13355, Integer.Sparse.eval_collectBalanced, rawRowCheck13355]

theorem rawRowCheck13356 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form2 = rawRow13356 := by decide +kernel

theorem rowCheck13356 : row13356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13356 := by decide +kernel

theorem rowEval13356 (x : Key → ℝ) : Integer.Sparse.eval row13356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13356, Integer.Sparse.eval_collectBalanced, rawRowCheck13356]

theorem rawRowCheck13357 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form2 = rawRow13357 := by decide +kernel

theorem rowCheck13357 : row13357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13357 := by decide +kernel

theorem rowEval13357 (x : Key → ℝ) : Integer.Sparse.eval row13357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13357, Integer.Sparse.eval_collectBalanced, rawRowCheck13357]

theorem rawRowCheck13358 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form2 = rawRow13358 := by decide +kernel

theorem rowCheck13358 : row13358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13358 := by decide +kernel

theorem rowEval13358 (x : Key → ℝ) : Integer.Sparse.eval row13358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13358, Integer.Sparse.eval_collectBalanced, rawRowCheck13358]

theorem rawRowCheck13359 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form2 = rawRow13359 := by decide +kernel

theorem rowCheck13359 : row13359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13359 := by decide +kernel

theorem rowEval13359 (x : Key → ℝ) : Integer.Sparse.eval row13359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13359, Integer.Sparse.eval_collectBalanced, rawRowCheck13359]

theorem rawRowCheck13360 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form2 = rawRow13360 := by decide +kernel

theorem rowCheck13360 : row13360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13360 := by decide +kernel

theorem rowEval13360 (x : Key → ℝ) : Integer.Sparse.eval row13360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13360, Integer.Sparse.eval_collectBalanced, rawRowCheck13360]

theorem rawRowCheck13361 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form2 = rawRow13361 := by decide +kernel

theorem rowCheck13361 : row13361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13361 := by decide +kernel

theorem rowEval13361 (x : Key → ℝ) : Integer.Sparse.eval row13361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13361, Integer.Sparse.eval_collectBalanced, rawRowCheck13361]

theorem rawRowCheck13362 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form2 = rawRow13362 := by decide +kernel

theorem rowCheck13362 : row13362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13362 := by decide +kernel

theorem rowEval13362 (x : Key → ℝ) : Integer.Sparse.eval row13362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13362, Integer.Sparse.eval_collectBalanced, rawRowCheck13362]

theorem rawRowCheck13363 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form2 = rawRow13363 := by decide +kernel

theorem rowCheck13363 : row13363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13363 := by decide +kernel

theorem rowEval13363 (x : Key → ℝ) : Integer.Sparse.eval row13363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13363, Integer.Sparse.eval_collectBalanced, rawRowCheck13363]

theorem rawRowCheck13364 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form2 = rawRow13364 := by decide +kernel

theorem rowCheck13364 : row13364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13364 := by decide +kernel

theorem rowEval13364 (x : Key → ℝ) : Integer.Sparse.eval row13364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13364, Integer.Sparse.eval_collectBalanced, rawRowCheck13364]

theorem rawRowCheck13365 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13365 := by decide +kernel

theorem rowCheck13365 : row13365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13365 := by decide +kernel

theorem rowEval13365 (x : Key → ℝ) : Integer.Sparse.eval row13365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13365, Integer.Sparse.eval_collectBalanced, rawRowCheck13365]

theorem rawRowCheck13366 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form3 = rawRow13366 := by decide +kernel

theorem rowCheck13366 : row13366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13366 := by decide +kernel

theorem rowEval13366 (x : Key → ℝ) : Integer.Sparse.eval row13366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13366, Integer.Sparse.eval_collectBalanced, rawRowCheck13366]

theorem rawRowCheck13367 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form3 = rawRow13367 := by decide +kernel

theorem rowCheck13367 : row13367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13367 := by decide +kernel

theorem rowEval13367 (x : Key → ℝ) : Integer.Sparse.eval row13367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13367, Integer.Sparse.eval_collectBalanced, rawRowCheck13367]

theorem rawRowCheck13368 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form3 = rawRow13368 := by decide +kernel

theorem rowCheck13368 : row13368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13368 := by decide +kernel

theorem rowEval13368 (x : Key → ℝ) : Integer.Sparse.eval row13368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13368, Integer.Sparse.eval_collectBalanced, rawRowCheck13368]

theorem rawRowCheck13369 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13369 := by decide +kernel

theorem rowCheck13369 : row13369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13369 := by decide +kernel

theorem rowEval13369 (x : Key → ℝ) : Integer.Sparse.eval row13369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13369, Integer.Sparse.eval_collectBalanced, rawRowCheck13369]

theorem rawRowCheck13370 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form3 = rawRow13370 := by decide +kernel

theorem rowCheck13370 : row13370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13370 := by decide +kernel

theorem rowEval13370 (x : Key → ℝ) : Integer.Sparse.eval row13370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13370, Integer.Sparse.eval_collectBalanced, rawRowCheck13370]

theorem rawRowCheck13371 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form3 = rawRow13371 := by decide +kernel

theorem rowCheck13371 : row13371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13371 := by decide +kernel

theorem rowEval13371 (x : Key → ℝ) : Integer.Sparse.eval row13371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13371, Integer.Sparse.eval_collectBalanced, rawRowCheck13371]

theorem rawRowCheck13372 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form3 = rawRow13372 := by decide +kernel

theorem rowCheck13372 : row13372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13372 := by decide +kernel

theorem rowEval13372 (x : Key → ℝ) : Integer.Sparse.eval row13372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13372, Integer.Sparse.eval_collectBalanced, rawRowCheck13372]

theorem rawRowCheck13373 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form3 = rawRow13373 := by decide +kernel

theorem rowCheck13373 : row13373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13373 := by decide +kernel

theorem rowEval13373 (x : Key → ℝ) : Integer.Sparse.eval row13373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13373, Integer.Sparse.eval_collectBalanced, rawRowCheck13373]

theorem rawRowCheck13374 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form3 = rawRow13374 := by decide +kernel

theorem rowCheck13374 : row13374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13374 := by decide +kernel

theorem rowEval13374 (x : Key → ℝ) : Integer.Sparse.eval row13374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13374, Integer.Sparse.eval_collectBalanced, rawRowCheck13374]

theorem rawRowCheck13375 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form3 = rawRow13375 := by decide +kernel

theorem rowCheck13375 : row13375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13375 := by decide +kernel

theorem rowEval13375 (x : Key → ℝ) : Integer.Sparse.eval row13375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13375, Integer.Sparse.eval_collectBalanced, rawRowCheck13375]

theorem rawRowCheck13376 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form3 = rawRow13376 := by decide +kernel

theorem rowCheck13376 : row13376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13376 := by decide +kernel

theorem rowEval13376 (x : Key → ℝ) : Integer.Sparse.eval row13376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13376, Integer.Sparse.eval_collectBalanced, rawRowCheck13376]

theorem rawRowCheck13377 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form3 = rawRow13377 := by decide +kernel

theorem rowCheck13377 : row13377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13377 := by decide +kernel

theorem rowEval13377 (x : Key → ℝ) : Integer.Sparse.eval row13377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13377, Integer.Sparse.eval_collectBalanced, rawRowCheck13377]

theorem rawRowCheck13378 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form3 = rawRow13378 := by decide +kernel

theorem rowCheck13378 : row13378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13378 := by decide +kernel

theorem rowEval13378 (x : Key → ℝ) : Integer.Sparse.eval row13378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13378, Integer.Sparse.eval_collectBalanced, rawRowCheck13378]

theorem rawRowCheck13379 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form3 = rawRow13379 := by decide +kernel

theorem rowCheck13379 : row13379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13379 := by decide +kernel

theorem rowEval13379 (x : Key → ℝ) : Integer.Sparse.eval row13379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13379, Integer.Sparse.eval_collectBalanced, rawRowCheck13379]

theorem rawRowCheck13380 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form3 = rawRow13380 := by decide +kernel

theorem rowCheck13380 : row13380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13380 := by decide +kernel

theorem rowEval13380 (x : Key → ℝ) : Integer.Sparse.eval row13380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13380, Integer.Sparse.eval_collectBalanced, rawRowCheck13380]

theorem rawRowCheck13381 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form3 = rawRow13381 := by decide +kernel

theorem rowCheck13381 : row13381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13381 := by decide +kernel

theorem rowEval13381 (x : Key → ℝ) : Integer.Sparse.eval row13381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13381, Integer.Sparse.eval_collectBalanced, rawRowCheck13381]

theorem rawRowCheck13382 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form3 = rawRow13382 := by decide +kernel

theorem rowCheck13382 : row13382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13382 := by decide +kernel

theorem rowEval13382 (x : Key → ℝ) : Integer.Sparse.eval row13382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13382, Integer.Sparse.eval_collectBalanced, rawRowCheck13382]

theorem rawRowCheck13383 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form3 = rawRow13383 := by decide +kernel

theorem rowCheck13383 : row13383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13383 := by decide +kernel

theorem rowEval13383 (x : Key → ℝ) : Integer.Sparse.eval row13383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13383, Integer.Sparse.eval_collectBalanced, rawRowCheck13383]

theorem rawRowCheck13384 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form3 = rawRow13384 := by decide +kernel

theorem rowCheck13384 : row13384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13384 := by decide +kernel

theorem rowEval13384 (x : Key → ℝ) : Integer.Sparse.eval row13384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13384, Integer.Sparse.eval_collectBalanced, rawRowCheck13384]

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

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block4.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form3.terms k).tag (GramFunctions.Block4.form3.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13345 x
  · exact rowEval13346 x
  · exact rowEval13347 x
  · exact rowEval13348 x
  · exact rowEval13349 x
  · exact rowEval13350 x
  · exact rowEval13351 x
  · exact rowEval13352 x
  · exact rowEval13353 x
  · exact rowEval13354 x
  · exact rowEval13355 x
  · exact rowEval13356 x
  · exact rowEval13357 x
  · exact rowEval13358 x
  · exact rowEval13359 x
  · exact rowEval13360 x
  · exact rowEval13361 x
  · exact rowEval13362 x
  · exact rowEval13363 x
  · exact rowEval13364 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block4.form3.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form3 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block4.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form3.terms k).tag (GramFunctions.Block4.form3.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13365 x
  · exact rowEval13366 x
  · exact rowEval13367 x
  · exact rowEval13368 x
  · exact rowEval13369 x
  · exact rowEval13370 x
  · exact rowEval13371 x
  · exact rowEval13372 x
  · exact rowEval13373 x
  · exact rowEval13374 x
  · exact rowEval13375 x
  · exact rowEval13376 x
  · exact rowEval13377 x
  · exact rowEval13378 x
  · exact rowEval13379 x
  · exact rowEval13380 x
  · exact rowEval13381 x
  · exact rowEval13382 x
  · exact rowEval13383 x
  · exact rowEval13384 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block4.form3.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form3 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

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

theorem rawRowCheck13445 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13445 := by decide +kernel

theorem rowCheck13445 : row13445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13445 := by decide +kernel

theorem rowEval13445 (x : Key → ℝ) : Integer.Sparse.eval row13445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13445, Integer.Sparse.eval_collectBalanced, rawRowCheck13445]

theorem rawRowCheck13446 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13446 := by decide +kernel

theorem rowCheck13446 : row13446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13446 := by decide +kernel

theorem rowEval13446 (x : Key → ℝ) : Integer.Sparse.eval row13446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13446, Integer.Sparse.eval_collectBalanced, rawRowCheck13446]

theorem rawRowCheck13447 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13447 := by decide +kernel

theorem rowCheck13447 : row13447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13447 := by decide +kernel

theorem rowEval13447 (x : Key → ℝ) : Integer.Sparse.eval row13447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13447, Integer.Sparse.eval_collectBalanced, rawRowCheck13447]

theorem rawRowCheck13448 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13448 := by decide +kernel

theorem rowCheck13448 : row13448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13448 := by decide +kernel

theorem rowEval13448 (x : Key → ℝ) : Integer.Sparse.eval row13448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13448, Integer.Sparse.eval_collectBalanced, rawRowCheck13448]

theorem rawRowCheck13449 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13449 := by decide +kernel

theorem rowCheck13449 : row13449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13449 := by decide +kernel

theorem rowEval13449 (x : Key → ℝ) : Integer.Sparse.eval row13449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13449, Integer.Sparse.eval_collectBalanced, rawRowCheck13449]

theorem rawRowCheck13450 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13450 := by decide +kernel

theorem rowCheck13450 : row13450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13450 := by decide +kernel

theorem rowEval13450 (x : Key → ℝ) : Integer.Sparse.eval row13450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13450, Integer.Sparse.eval_collectBalanced, rawRowCheck13450]

theorem rawRowCheck13451 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13451 := by decide +kernel

theorem rowCheck13451 : row13451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13451 := by decide +kernel

theorem rowEval13451 (x : Key → ℝ) : Integer.Sparse.eval row13451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13451, Integer.Sparse.eval_collectBalanced, rawRowCheck13451]

theorem rawRowCheck13452 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13452 := by decide +kernel

theorem rowCheck13452 : row13452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13452 := by decide +kernel

theorem rowEval13452 (x : Key → ℝ) : Integer.Sparse.eval row13452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13452, Integer.Sparse.eval_collectBalanced, rawRowCheck13452]

theorem rawRowCheck13453 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13453 := by decide +kernel

theorem rowCheck13453 : row13453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13453 := by decide +kernel

theorem rowEval13453 (x : Key → ℝ) : Integer.Sparse.eval row13453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13453, Integer.Sparse.eval_collectBalanced, rawRowCheck13453]

theorem rawRowCheck13454 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13454 := by decide +kernel

theorem rowCheck13454 : row13454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13454 := by decide +kernel

theorem rowEval13454 (x : Key → ℝ) : Integer.Sparse.eval row13454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13454, Integer.Sparse.eval_collectBalanced, rawRowCheck13454]

theorem rawRowCheck13455 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13455 := by decide +kernel

theorem rowCheck13455 : row13455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13455 := by decide +kernel

theorem rowEval13455 (x : Key → ℝ) : Integer.Sparse.eval row13455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13455, Integer.Sparse.eval_collectBalanced, rawRowCheck13455]

theorem rawRowCheck13456 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13456 := by decide +kernel

theorem rowCheck13456 : row13456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13456 := by decide +kernel

theorem rowEval13456 (x : Key → ℝ) : Integer.Sparse.eval row13456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13456, Integer.Sparse.eval_collectBalanced, rawRowCheck13456]

theorem rawRowCheck13457 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13457 := by decide +kernel

theorem rowCheck13457 : row13457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13457 := by decide +kernel

theorem rowEval13457 (x : Key → ℝ) : Integer.Sparse.eval row13457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13457, Integer.Sparse.eval_collectBalanced, rawRowCheck13457]

theorem rawRowCheck13458 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13458 := by decide +kernel

theorem rowCheck13458 : row13458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13458 := by decide +kernel

theorem rowEval13458 (x : Key → ℝ) : Integer.Sparse.eval row13458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13458, Integer.Sparse.eval_collectBalanced, rawRowCheck13458]

theorem rawRowCheck13459 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13459 := by decide +kernel

theorem rowCheck13459 : row13459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13459 := by decide +kernel

theorem rowEval13459 (x : Key → ℝ) : Integer.Sparse.eval row13459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13459, Integer.Sparse.eval_collectBalanced, rawRowCheck13459]

theorem rawRowCheck13460 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13460 := by decide +kernel

theorem rowCheck13460 : row13460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13460 := by decide +kernel

theorem rowEval13460 (x : Key → ℝ) : Integer.Sparse.eval row13460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13460, Integer.Sparse.eval_collectBalanced, rawRowCheck13460]

theorem rawRowCheck13461 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13461 := by decide +kernel

theorem rowCheck13461 : row13461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13461 := by decide +kernel

theorem rowEval13461 (x : Key → ℝ) : Integer.Sparse.eval row13461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13461, Integer.Sparse.eval_collectBalanced, rawRowCheck13461]

theorem rawRowCheck13462 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13462 := by decide +kernel

theorem rowCheck13462 : row13462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13462 := by decide +kernel

theorem rowEval13462 (x : Key → ℝ) : Integer.Sparse.eval row13462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13462, Integer.Sparse.eval_collectBalanced, rawRowCheck13462]

theorem rawRowCheck13463 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13463 := by decide +kernel

theorem rowCheck13463 : row13463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13463 := by decide +kernel

theorem rowEval13463 (x : Key → ℝ) : Integer.Sparse.eval row13463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13463, Integer.Sparse.eval_collectBalanced, rawRowCheck13463]

theorem rawRowCheck13464 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13464 := by decide +kernel

theorem rowCheck13464 : row13464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13464 := by decide +kernel

theorem rowEval13464 (x : Key → ℝ) : Integer.Sparse.eval row13464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13464, Integer.Sparse.eval_collectBalanced, rawRowCheck13464]

theorem rawRowCheck13539 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form3 = rawRow13539 := by decide +kernel

theorem rowCheck13539 : row13539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13539 := by decide +kernel

theorem rowEval13539 (x : Key → ℝ) : Integer.Sparse.eval row13539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13539, Integer.Sparse.eval_collectBalanced, rawRowCheck13539]

theorem rawRowCheck13540 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form3 = rawRow13540 := by decide +kernel

theorem rowCheck13540 : row13540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13540 := by decide +kernel

theorem rowEval13540 (x : Key → ℝ) : Integer.Sparse.eval row13540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13540, Integer.Sparse.eval_collectBalanced, rawRowCheck13540]

theorem rawRowCheck13541 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form3 = rawRow13541 := by decide +kernel

theorem rowCheck13541 : row13541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13541 := by decide +kernel

theorem rowEval13541 (x : Key → ℝ) : Integer.Sparse.eval row13541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13541, Integer.Sparse.eval_collectBalanced, rawRowCheck13541]

theorem rawRowCheck13542 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13542 := by decide +kernel

theorem rowCheck13542 : row13542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13542 := by decide +kernel

theorem rowEval13542 (x : Key → ℝ) : Integer.Sparse.eval row13542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13542, Integer.Sparse.eval_collectBalanced, rawRowCheck13542]

theorem rawRowCheck13543 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13543 := by decide +kernel

theorem rowCheck13543 : row13543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13543 := by decide +kernel

theorem rowEval13543 (x : Key → ℝ) : Integer.Sparse.eval row13543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13543, Integer.Sparse.eval_collectBalanced, rawRowCheck13543]

theorem rawRowCheck13544 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13544 := by decide +kernel

theorem rowCheck13544 : row13544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13544 := by decide +kernel

theorem rowEval13544 (x : Key → ℝ) : Integer.Sparse.eval row13544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13544, Integer.Sparse.eval_collectBalanced, rawRowCheck13544]

theorem rawRowCheck13545 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13545 := by decide +kernel

theorem rowCheck13545 : row13545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13545 := by decide +kernel

theorem rowEval13545 (x : Key → ℝ) : Integer.Sparse.eval row13545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13545, Integer.Sparse.eval_collectBalanced, rawRowCheck13545]

theorem rawRowCheck13546 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13546 := by decide +kernel

theorem rowCheck13546 : row13546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13546 := by decide +kernel

theorem rowEval13546 (x : Key → ℝ) : Integer.Sparse.eval row13546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13546, Integer.Sparse.eval_collectBalanced, rawRowCheck13546]

theorem rawRowCheck13547 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13547 := by decide +kernel

theorem rowCheck13547 : row13547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13547 := by decide +kernel

theorem rowEval13547 (x : Key → ℝ) : Integer.Sparse.eval row13547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13547, Integer.Sparse.eval_collectBalanced, rawRowCheck13547]

theorem rawRowCheck13548 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13548 := by decide +kernel

theorem rowCheck13548 : row13548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13548 := by decide +kernel

theorem rowEval13548 (x : Key → ℝ) : Integer.Sparse.eval row13548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13548, Integer.Sparse.eval_collectBalanced, rawRowCheck13548]

theorem rawRowCheck13549 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13549 := by decide +kernel

theorem rowCheck13549 : row13549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13549 := by decide +kernel

theorem rowEval13549 (x : Key → ℝ) : Integer.Sparse.eval row13549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13549, Integer.Sparse.eval_collectBalanced, rawRowCheck13549]

theorem rawRowCheck13550 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13550 := by decide +kernel

theorem rowCheck13550 : row13550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13550 := by decide +kernel

theorem rowEval13550 (x : Key → ℝ) : Integer.Sparse.eval row13550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13550, Integer.Sparse.eval_collectBalanced, rawRowCheck13550]

theorem rawRowCheck13551 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13551 := by decide +kernel

theorem rowCheck13551 : row13551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13551 := by decide +kernel

theorem rowEval13551 (x : Key → ℝ) : Integer.Sparse.eval row13551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13551, Integer.Sparse.eval_collectBalanced, rawRowCheck13551]

theorem rawRowCheck13552 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13552 := by decide +kernel

theorem rowCheck13552 : row13552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13552 := by decide +kernel

theorem rowEval13552 (x : Key → ℝ) : Integer.Sparse.eval row13552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13552, Integer.Sparse.eval_collectBalanced, rawRowCheck13552]

theorem rawRowCheck13553 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13553 := by decide +kernel

theorem rowCheck13553 : row13553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13553 := by decide +kernel

theorem rowEval13553 (x : Key → ℝ) : Integer.Sparse.eval row13553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13553, Integer.Sparse.eval_collectBalanced, rawRowCheck13553]

theorem rawRowCheck13554 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13554 := by decide +kernel

theorem rowCheck13554 : row13554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13554 := by decide +kernel

theorem rowEval13554 (x : Key → ℝ) : Integer.Sparse.eval row13554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13554, Integer.Sparse.eval_collectBalanced, rawRowCheck13554]

theorem rawRowCheck13555 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13555 := by decide +kernel

theorem rowCheck13555 : row13555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13555 := by decide +kernel

theorem rowEval13555 (x : Key → ℝ) : Integer.Sparse.eval row13555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13555, Integer.Sparse.eval_collectBalanced, rawRowCheck13555]

theorem rawRowCheck13556 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13556 := by decide +kernel

theorem rowCheck13556 : row13556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13556 := by decide +kernel

theorem rowEval13556 (x : Key → ℝ) : Integer.Sparse.eval row13556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13556, Integer.Sparse.eval_collectBalanced, rawRowCheck13556]

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

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13445 x
  · exact rowEval13446 x
  · exact rowEval13447 x
  · exact rowEval13448 x
  · exact rowEval13449 x
  · exact rowEval13450 x
  · exact rowEval13451 x
  · exact rowEval13452 x
  · exact rowEval13453 x
  · exact rowEval13454 x
  · exact rowEval13455 x
  · exact rowEval13456 x
  · exact rowEval13457 x
  · exact rowEval13458 x
  · exact rowEval13459 x
  · exact rowEval13460 x
  · exact rowEval13461 x
  · exact rowEval13462 x
  · exact rowEval13463 x
  · exact rowEval13464 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

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

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13539 x
  · exact rowEval13540 x
  · exact rowEval13541 x
  · exact rowEval13542 x
  · exact rowEval13543 x
  · exact rowEval13544 x
  · exact rowEval13545 x
  · exact rowEval13546 x
  · exact rowEval13547 x
  · exact rowEval13548 x
  · exact rowEval13549 x
  · exact rowEval13550 x
  · exact rowEval13551 x
  · exact rowEval13552 x
  · exact rowEval13553 x
  · exact rowEval13554 x
  · exact rowEval13555 x
  · exact rowEval13556 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

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

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13875 x
  · exact rowEval13876 x
  · exact rowEval13877 x
  · exact rowEval13878 x
  · exact rowEval13879 x
  · exact rowEval13880 x
  · exact rowEval13881 x
  · exact rowEval13882 x
  · exact rowEval13883 x
  · exact rowEval13884 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

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

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval14135 x
  · exact rowEval14136 x
  · exact rowEval14137 x
  · exact rowEval14138 x
  · exact rowEval14139 x
  · exact rowEval14140 x
  · exact rowEval14141 x
  · exact rowEval14142 x
  · exact rowEval14143 x
  · exact rowEval14144 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

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

theorem entryEvalRow3_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 3).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval3_0 B hB
  · exact entryEval3_1 B hB
  · exact entryEval3_2 B hB
  · exact entryEval3_3 B hB
  · exact (entryEval4_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e_oai
