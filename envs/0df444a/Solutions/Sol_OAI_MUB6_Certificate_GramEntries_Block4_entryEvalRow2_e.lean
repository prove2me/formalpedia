-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T18:02:13.998247+00:00
-- url     : https://prove2.me/submissions/93b40cf5-6671-45a2-9480-2706720c130a

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval10_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval6_2_e

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

theorem rawRowCheck13285 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form2 = rawRow13285 := by decide +kernel

theorem rowCheck13285 : row13285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13285 := by decide +kernel

theorem rowEval13285 (x : Key → ℝ) : Integer.Sparse.eval row13285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13285, Integer.Sparse.eval_collectBalanced, rawRowCheck13285]

theorem rawRowCheck13286 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form2 = rawRow13286 := by decide +kernel

theorem rowCheck13286 : row13286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13286 := by decide +kernel

theorem rowEval13286 (x : Key → ℝ) : Integer.Sparse.eval row13286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13286, Integer.Sparse.eval_collectBalanced, rawRowCheck13286]

theorem rawRowCheck13287 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form2 = rawRow13287 := by decide +kernel

theorem rowCheck13287 : row13287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13287 := by decide +kernel

theorem rowEval13287 (x : Key → ℝ) : Integer.Sparse.eval row13287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13287, Integer.Sparse.eval_collectBalanced, rawRowCheck13287]

theorem rawRowCheck13288 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13288 := by decide +kernel

theorem rowCheck13288 : row13288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13288 := by decide +kernel

theorem rowEval13288 (x : Key → ℝ) : Integer.Sparse.eval row13288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13288, Integer.Sparse.eval_collectBalanced, rawRowCheck13288]

theorem rawRowCheck13289 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form2 = rawRow13289 := by decide +kernel

theorem rowCheck13289 : row13289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13289 := by decide +kernel

theorem rowEval13289 (x : Key → ℝ) : Integer.Sparse.eval row13289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13289, Integer.Sparse.eval_collectBalanced, rawRowCheck13289]

theorem rawRowCheck13290 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form2 = rawRow13290 := by decide +kernel

theorem rowCheck13290 : row13290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13290 := by decide +kernel

theorem rowEval13290 (x : Key → ℝ) : Integer.Sparse.eval row13290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13290, Integer.Sparse.eval_collectBalanced, rawRowCheck13290]

theorem rawRowCheck13291 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form2 = rawRow13291 := by decide +kernel

theorem rowCheck13291 : row13291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13291 := by decide +kernel

theorem rowEval13291 (x : Key → ℝ) : Integer.Sparse.eval row13291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13291, Integer.Sparse.eval_collectBalanced, rawRowCheck13291]

theorem rawRowCheck13292 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form2 = rawRow13292 := by decide +kernel

theorem rowCheck13292 : row13292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13292 := by decide +kernel

theorem rowEval13292 (x : Key → ℝ) : Integer.Sparse.eval row13292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13292, Integer.Sparse.eval_collectBalanced, rawRowCheck13292]

theorem rawRowCheck13293 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form2 = rawRow13293 := by decide +kernel

theorem rowCheck13293 : row13293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13293 := by decide +kernel

theorem rowEval13293 (x : Key → ℝ) : Integer.Sparse.eval row13293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13293, Integer.Sparse.eval_collectBalanced, rawRowCheck13293]

theorem rawRowCheck13294 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form2 = rawRow13294 := by decide +kernel

theorem rowCheck13294 : row13294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13294 := by decide +kernel

theorem rowEval13294 (x : Key → ℝ) : Integer.Sparse.eval row13294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13294, Integer.Sparse.eval_collectBalanced, rawRowCheck13294]

theorem rawRowCheck13295 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form2 = rawRow13295 := by decide +kernel

theorem rowCheck13295 : row13295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13295 := by decide +kernel

theorem rowEval13295 (x : Key → ℝ) : Integer.Sparse.eval row13295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13295, Integer.Sparse.eval_collectBalanced, rawRowCheck13295]

theorem rawRowCheck13296 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form2 = rawRow13296 := by decide +kernel

theorem rowCheck13296 : row13296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13296 := by decide +kernel

theorem rowEval13296 (x : Key → ℝ) : Integer.Sparse.eval row13296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13296, Integer.Sparse.eval_collectBalanced, rawRowCheck13296]

theorem rawRowCheck13297 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form2 = rawRow13297 := by decide +kernel

theorem rowCheck13297 : row13297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13297 := by decide +kernel

theorem rowEval13297 (x : Key → ℝ) : Integer.Sparse.eval row13297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13297, Integer.Sparse.eval_collectBalanced, rawRowCheck13297]

theorem rawRowCheck13298 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13298 := by decide +kernel

theorem rowCheck13298 : row13298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13298 := by decide +kernel

theorem rowEval13298 (x : Key → ℝ) : Integer.Sparse.eval row13298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13298, Integer.Sparse.eval_collectBalanced, rawRowCheck13298]

theorem rawRowCheck13299 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13299 := by decide +kernel

theorem rowCheck13299 : row13299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13299 := by decide +kernel

theorem rowEval13299 (x : Key → ℝ) : Integer.Sparse.eval row13299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13299, Integer.Sparse.eval_collectBalanced, rawRowCheck13299]

theorem rawRowCheck13300 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13300 := by decide +kernel

theorem rowCheck13300 : row13300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13300 := by decide +kernel

theorem rowEval13300 (x : Key → ℝ) : Integer.Sparse.eval row13300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13300, Integer.Sparse.eval_collectBalanced, rawRowCheck13300]

theorem rawRowCheck13301 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13301 := by decide +kernel

theorem rowCheck13301 : row13301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13301 := by decide +kernel

theorem rowEval13301 (x : Key → ℝ) : Integer.Sparse.eval row13301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13301, Integer.Sparse.eval_collectBalanced, rawRowCheck13301]

theorem rawRowCheck13302 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13302 := by decide +kernel

theorem rowCheck13302 : row13302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13302 := by decide +kernel

theorem rowEval13302 (x : Key → ℝ) : Integer.Sparse.eval row13302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13302, Integer.Sparse.eval_collectBalanced, rawRowCheck13302]

theorem rawRowCheck13303 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13303 := by decide +kernel

theorem rowCheck13303 : row13303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13303 := by decide +kernel

theorem rowEval13303 (x : Key → ℝ) : Integer.Sparse.eval row13303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13303, Integer.Sparse.eval_collectBalanced, rawRowCheck13303]

theorem rawRowCheck13304 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13304 := by decide +kernel

theorem rowCheck13304 : row13304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13304 := by decide +kernel

theorem rowEval13304 (x : Key → ℝ) : Integer.Sparse.eval row13304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13304, Integer.Sparse.eval_collectBalanced, rawRowCheck13304]

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

theorem rawRowCheck14125 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form2 = rawRow14125 := by decide +kernel

theorem rowCheck14125 : row14125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14125 := by decide +kernel

theorem rowEval14125 (x : Key → ℝ) : Integer.Sparse.eval row14125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14125, Integer.Sparse.eval_collectBalanced, rawRowCheck14125]

theorem rawRowCheck14126 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form2 = rawRow14126 := by decide +kernel

theorem rowCheck14126 : row14126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14126 := by decide +kernel

theorem rowEval14126 (x : Key → ℝ) : Integer.Sparse.eval row14126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14126, Integer.Sparse.eval_collectBalanced, rawRowCheck14126]

theorem rawRowCheck14127 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form2 = rawRow14127 := by decide +kernel

theorem rowCheck14127 : row14127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14127 := by decide +kernel

theorem rowEval14127 (x : Key → ℝ) : Integer.Sparse.eval row14127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14127, Integer.Sparse.eval_collectBalanced, rawRowCheck14127]

theorem rawRowCheck14128 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form2 = rawRow14128 := by decide +kernel

theorem rowCheck14128 : row14128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14128 := by decide +kernel

theorem rowEval14128 (x : Key → ℝ) : Integer.Sparse.eval row14128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14128, Integer.Sparse.eval_collectBalanced, rawRowCheck14128]

theorem rawRowCheck14129 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form2 = rawRow14129 := by decide +kernel

theorem rowCheck14129 : row14129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14129 := by decide +kernel

theorem rowEval14129 (x : Key → ℝ) : Integer.Sparse.eval row14129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14129, Integer.Sparse.eval_collectBalanced, rawRowCheck14129]

theorem rawRowCheck14130 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form2 = rawRow14130 := by decide +kernel

theorem rowCheck14130 : row14130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14130 := by decide +kernel

theorem rowEval14130 (x : Key → ℝ) : Integer.Sparse.eval row14130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14130, Integer.Sparse.eval_collectBalanced, rawRowCheck14130]

theorem rawRowCheck14131 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow14131 := by decide +kernel

theorem rowCheck14131 : row14131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14131 := by decide +kernel

theorem rowEval14131 (x : Key → ℝ) : Integer.Sparse.eval row14131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14131, Integer.Sparse.eval_collectBalanced, rawRowCheck14131]

theorem rawRowCheck14132 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow14132 := by decide +kernel

theorem rowCheck14132 : row14132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14132 := by decide +kernel

theorem rowEval14132 (x : Key → ℝ) : Integer.Sparse.eval row14132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14132, Integer.Sparse.eval_collectBalanced, rawRowCheck14132]

theorem rawRowCheck14133 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow14133 := by decide +kernel

theorem rowCheck14133 : row14133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14133 := by decide +kernel

theorem rowEval14133 (x : Key → ℝ) : Integer.Sparse.eval row14133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14133, Integer.Sparse.eval_collectBalanced, rawRowCheck14133]

theorem rawRowCheck14134 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow14134 := by decide +kernel

theorem rowCheck14134 : row14134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14134 := by decide +kernel

theorem rowEval14134 (x : Key → ℝ) : Integer.Sparse.eval row14134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck14134, Integer.Sparse.eval_collectBalanced, rawRowCheck14134]

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

theorem rawRowCheck14641 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form2 = rawRow14641 := by decide +kernel

theorem rowCheck14641 : row14641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14641 := by decide +kernel

theorem rowEval14641 (x : Key → ℝ) : Integer.Sparse.eval row14641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14641, Integer.Sparse.eval_collectBalanced, rawRowCheck14641]

theorem rawRowCheck14642 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form2 = rawRow14642 := by decide +kernel

theorem rowCheck14642 : row14642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14642 := by decide +kernel

theorem rowEval14642 (x : Key → ℝ) : Integer.Sparse.eval row14642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14642, Integer.Sparse.eval_collectBalanced, rawRowCheck14642]

theorem rawRowCheck14643 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form2 = rawRow14643 := by decide +kernel

theorem rowCheck14643 : row14643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14643 := by decide +kernel

theorem rowEval14643 (x : Key → ℝ) : Integer.Sparse.eval row14643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14643, Integer.Sparse.eval_collectBalanced, rawRowCheck14643]

theorem rawRowCheck14644 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form2 = rawRow14644 := by decide +kernel

theorem rowCheck14644 : row14644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14644 := by decide +kernel

theorem rowEval14644 (x : Key → ℝ) : Integer.Sparse.eval row14644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14644, Integer.Sparse.eval_collectBalanced, rawRowCheck14644]

theorem rawRowCheck14645 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form2 = rawRow14645 := by decide +kernel

theorem rowCheck14645 : row14645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14645 := by decide +kernel

theorem rowEval14645 (x : Key → ℝ) : Integer.Sparse.eval row14645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14645, Integer.Sparse.eval_collectBalanced, rawRowCheck14645]

theorem rawRowCheck14646 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form2 = rawRow14646 := by decide +kernel

theorem rowCheck14646 : row14646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14646 := by decide +kernel

theorem rowEval14646 (x : Key → ℝ) : Integer.Sparse.eval row14646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14646, Integer.Sparse.eval_collectBalanced, rawRowCheck14646]

theorem rawRowCheck14647 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form2 = rawRow14647 := by decide +kernel

theorem rowCheck14647 : row14647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14647 := by decide +kernel

theorem rowEval14647 (x : Key → ℝ) : Integer.Sparse.eval row14647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14647, Integer.Sparse.eval_collectBalanced, rawRowCheck14647]

theorem rawRowCheck14648 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form2 = rawRow14648 := by decide +kernel

theorem rowCheck14648 : row14648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14648 := by decide +kernel

theorem rowEval14648 (x : Key → ℝ) : Integer.Sparse.eval row14648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14648, Integer.Sparse.eval_collectBalanced, rawRowCheck14648]

theorem rawRowCheck14649 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form2 = rawRow14649 := by decide +kernel

theorem rowCheck14649 : row14649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14649 := by decide +kernel

theorem rowEval14649 (x : Key → ℝ) : Integer.Sparse.eval row14649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14649, Integer.Sparse.eval_collectBalanced, rawRowCheck14649]

theorem rawRowCheck14650 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form2 = rawRow14650 := by decide +kernel

theorem rowCheck14650 : row14650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14650 := by decide +kernel

theorem rowEval14650 (x : Key → ℝ) : Integer.Sparse.eval row14650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14650, Integer.Sparse.eval_collectBalanced, rawRowCheck14650]

theorem rawRowCheck14651 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form2 = rawRow14651 := by decide +kernel

theorem rowCheck14651 : row14651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14651 := by decide +kernel

theorem rowEval14651 (x : Key → ℝ) : Integer.Sparse.eval row14651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14651, Integer.Sparse.eval_collectBalanced, rawRowCheck14651]

theorem rawRowCheck14652 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form2 = rawRow14652 := by decide +kernel

theorem rowCheck14652 : row14652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14652 := by decide +kernel

theorem rowEval14652 (x : Key → ℝ) : Integer.Sparse.eval row14652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14652, Integer.Sparse.eval_collectBalanced, rawRowCheck14652]

theorem rawRowCheck14653 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form2 = rawRow14653 := by decide +kernel

theorem rowCheck14653 : row14653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14653 := by decide +kernel

theorem rowEval14653 (x : Key → ℝ) : Integer.Sparse.eval row14653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14653, Integer.Sparse.eval_collectBalanced, rawRowCheck14653]

theorem rawRowCheck14654 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form2 = rawRow14654 := by decide +kernel

theorem rowCheck14654 : row14654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14654 := by decide +kernel

theorem rowEval14654 (x : Key → ℝ) : Integer.Sparse.eval row14654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14654, Integer.Sparse.eval_collectBalanced, rawRowCheck14654]

theorem rawRowCheck14655 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form2 = rawRow14655 := by decide +kernel

theorem rowCheck14655 : row14655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14655 := by decide +kernel

theorem rowEval14655 (x : Key → ℝ) : Integer.Sparse.eval row14655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14655, Integer.Sparse.eval_collectBalanced, rawRowCheck14655]

theorem rawRowCheck14656 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form2 = rawRow14656 := by decide +kernel

theorem rowCheck14656 : row14656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14656 := by decide +kernel

theorem rowEval14656 (x : Key → ℝ) : Integer.Sparse.eval row14656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14656, Integer.Sparse.eval_collectBalanced, rawRowCheck14656]

theorem rawRowCheck14657 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form2 = rawRow14657 := by decide +kernel

theorem rowCheck14657 : row14657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14657 := by decide +kernel

theorem rowEval14657 (x : Key → ℝ) : Integer.Sparse.eval row14657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14657, Integer.Sparse.eval_collectBalanced, rawRowCheck14657]

theorem rawRowCheck14658 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form2 = rawRow14658 := by decide +kernel

theorem rowCheck14658 : row14658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14658 := by decide +kernel

theorem rowEval14658 (x : Key → ℝ) : Integer.Sparse.eval row14658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14658, Integer.Sparse.eval_collectBalanced, rawRowCheck14658]

theorem rawRowCheck14659 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form2 = rawRow14659 := by decide +kernel

theorem rowCheck14659 : row14659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14659 := by decide +kernel

theorem rowEval14659 (x : Key → ℝ) : Integer.Sparse.eval row14659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck14659, Integer.Sparse.eval_collectBalanced, rawRowCheck14659]

theorem rawRowCheck14660 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form2 = rawRow14660 := by decide +kernel

theorem rowCheck14660 : row14660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14660 := by decide +kernel

theorem rowEval14660 (x : Key → ℝ) : Integer.Sparse.eval row14660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck14660, Integer.Sparse.eval_collectBalanced, rawRowCheck14660]

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

theorem entryCheck11_2 : entry11_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_2 k)) := by decide +kernel

theorem rowsSound11_2 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval14641 x
  · exact rowEval14642 x
  · exact rowEval14643 x
  · exact rowEval14644 x
  · exact rowEval14645 x
  · exact rowEval14646 x
  · exact rowEval14647 x
  · exact rowEval14648 x
  · exact rowEval14649 x
  · exact rowEval14650 x
  · exact rowEval14651 x
  · exact rowEval14652 x
  · exact rowEval14653 x
  · exact rowEval14654 x
  · exact rowEval14655 x
  · exact rowEval14656 x
  · exact rowEval14657 x
  · exact rowEval14658 x
  · exact rowEval14659 x
  · exact rowEval14660 x

theorem entryEval11_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_2 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck11_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_2]

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

theorem rawRowCheck13865 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form2 = rawRow13865 := by decide +kernel

theorem rowCheck13865 : row13865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13865 := by decide +kernel

theorem rowEval13865 (x : Key → ℝ) : Integer.Sparse.eval row13865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13865, Integer.Sparse.eval_collectBalanced, rawRowCheck13865]

theorem rawRowCheck13866 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form2 = rawRow13866 := by decide +kernel

theorem rowCheck13866 : row13866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13866 := by decide +kernel

theorem rowEval13866 (x : Key → ℝ) : Integer.Sparse.eval row13866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13866, Integer.Sparse.eval_collectBalanced, rawRowCheck13866]

theorem rawRowCheck13867 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form2 = rawRow13867 := by decide +kernel

theorem rowCheck13867 : row13867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13867 := by decide +kernel

theorem rowEval13867 (x : Key → ℝ) : Integer.Sparse.eval row13867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13867, Integer.Sparse.eval_collectBalanced, rawRowCheck13867]

theorem rawRowCheck13868 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form2 = rawRow13868 := by decide +kernel

theorem rowCheck13868 : row13868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13868 := by decide +kernel

theorem rowEval13868 (x : Key → ℝ) : Integer.Sparse.eval row13868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13868, Integer.Sparse.eval_collectBalanced, rawRowCheck13868]

theorem rawRowCheck13869 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form2 = rawRow13869 := by decide +kernel

theorem rowCheck13869 : row13869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13869 := by decide +kernel

theorem rowEval13869 (x : Key → ℝ) : Integer.Sparse.eval row13869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13869, Integer.Sparse.eval_collectBalanced, rawRowCheck13869]

theorem rawRowCheck13870 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form2 = rawRow13870 := by decide +kernel

theorem rowCheck13870 : row13870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13870 := by decide +kernel

theorem rowEval13870 (x : Key → ℝ) : Integer.Sparse.eval row13870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13870, Integer.Sparse.eval_collectBalanced, rawRowCheck13870]

theorem rawRowCheck13871 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow13871 := by decide +kernel

theorem rowCheck13871 : row13871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13871 := by decide +kernel

theorem rowEval13871 (x : Key → ℝ) : Integer.Sparse.eval row13871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13871, Integer.Sparse.eval_collectBalanced, rawRowCheck13871]

theorem rawRowCheck13872 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow13872 := by decide +kernel

theorem rowCheck13872 : row13872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13872 := by decide +kernel

theorem rowEval13872 (x : Key → ℝ) : Integer.Sparse.eval row13872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13872, Integer.Sparse.eval_collectBalanced, rawRowCheck13872]

theorem rawRowCheck13873 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow13873 := by decide +kernel

theorem rowCheck13873 : row13873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13873 := by decide +kernel

theorem rowEval13873 (x : Key → ℝ) : Integer.Sparse.eval row13873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13873, Integer.Sparse.eval_collectBalanced, rawRowCheck13873]

theorem rawRowCheck13874 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow13874 := by decide +kernel

theorem rowCheck13874 : row13874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13874 := by decide +kernel

theorem rowEval13874 (x : Key → ℝ) : Integer.Sparse.eval row13874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13874, Integer.Sparse.eval_collectBalanced, rawRowCheck13874]

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

theorem rawRowCheck17431 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form2 = rawRow17431 := by decide +kernel

theorem rowCheck17431 : row17431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17431 := by decide +kernel

theorem rowEval17431 (x : Key → ℝ) : Integer.Sparse.eval row17431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17431, Integer.Sparse.eval_collectBalanced, rawRowCheck17431]

theorem rawRowCheck17432 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form2 = rawRow17432 := by decide +kernel

theorem rowCheck17432 : row17432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17432 := by decide +kernel

theorem rowEval17432 (x : Key → ℝ) : Integer.Sparse.eval row17432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17432, Integer.Sparse.eval_collectBalanced, rawRowCheck17432]

theorem rawRowCheck17433 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form2 = rawRow17433 := by decide +kernel

theorem rowCheck17433 : row17433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17433 := by decide +kernel

theorem rowEval17433 (x : Key → ℝ) : Integer.Sparse.eval row17433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17433, Integer.Sparse.eval_collectBalanced, rawRowCheck17433]

theorem rawRowCheck17434 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form2 = rawRow17434 := by decide +kernel

theorem rowCheck17434 : row17434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17434 := by decide +kernel

theorem rowEval17434 (x : Key → ℝ) : Integer.Sparse.eval row17434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17434, Integer.Sparse.eval_collectBalanced, rawRowCheck17434]

theorem rawRowCheck17435 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form2 = rawRow17435 := by decide +kernel

theorem rowCheck17435 : row17435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17435 := by decide +kernel

theorem rowEval17435 (x : Key → ℝ) : Integer.Sparse.eval row17435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17435, Integer.Sparse.eval_collectBalanced, rawRowCheck17435]

theorem rawRowCheck17436 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form2 = rawRow17436 := by decide +kernel

theorem rowCheck17436 : row17436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17436 := by decide +kernel

theorem rowEval17436 (x : Key → ℝ) : Integer.Sparse.eval row17436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17436, Integer.Sparse.eval_collectBalanced, rawRowCheck17436]

theorem rawRowCheck17437 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form2 = rawRow17437 := by decide +kernel

theorem rowCheck17437 : row17437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17437 := by decide +kernel

theorem rowEval17437 (x : Key → ℝ) : Integer.Sparse.eval row17437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17437, Integer.Sparse.eval_collectBalanced, rawRowCheck17437]

theorem rawRowCheck17438 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form2 = rawRow17438 := by decide +kernel

theorem rowCheck17438 : row17438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17438 := by decide +kernel

theorem rowEval17438 (x : Key → ℝ) : Integer.Sparse.eval row17438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17438, Integer.Sparse.eval_collectBalanced, rawRowCheck17438]

theorem rawRowCheck17439 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form2 = rawRow17439 := by decide +kernel

theorem rowCheck17439 : row17439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17439 := by decide +kernel

theorem rowEval17439 (x : Key → ℝ) : Integer.Sparse.eval row17439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17439, Integer.Sparse.eval_collectBalanced, rawRowCheck17439]

theorem rawRowCheck17440 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow17440 := by decide +kernel

theorem rowCheck17440 : row17440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17440 := by decide +kernel

theorem rowEval17440 (x : Key → ℝ) : Integer.Sparse.eval row17440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17440, Integer.Sparse.eval_collectBalanced, rawRowCheck17440]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck19_2 : entry19_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_2 k)) := by decide +kernel

theorem rowsSound19_2 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval17431 x
  · exact rowEval17432 x
  · exact rowEval17433 x
  · exact rowEval17434 x
  · exact rowEval17435 x
  · exact rowEval17436 x
  · exact rowEval17437 x
  · exact rowEval17438 x
  · exact rowEval17439 x
  · exact rowEval17440 x

theorem entryEval19_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_2 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck19_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_2]

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

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block4.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form2.terms k).tag (GramFunctions.Block4.form2.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13285 x
  · exact rowEval13286 x
  · exact rowEval13287 x
  · exact rowEval13288 x
  · exact rowEval13289 x
  · exact rowEval13290 x
  · exact rowEval13291 x
  · exact rowEval13292 x
  · exact rowEval13293 x
  · exact rowEval13294 x
  · exact rowEval13295 x
  · exact rowEval13296 x
  · exact rowEval13297 x
  · exact rowEval13298 x
  · exact rowEval13299 x
  · exact rowEval13300 x
  · exact rowEval13301 x
  · exact rowEval13302 x
  · exact rowEval13303 x
  · exact rowEval13304 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block4.form2.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form2 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

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

theorem rawRowCheck17664 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form2 = rawRow17664 := by decide +kernel

theorem rowCheck17664 : row17664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17664 := by decide +kernel

theorem rowEval17664 (x : Key → ℝ) : Integer.Sparse.eval row17664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17664, Integer.Sparse.eval_collectBalanced, rawRowCheck17664]

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

theorem rawRowCheck18029 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form2 = rawRow18029 := by decide +kernel

theorem rowCheck18029 : row18029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18029 := by decide +kernel

theorem rowEval18029 (x : Key → ℝ) : Integer.Sparse.eval row18029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18029, Integer.Sparse.eval_collectBalanced, rawRowCheck18029]

theorem rawRowCheck18030 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form2 = rawRow18030 := by decide +kernel

theorem rowCheck18030 : row18030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18030 := by decide +kernel

theorem rowEval18030 (x : Key → ℝ) : Integer.Sparse.eval row18030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18030, Integer.Sparse.eval_collectBalanced, rawRowCheck18030]

theorem rawRowCheck18031 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form2 = rawRow18031 := by decide +kernel

theorem rowCheck18031 : row18031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18031 := by decide +kernel

theorem rowEval18031 (x : Key → ℝ) : Integer.Sparse.eval row18031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18031, Integer.Sparse.eval_collectBalanced, rawRowCheck18031]

theorem rawRowCheck18032 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form2 = rawRow18032 := by decide +kernel

theorem rowCheck18032 : row18032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18032 := by decide +kernel

theorem rowEval18032 (x : Key → ℝ) : Integer.Sparse.eval row18032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18032, Integer.Sparse.eval_collectBalanced, rawRowCheck18032]

theorem rawRowCheck18033 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form2 = rawRow18033 := by decide +kernel

theorem rowCheck18033 : row18033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18033 := by decide +kernel

theorem rowEval18033 (x : Key → ℝ) : Integer.Sparse.eval row18033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18033, Integer.Sparse.eval_collectBalanced, rawRowCheck18033]

theorem rawRowCheck18034 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form2 = rawRow18034 := by decide +kernel

theorem rowCheck18034 : row18034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18034 := by decide +kernel

theorem rowEval18034 (x : Key → ℝ) : Integer.Sparse.eval row18034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18034, Integer.Sparse.eval_collectBalanced, rawRowCheck18034]

theorem rawRowCheck18035 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form2 = rawRow18035 := by decide +kernel

theorem rowCheck18035 : row18035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18035 := by decide +kernel

theorem rowEval18035 (x : Key → ℝ) : Integer.Sparse.eval row18035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18035, Integer.Sparse.eval_collectBalanced, rawRowCheck18035]

theorem rawRowCheck18036 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form2 = rawRow18036 := by decide +kernel

theorem rowCheck18036 : row18036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18036 := by decide +kernel

theorem rowEval18036 (x : Key → ℝ) : Integer.Sparse.eval row18036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18036, Integer.Sparse.eval_collectBalanced, rawRowCheck18036]

theorem rawRowCheck18037 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form2 = rawRow18037 := by decide +kernel

theorem rowCheck18037 : row18037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18037 := by decide +kernel

theorem rowEval18037 (x : Key → ℝ) : Integer.Sparse.eval row18037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18037, Integer.Sparse.eval_collectBalanced, rawRowCheck18037]

theorem rawRowCheck18038 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow18038 := by decide +kernel

theorem rowCheck18038 : row18038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18038 := by decide +kernel

theorem rowEval18038 (x : Key → ℝ) : Integer.Sparse.eval row18038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18038, Integer.Sparse.eval_collectBalanced, rawRowCheck18038]

theorem rawRowCheck18039 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow18039 := by decide +kernel

theorem rowCheck18039 : row18039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18039 := by decide +kernel

theorem rowEval18039 (x : Key → ℝ) : Integer.Sparse.eval row18039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18039, Integer.Sparse.eval_collectBalanced, rawRowCheck18039]

theorem rawRowCheck18040 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow18040 := by decide +kernel

theorem rowCheck18040 : row18040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18040 := by decide +kernel

theorem rowEval18040 (x : Key → ℝ) : Integer.Sparse.eval row18040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18040, Integer.Sparse.eval_collectBalanced, rawRowCheck18040]

theorem rawRowCheck18041 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form2 = rawRow18041 := by decide +kernel

theorem rowCheck18041 : row18041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18041 := by decide +kernel

theorem rowEval18041 (x : Key → ℝ) : Integer.Sparse.eval row18041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18041, Integer.Sparse.eval_collectBalanced, rawRowCheck18041]

theorem rawRowCheck18042 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form2 = rawRow18042 := by decide +kernel

theorem rowCheck18042 : row18042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18042 := by decide +kernel

theorem rowEval18042 (x : Key → ℝ) : Integer.Sparse.eval row18042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18042, Integer.Sparse.eval_collectBalanced, rawRowCheck18042]

theorem rawRowCheck18043 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form2 = rawRow18043 := by decide +kernel

theorem rowCheck18043 : row18043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18043 := by decide +kernel

theorem rowEval18043 (x : Key → ℝ) : Integer.Sparse.eval row18043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18043, Integer.Sparse.eval_collectBalanced, rawRowCheck18043]

theorem rawRowCheck18044 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form2 = rawRow18044 := by decide +kernel

theorem rowCheck18044 : row18044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18044 := by decide +kernel

theorem rowEval18044 (x : Key → ℝ) : Integer.Sparse.eval row18044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18044, Integer.Sparse.eval_collectBalanced, rawRowCheck18044]

theorem rawRowCheck18045 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow18045 := by decide +kernel

theorem rowCheck18045 : row18045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18045 := by decide +kernel

theorem rowEval18045 (x : Key → ℝ) : Integer.Sparse.eval row18045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18045, Integer.Sparse.eval_collectBalanced, rawRowCheck18045]

theorem rawRowCheck18046 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow18046 := by decide +kernel

theorem rowCheck18046 : row18046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18046 := by decide +kernel

theorem rowEval18046 (x : Key → ℝ) : Integer.Sparse.eval row18046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18046, Integer.Sparse.eval_collectBalanced, rawRowCheck18046]

theorem rawRowCheck18047 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow18047 := by decide +kernel

theorem rowCheck18047 : row18047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18047 := by decide +kernel

theorem rowEval18047 (x : Key → ℝ) : Integer.Sparse.eval row18047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18047, Integer.Sparse.eval_collectBalanced, rawRowCheck18047]

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

theorem rawRowCheck18048 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow18048 := by decide +kernel

theorem rowCheck18048 : row18048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18048 := by decide +kernel

theorem rowEval18048 (x : Key → ℝ) : Integer.Sparse.eval row18048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18048, Integer.Sparse.eval_collectBalanced, rawRowCheck18048]

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

theorem entryCheck21_2 : entry21_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_2 k)) := by decide +kernel

theorem rowsSound21_2 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval18029 x
  · exact rowEval18030 x
  · exact rowEval18031 x
  · exact rowEval18032 x
  · exact rowEval18033 x
  · exact rowEval18034 x
  · exact rowEval18035 x
  · exact rowEval18036 x
  · exact rowEval18037 x
  · exact rowEval18038 x
  · exact rowEval18039 x
  · exact rowEval18040 x
  · exact rowEval18041 x
  · exact rowEval18042 x
  · exact rowEval18043 x
  · exact rowEval18044 x
  · exact rowEval18045 x
  · exact rowEval18046 x
  · exact rowEval18047 x
  · exact rowEval18048 x

theorem entryEval21_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_2 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck21_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_2]

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

theorem rawRowCheck13425 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13425 := by decide +kernel

theorem rowCheck13425 : row13425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13425 := by decide +kernel

theorem rowEval13425 (x : Key → ℝ) : Integer.Sparse.eval row13425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13425, Integer.Sparse.eval_collectBalanced, rawRowCheck13425]

theorem rawRowCheck13426 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13426 := by decide +kernel

theorem rowCheck13426 : row13426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13426 := by decide +kernel

theorem rowEval13426 (x : Key → ℝ) : Integer.Sparse.eval row13426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13426, Integer.Sparse.eval_collectBalanced, rawRowCheck13426]

theorem rawRowCheck13427 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13427 := by decide +kernel

theorem rowCheck13427 : row13427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13427 := by decide +kernel

theorem rowEval13427 (x : Key → ℝ) : Integer.Sparse.eval row13427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13427, Integer.Sparse.eval_collectBalanced, rawRowCheck13427]

theorem rawRowCheck13428 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13428 := by decide +kernel

theorem rowCheck13428 : row13428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13428 := by decide +kernel

theorem rowEval13428 (x : Key → ℝ) : Integer.Sparse.eval row13428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13428, Integer.Sparse.eval_collectBalanced, rawRowCheck13428]

theorem rawRowCheck13429 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13429 := by decide +kernel

theorem rowCheck13429 : row13429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13429 := by decide +kernel

theorem rowEval13429 (x : Key → ℝ) : Integer.Sparse.eval row13429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13429, Integer.Sparse.eval_collectBalanced, rawRowCheck13429]

theorem rawRowCheck13430 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13430 := by decide +kernel

theorem rowCheck13430 : row13430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13430 := by decide +kernel

theorem rowEval13430 (x : Key → ℝ) : Integer.Sparse.eval row13430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13430, Integer.Sparse.eval_collectBalanced, rawRowCheck13430]

theorem rawRowCheck13431 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13431 := by decide +kernel

theorem rowCheck13431 : row13431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13431 := by decide +kernel

theorem rowEval13431 (x : Key → ℝ) : Integer.Sparse.eval row13431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13431, Integer.Sparse.eval_collectBalanced, rawRowCheck13431]

theorem rawRowCheck13432 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13432 := by decide +kernel

theorem rowCheck13432 : row13432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13432 := by decide +kernel

theorem rowEval13432 (x : Key → ℝ) : Integer.Sparse.eval row13432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13432, Integer.Sparse.eval_collectBalanced, rawRowCheck13432]

theorem rawRowCheck13433 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13433 := by decide +kernel

theorem rowCheck13433 : row13433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13433 := by decide +kernel

theorem rowEval13433 (x : Key → ℝ) : Integer.Sparse.eval row13433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13433, Integer.Sparse.eval_collectBalanced, rawRowCheck13433]

theorem rawRowCheck13434 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13434 := by decide +kernel

theorem rowCheck13434 : row13434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13434 := by decide +kernel

theorem rowEval13434 (x : Key → ℝ) : Integer.Sparse.eval row13434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13434, Integer.Sparse.eval_collectBalanced, rawRowCheck13434]

theorem rawRowCheck13435 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13435 := by decide +kernel

theorem rowCheck13435 : row13435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13435 := by decide +kernel

theorem rowEval13435 (x : Key → ℝ) : Integer.Sparse.eval row13435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13435, Integer.Sparse.eval_collectBalanced, rawRowCheck13435]

theorem rawRowCheck13436 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13436 := by decide +kernel

theorem rowCheck13436 : row13436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13436 := by decide +kernel

theorem rowEval13436 (x : Key → ℝ) : Integer.Sparse.eval row13436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13436, Integer.Sparse.eval_collectBalanced, rawRowCheck13436]

theorem rawRowCheck13437 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13437 := by decide +kernel

theorem rowCheck13437 : row13437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13437 := by decide +kernel

theorem rowEval13437 (x : Key → ℝ) : Integer.Sparse.eval row13437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13437, Integer.Sparse.eval_collectBalanced, rawRowCheck13437]

theorem rawRowCheck13438 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13438 := by decide +kernel

theorem rowCheck13438 : row13438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13438 := by decide +kernel

theorem rowEval13438 (x : Key → ℝ) : Integer.Sparse.eval row13438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13438, Integer.Sparse.eval_collectBalanced, rawRowCheck13438]

theorem rawRowCheck13439 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13439 := by decide +kernel

theorem rowCheck13439 : row13439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13439 := by decide +kernel

theorem rowEval13439 (x : Key → ℝ) : Integer.Sparse.eval row13439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13439, Integer.Sparse.eval_collectBalanced, rawRowCheck13439]

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

theorem rawRowCheck13440 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13440 := by decide +kernel

theorem rowCheck13440 : row13440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13440 := by decide +kernel

theorem rowEval13440 (x : Key → ℝ) : Integer.Sparse.eval row13440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13440, Integer.Sparse.eval_collectBalanced, rawRowCheck13440]

theorem rawRowCheck13441 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13441 := by decide +kernel

theorem rowCheck13441 : row13441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13441 := by decide +kernel

theorem rowEval13441 (x : Key → ℝ) : Integer.Sparse.eval row13441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13441, Integer.Sparse.eval_collectBalanced, rawRowCheck13441]

theorem rawRowCheck13442 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13442 := by decide +kernel

theorem rowCheck13442 : row13442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13442 := by decide +kernel

theorem rowEval13442 (x : Key → ℝ) : Integer.Sparse.eval row13442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13442, Integer.Sparse.eval_collectBalanced, rawRowCheck13442]

theorem rawRowCheck13443 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13443 := by decide +kernel

theorem rowCheck13443 : row13443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13443 := by decide +kernel

theorem rowEval13443 (x : Key → ℝ) : Integer.Sparse.eval row13443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13443, Integer.Sparse.eval_collectBalanced, rawRowCheck13443]

theorem rawRowCheck13444 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13444 := by decide +kernel

theorem rowCheck13444 : row13444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13444 := by decide +kernel

theorem rowEval13444 (x : Key → ℝ) : Integer.Sparse.eval row13444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13444, Integer.Sparse.eval_collectBalanced, rawRowCheck13444]

theorem rawRowCheck13521 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form2 = rawRow13521 := by decide +kernel

theorem rowCheck13521 : row13521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13521 := by decide +kernel

theorem rowEval13521 (x : Key → ℝ) : Integer.Sparse.eval row13521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13521, Integer.Sparse.eval_collectBalanced, rawRowCheck13521]

theorem rawRowCheck13522 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form2 = rawRow13522 := by decide +kernel

theorem rowCheck13522 : row13522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13522 := by decide +kernel

theorem rowEval13522 (x : Key → ℝ) : Integer.Sparse.eval row13522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13522, Integer.Sparse.eval_collectBalanced, rawRowCheck13522]

theorem rawRowCheck13523 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form2 = rawRow13523 := by decide +kernel

theorem rowCheck13523 : row13523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13523 := by decide +kernel

theorem rowEval13523 (x : Key → ℝ) : Integer.Sparse.eval row13523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13523, Integer.Sparse.eval_collectBalanced, rawRowCheck13523]

theorem rawRowCheck13524 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13524 := by decide +kernel

theorem rowCheck13524 : row13524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13524 := by decide +kernel

theorem rowEval13524 (x : Key → ℝ) : Integer.Sparse.eval row13524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13524, Integer.Sparse.eval_collectBalanced, rawRowCheck13524]

theorem rawRowCheck13525 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13525 := by decide +kernel

theorem rowCheck13525 : row13525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13525 := by decide +kernel

theorem rowEval13525 (x : Key → ℝ) : Integer.Sparse.eval row13525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13525, Integer.Sparse.eval_collectBalanced, rawRowCheck13525]

theorem rawRowCheck13526 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13526 := by decide +kernel

theorem rowCheck13526 : row13526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13526 := by decide +kernel

theorem rowEval13526 (x : Key → ℝ) : Integer.Sparse.eval row13526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13526, Integer.Sparse.eval_collectBalanced, rawRowCheck13526]

theorem rawRowCheck13527 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13527 := by decide +kernel

theorem rowCheck13527 : row13527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13527 := by decide +kernel

theorem rowEval13527 (x : Key → ℝ) : Integer.Sparse.eval row13527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13527, Integer.Sparse.eval_collectBalanced, rawRowCheck13527]

theorem rawRowCheck13528 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13528 := by decide +kernel

theorem rowCheck13528 : row13528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13528 := by decide +kernel

theorem rowEval13528 (x : Key → ℝ) : Integer.Sparse.eval row13528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13528, Integer.Sparse.eval_collectBalanced, rawRowCheck13528]

theorem rawRowCheck13529 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13529 := by decide +kernel

theorem rowCheck13529 : row13529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13529 := by decide +kernel

theorem rowEval13529 (x : Key → ℝ) : Integer.Sparse.eval row13529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13529, Integer.Sparse.eval_collectBalanced, rawRowCheck13529]

theorem rawRowCheck13530 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13530 := by decide +kernel

theorem rowCheck13530 : row13530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13530 := by decide +kernel

theorem rowEval13530 (x : Key → ℝ) : Integer.Sparse.eval row13530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13530, Integer.Sparse.eval_collectBalanced, rawRowCheck13530]

theorem rawRowCheck13531 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13531 := by decide +kernel

theorem rowCheck13531 : row13531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13531 := by decide +kernel

theorem rowEval13531 (x : Key → ℝ) : Integer.Sparse.eval row13531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13531, Integer.Sparse.eval_collectBalanced, rawRowCheck13531]

theorem rawRowCheck13532 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13532 := by decide +kernel

theorem rowCheck13532 : row13532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13532 := by decide +kernel

theorem rowEval13532 (x : Key → ℝ) : Integer.Sparse.eval row13532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13532, Integer.Sparse.eval_collectBalanced, rawRowCheck13532]

theorem rawRowCheck13533 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13533 := by decide +kernel

theorem rowCheck13533 : row13533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13533 := by decide +kernel

theorem rowEval13533 (x : Key → ℝ) : Integer.Sparse.eval row13533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13533, Integer.Sparse.eval_collectBalanced, rawRowCheck13533]

theorem rawRowCheck13534 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13534 := by decide +kernel

theorem rowCheck13534 : row13534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13534 := by decide +kernel

theorem rowEval13534 (x : Key → ℝ) : Integer.Sparse.eval row13534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13534, Integer.Sparse.eval_collectBalanced, rawRowCheck13534]

theorem rawRowCheck13535 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13535 := by decide +kernel

theorem rowCheck13535 : row13535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13535 := by decide +kernel

theorem rowEval13535 (x : Key → ℝ) : Integer.Sparse.eval row13535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13535, Integer.Sparse.eval_collectBalanced, rawRowCheck13535]

theorem rawRowCheck13536 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13536 := by decide +kernel

theorem rowCheck13536 : row13536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13536 := by decide +kernel

theorem rowEval13536 (x : Key → ℝ) : Integer.Sparse.eval row13536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13536, Integer.Sparse.eval_collectBalanced, rawRowCheck13536]

theorem rawRowCheck13537 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13537 := by decide +kernel

theorem rowCheck13537 : row13537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13537 := by decide +kernel

theorem rowEval13537 (x : Key → ℝ) : Integer.Sparse.eval row13537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13537, Integer.Sparse.eval_collectBalanced, rawRowCheck13537]

theorem rawRowCheck13538 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13538 := by decide +kernel

theorem rowCheck13538 : row13538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13538 := by decide +kernel

theorem rowEval13538 (x : Key → ℝ) : Integer.Sparse.eval row13538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13538, Integer.Sparse.eval_collectBalanced, rawRowCheck13538]

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

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13425 x
  · exact rowEval13426 x
  · exact rowEval13427 x
  · exact rowEval13428 x
  · exact rowEval13429 x
  · exact rowEval13430 x
  · exact rowEval13431 x
  · exact rowEval13432 x
  · exact rowEval13433 x
  · exact rowEval13434 x
  · exact rowEval13435 x
  · exact rowEval13436 x
  · exact rowEval13437 x
  · exact rowEval13438 x
  · exact rowEval13439 x
  · exact rowEval13440 x
  · exact rowEval13441 x
  · exact rowEval13442 x
  · exact rowEval13443 x
  · exact rowEval13444 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

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

theorem entryCheck5_2 : entry5_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_2 k)) := by decide +kernel

theorem rowsSound5_2 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13521 x
  · exact rowEval13522 x
  · exact rowEval13523 x
  · exact rowEval13524 x
  · exact rowEval13525 x
  · exact rowEval13526 x
  · exact rowEval13527 x
  · exact rowEval13528 x
  · exact rowEval13529 x
  · exact rowEval13530 x
  · exact rowEval13531 x
  · exact rowEval13532 x
  · exact rowEval13533 x
  · exact rowEval13534 x
  · exact rowEval13535 x
  · exact rowEval13536 x
  · exact rowEval13537 x
  · exact rowEval13538 x

theorem entryEval5_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_2 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck5_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_2]

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

theorem entryCheck7_2 : entry7_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_2 k)) := by decide +kernel

theorem rowsSound7_2 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13865 x
  · exact rowEval13866 x
  · exact rowEval13867 x
  · exact rowEval13868 x
  · exact rowEval13869 x
  · exact rowEval13870 x
  · exact rowEval13871 x
  · exact rowEval13872 x
  · exact rowEval13873 x
  · exact rowEval13874 x

theorem entryEval7_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_2 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck7_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_2]

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

theorem entryCheck9_2 : entry9_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_2 k)) := by decide +kernel

theorem rowsSound9_2 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval14125 x
  · exact rowEval14126 x
  · exact rowEval14127 x
  · exact rowEval14128 x
  · exact rowEval14129 x
  · exact rowEval14130 x
  · exact rowEval14131 x
  · exact rowEval14132 x
  · exact rowEval14133 x
  · exact rowEval14134 x

theorem entryEval9_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_2 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck9_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_2]

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

theorem entryEvalRow2_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 2 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 2).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval2_0 B hB
  · exact entryEval2_1 B hB
  · exact entryEval2_2 B hB
  · exact (entryEval3_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e_oai
