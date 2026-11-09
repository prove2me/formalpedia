-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:12:17.378884+00:00
-- url     : https://prove2.me/submissions/a739c241-8ed2-4c9b-b3be-d343c7dd07f9

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval10_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_10_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8485 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8485 := by decide +kernel

theorem rowCheck8485 : row8485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8485 := by decide +kernel

theorem rowEval8485 (x : Key → ℝ) : Integer.Sparse.eval row8485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8485, Integer.Sparse.eval_collectBalanced, rawRowCheck8485]

theorem rawRowCheck8486 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow8486 := by decide +kernel

theorem rowCheck8486 : row8486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8486 := by decide +kernel

theorem rowEval8486 (x : Key → ℝ) : Integer.Sparse.eval row8486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8486, Integer.Sparse.eval_collectBalanced, rawRowCheck8486]

theorem rawRowCheck8487 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow8487 := by decide +kernel

theorem rowCheck8487 : row8487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8487 := by decide +kernel

theorem rowEval8487 (x : Key → ℝ) : Integer.Sparse.eval row8487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8487, Integer.Sparse.eval_collectBalanced, rawRowCheck8487]

theorem rawRowCheck8488 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow8488 := by decide +kernel

theorem rowCheck8488 : row8488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8488 := by decide +kernel

theorem rowEval8488 (x : Key → ℝ) : Integer.Sparse.eval row8488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8488, Integer.Sparse.eval_collectBalanced, rawRowCheck8488]

theorem rawRowCheck8489 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow8489 := by decide +kernel

theorem rowCheck8489 : row8489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8489 := by decide +kernel

theorem rowEval8489 (x : Key → ℝ) : Integer.Sparse.eval row8489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8489, Integer.Sparse.eval_collectBalanced, rawRowCheck8489]

theorem rawRowCheck8490 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow8490 := by decide +kernel

theorem rowCheck8490 : row8490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8490 := by decide +kernel

theorem rowEval8490 (x : Key → ℝ) : Integer.Sparse.eval row8490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8490, Integer.Sparse.eval_collectBalanced, rawRowCheck8490]

theorem rawRowCheck8491 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow8491 := by decide +kernel

theorem rowCheck8491 : row8491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8491 := by decide +kernel

theorem rowEval8491 (x : Key → ℝ) : Integer.Sparse.eval row8491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8491, Integer.Sparse.eval_collectBalanced, rawRowCheck8491]

theorem rawRowCheck8492 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow8492 := by decide +kernel

theorem rowCheck8492 : row8492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8492 := by decide +kernel

theorem rowEval8492 (x : Key → ℝ) : Integer.Sparse.eval row8492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8492, Integer.Sparse.eval_collectBalanced, rawRowCheck8492]

theorem rawRowCheck8493 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow8493 := by decide +kernel

theorem rowCheck8493 : row8493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8493 := by decide +kernel

theorem rowEval8493 (x : Key → ℝ) : Integer.Sparse.eval row8493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8493, Integer.Sparse.eval_collectBalanced, rawRowCheck8493]

theorem rawRowCheck8494 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow8494 := by decide +kernel

theorem rowCheck8494 : row8494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8494 := by decide +kernel

theorem rowEval8494 (x : Key → ℝ) : Integer.Sparse.eval row8494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8494, Integer.Sparse.eval_collectBalanced, rawRowCheck8494]

theorem rawRowCheck8495 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0 = rawRow8495 := by decide +kernel

theorem rowCheck8495 : row8495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8495 := by decide +kernel

theorem rowEval8495 (x : Key → ℝ) : Integer.Sparse.eval row8495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8495, Integer.Sparse.eval_collectBalanced, rawRowCheck8495]

theorem rawRowCheck8496 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0 = rawRow8496 := by decide +kernel

theorem rowCheck8496 : row8496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8496 := by decide +kernel

theorem rowEval8496 (x : Key → ℝ) : Integer.Sparse.eval row8496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8496, Integer.Sparse.eval_collectBalanced, rawRowCheck8496]

theorem rawRowCheck8497 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0 = rawRow8497 := by decide +kernel

theorem rowCheck8497 : row8497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8497 := by decide +kernel

theorem rowEval8497 (x : Key → ℝ) : Integer.Sparse.eval row8497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8497, Integer.Sparse.eval_collectBalanced, rawRowCheck8497]

theorem rawRowCheck8498 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0 = rawRow8498 := by decide +kernel

theorem rowCheck8498 : row8498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8498 := by decide +kernel

theorem rowEval8498 (x : Key → ℝ) : Integer.Sparse.eval row8498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8498, Integer.Sparse.eval_collectBalanced, rawRowCheck8498]

theorem rawRowCheck8499 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0 = rawRow8499 := by decide +kernel

theorem rowCheck8499 : row8499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8499 := by decide +kernel

theorem rowEval8499 (x : Key → ℝ) : Integer.Sparse.eval row8499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8499, Integer.Sparse.eval_collectBalanced, rawRowCheck8499]

theorem rawRowCheck8500 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0 = rawRow8500 := by decide +kernel

theorem rowCheck8500 : row8500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8500 := by decide +kernel

theorem rowEval8500 (x : Key → ℝ) : Integer.Sparse.eval row8500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8500, Integer.Sparse.eval_collectBalanced, rawRowCheck8500]

theorem rawRowCheck8501 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8501 := by decide +kernel

theorem rowCheck8501 : row8501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8501 := by decide +kernel

theorem rowEval8501 (x : Key → ℝ) : Integer.Sparse.eval row8501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8501, Integer.Sparse.eval_collectBalanced, rawRowCheck8501]

theorem rawRowCheck8502 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1 = rawRow8502 := by decide +kernel

theorem rowCheck8502 : row8502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8502 := by decide +kernel

theorem rowEval8502 (x : Key → ℝ) : Integer.Sparse.eval row8502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8502, Integer.Sparse.eval_collectBalanced, rawRowCheck8502]

theorem rawRowCheck8503 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1 = rawRow8503 := by decide +kernel

theorem rowCheck8503 : row8503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8503 := by decide +kernel

theorem rowEval8503 (x : Key → ℝ) : Integer.Sparse.eval row8503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8503, Integer.Sparse.eval_collectBalanced, rawRowCheck8503]

theorem rawRowCheck8504 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1 = rawRow8504 := by decide +kernel

theorem rowCheck8504 : row8504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8504 := by decide +kernel

theorem rowEval8504 (x : Key → ℝ) : Integer.Sparse.eval row8504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8504, Integer.Sparse.eval_collectBalanced, rawRowCheck8504]

theorem rawRowCheck8505 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow8505 := by decide +kernel

theorem rowCheck8505 : row8505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8505 := by decide +kernel

theorem rowEval8505 (x : Key → ℝ) : Integer.Sparse.eval row8505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8505, Integer.Sparse.eval_collectBalanced, rawRowCheck8505]

theorem rawRowCheck8506 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow8506 := by decide +kernel

theorem rowCheck8506 : row8506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8506 := by decide +kernel

theorem rowEval8506 (x : Key → ℝ) : Integer.Sparse.eval row8506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8506, Integer.Sparse.eval_collectBalanced, rawRowCheck8506]

theorem rawRowCheck8507 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow8507 := by decide +kernel

theorem rowCheck8507 : row8507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8507 := by decide +kernel

theorem rowEval8507 (x : Key → ℝ) : Integer.Sparse.eval row8507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8507, Integer.Sparse.eval_collectBalanced, rawRowCheck8507]

theorem rawRowCheck8508 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow8508 := by decide +kernel

theorem rowCheck8508 : row8508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8508 := by decide +kernel

theorem rowEval8508 (x : Key → ℝ) : Integer.Sparse.eval row8508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8508, Integer.Sparse.eval_collectBalanced, rawRowCheck8508]

theorem rawRowCheck8509 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow8509 := by decide +kernel

theorem rowCheck8509 : row8509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8509 := by decide +kernel

theorem rowEval8509 (x : Key → ℝ) : Integer.Sparse.eval row8509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8509, Integer.Sparse.eval_collectBalanced, rawRowCheck8509]

theorem rawRowCheck8510 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow8510 := by decide +kernel

theorem rowCheck8510 : row8510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8510 := by decide +kernel

theorem rowEval8510 (x : Key → ℝ) : Integer.Sparse.eval row8510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8510, Integer.Sparse.eval_collectBalanced, rawRowCheck8510]

theorem rawRowCheck8511 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form1 = rawRow8511 := by decide +kernel

theorem rowCheck8511 : row8511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8511 := by decide +kernel

theorem rowEval8511 (x : Key → ℝ) : Integer.Sparse.eval row8511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8511, Integer.Sparse.eval_collectBalanced, rawRowCheck8511]

theorem rawRowCheck8512 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form1 = rawRow8512 := by decide +kernel

theorem rowCheck8512 : row8512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8512 := by decide +kernel

theorem rowEval8512 (x : Key → ℝ) : Integer.Sparse.eval row8512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8512, Integer.Sparse.eval_collectBalanced, rawRowCheck8512]

theorem rawRowCheck8513 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form1 = rawRow8513 := by decide +kernel

theorem rowCheck8513 : row8513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8513 := by decide +kernel

theorem rowEval8513 (x : Key → ℝ) : Integer.Sparse.eval row8513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8513, Integer.Sparse.eval_collectBalanced, rawRowCheck8513]

theorem rawRowCheck8514 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form1 = rawRow8514 := by decide +kernel

theorem rowCheck8514 : row8514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8514 := by decide +kernel

theorem rowEval8514 (x : Key → ℝ) : Integer.Sparse.eval row8514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8514, Integer.Sparse.eval_collectBalanced, rawRowCheck8514]

theorem rawRowCheck8515 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form1 = rawRow8515 := by decide +kernel

theorem rowCheck8515 : row8515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8515 := by decide +kernel

theorem rowEval8515 (x : Key → ℝ) : Integer.Sparse.eval row8515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8515, Integer.Sparse.eval_collectBalanced, rawRowCheck8515]

theorem rawRowCheck8516 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form1 = rawRow8516 := by decide +kernel

theorem rowCheck8516 : row8516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8516 := by decide +kernel

theorem rowEval8516 (x : Key → ℝ) : Integer.Sparse.eval row8516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8516, Integer.Sparse.eval_collectBalanced, rawRowCheck8516]

theorem rawRowCheck8517 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8517 := by decide +kernel

theorem rowCheck8517 : row8517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8517 := by decide +kernel

theorem rowEval8517 (x : Key → ℝ) : Integer.Sparse.eval row8517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8517, Integer.Sparse.eval_collectBalanced, rawRowCheck8517]

theorem rawRowCheck8518 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2 = rawRow8518 := by decide +kernel

theorem rowCheck8518 : row8518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8518 := by decide +kernel

theorem rowEval8518 (x : Key → ℝ) : Integer.Sparse.eval row8518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8518, Integer.Sparse.eval_collectBalanced, rawRowCheck8518]

theorem rawRowCheck8519 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2 = rawRow8519 := by decide +kernel

theorem rowCheck8519 : row8519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8519 := by decide +kernel

theorem rowEval8519 (x : Key → ℝ) : Integer.Sparse.eval row8519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8519, Integer.Sparse.eval_collectBalanced, rawRowCheck8519]

theorem rawRowCheck8520 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2 = rawRow8520 := by decide +kernel

theorem rowCheck8520 : row8520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8520 := by decide +kernel

theorem rowEval8520 (x : Key → ℝ) : Integer.Sparse.eval row8520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8520, Integer.Sparse.eval_collectBalanced, rawRowCheck8520]

theorem rawRowCheck8521 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow8521 := by decide +kernel

theorem rowCheck8521 : row8521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8521 := by decide +kernel

theorem rowEval8521 (x : Key → ℝ) : Integer.Sparse.eval row8521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8521, Integer.Sparse.eval_collectBalanced, rawRowCheck8521]

theorem rawRowCheck8522 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow8522 := by decide +kernel

theorem rowCheck8522 : row8522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8522 := by decide +kernel

theorem rowEval8522 (x : Key → ℝ) : Integer.Sparse.eval row8522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8522, Integer.Sparse.eval_collectBalanced, rawRowCheck8522]

theorem rawRowCheck8523 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow8523 := by decide +kernel

theorem rowCheck8523 : row8523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8523 := by decide +kernel

theorem rowEval8523 (x : Key → ℝ) : Integer.Sparse.eval row8523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8523, Integer.Sparse.eval_collectBalanced, rawRowCheck8523]

theorem rawRowCheck8524 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow8524 := by decide +kernel

theorem rowCheck8524 : row8524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8524 := by decide +kernel

theorem rowEval8524 (x : Key → ℝ) : Integer.Sparse.eval row8524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8524, Integer.Sparse.eval_collectBalanced, rawRowCheck8524]

theorem rawRowCheck8525 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow8525 := by decide +kernel

theorem rowCheck8525 : row8525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8525 := by decide +kernel

theorem rowEval8525 (x : Key → ℝ) : Integer.Sparse.eval row8525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8525, Integer.Sparse.eval_collectBalanced, rawRowCheck8525]

theorem rawRowCheck8526 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow8526 := by decide +kernel

theorem rowCheck8526 : row8526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8526 := by decide +kernel

theorem rowEval8526 (x : Key → ℝ) : Integer.Sparse.eval row8526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8526, Integer.Sparse.eval_collectBalanced, rawRowCheck8526]

theorem rawRowCheck8527 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form2 = rawRow8527 := by decide +kernel

theorem rowCheck8527 : row8527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8527 := by decide +kernel

theorem rowEval8527 (x : Key → ℝ) : Integer.Sparse.eval row8527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8527, Integer.Sparse.eval_collectBalanced, rawRowCheck8527]

theorem rawRowCheck8528 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form2 = rawRow8528 := by decide +kernel

theorem rowCheck8528 : row8528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8528 := by decide +kernel

theorem rowEval8528 (x : Key → ℝ) : Integer.Sparse.eval row8528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8528, Integer.Sparse.eval_collectBalanced, rawRowCheck8528]

theorem rawRowCheck8529 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form2 = rawRow8529 := by decide +kernel

theorem rowCheck8529 : row8529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8529 := by decide +kernel

theorem rowEval8529 (x : Key → ℝ) : Integer.Sparse.eval row8529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8529, Integer.Sparse.eval_collectBalanced, rawRowCheck8529]

theorem rawRowCheck8530 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form2 = rawRow8530 := by decide +kernel

theorem rowCheck8530 : row8530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8530 := by decide +kernel

theorem rowEval8530 (x : Key → ℝ) : Integer.Sparse.eval row8530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8530, Integer.Sparse.eval_collectBalanced, rawRowCheck8530]

theorem rawRowCheck8531 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form2 = rawRow8531 := by decide +kernel

theorem rowCheck8531 : row8531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8531 := by decide +kernel

theorem rowEval8531 (x : Key → ℝ) : Integer.Sparse.eval row8531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8531, Integer.Sparse.eval_collectBalanced, rawRowCheck8531]

theorem rawRowCheck8532 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form2 = rawRow8532 := by decide +kernel

theorem rowCheck8532 : row8532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8532 := by decide +kernel

theorem rowEval8532 (x : Key → ℝ) : Integer.Sparse.eval row8532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8532, Integer.Sparse.eval_collectBalanced, rawRowCheck8532]

theorem rawRowCheck8533 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8533 := by decide +kernel

theorem rowCheck8533 : row8533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8533 := by decide +kernel

theorem rowEval8533 (x : Key → ℝ) : Integer.Sparse.eval row8533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8533, Integer.Sparse.eval_collectBalanced, rawRowCheck8533]

theorem rawRowCheck8534 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3 = rawRow8534 := by decide +kernel

theorem rowCheck8534 : row8534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8534 := by decide +kernel

theorem rowEval8534 (x : Key → ℝ) : Integer.Sparse.eval row8534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8534, Integer.Sparse.eval_collectBalanced, rawRowCheck8534]

theorem rawRowCheck8535 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3 = rawRow8535 := by decide +kernel

theorem rowCheck8535 : row8535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8535 := by decide +kernel

theorem rowEval8535 (x : Key → ℝ) : Integer.Sparse.eval row8535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8535, Integer.Sparse.eval_collectBalanced, rawRowCheck8535]

theorem rawRowCheck8536 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3 = rawRow8536 := by decide +kernel

theorem rowCheck8536 : row8536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8536 := by decide +kernel

theorem rowEval8536 (x : Key → ℝ) : Integer.Sparse.eval row8536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8536, Integer.Sparse.eval_collectBalanced, rawRowCheck8536]

theorem rawRowCheck8537 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow8537 := by decide +kernel

theorem rowCheck8537 : row8537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8537 := by decide +kernel

theorem rowEval8537 (x : Key → ℝ) : Integer.Sparse.eval row8537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8537, Integer.Sparse.eval_collectBalanced, rawRowCheck8537]

theorem rawRowCheck8538 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow8538 := by decide +kernel

theorem rowCheck8538 : row8538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8538 := by decide +kernel

theorem rowEval8538 (x : Key → ℝ) : Integer.Sparse.eval row8538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8538, Integer.Sparse.eval_collectBalanced, rawRowCheck8538]

theorem rawRowCheck8539 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow8539 := by decide +kernel

theorem rowCheck8539 : row8539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8539 := by decide +kernel

theorem rowEval8539 (x : Key → ℝ) : Integer.Sparse.eval row8539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8539, Integer.Sparse.eval_collectBalanced, rawRowCheck8539]

theorem rawRowCheck8540 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow8540 := by decide +kernel

theorem rowCheck8540 : row8540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8540 := by decide +kernel

theorem rowEval8540 (x : Key → ℝ) : Integer.Sparse.eval row8540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8540, Integer.Sparse.eval_collectBalanced, rawRowCheck8540]

theorem rawRowCheck8541 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow8541 := by decide +kernel

theorem rowCheck8541 : row8541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8541 := by decide +kernel

theorem rowEval8541 (x : Key → ℝ) : Integer.Sparse.eval row8541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8541, Integer.Sparse.eval_collectBalanced, rawRowCheck8541]

theorem rawRowCheck8542 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow8542 := by decide +kernel

theorem rowCheck8542 : row8542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8542 := by decide +kernel

theorem rowEval8542 (x : Key → ℝ) : Integer.Sparse.eval row8542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8542, Integer.Sparse.eval_collectBalanced, rawRowCheck8542]

theorem rawRowCheck8543 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form3 = rawRow8543 := by decide +kernel

theorem rowCheck8543 : row8543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8543 := by decide +kernel

theorem rowEval8543 (x : Key → ℝ) : Integer.Sparse.eval row8543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8543, Integer.Sparse.eval_collectBalanced, rawRowCheck8543]

theorem rawRowCheck8544 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form3 = rawRow8544 := by decide +kernel

theorem rowCheck8544 : row8544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8544 := by decide +kernel

theorem rowEval8544 (x : Key → ℝ) : Integer.Sparse.eval row8544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8544, Integer.Sparse.eval_collectBalanced, rawRowCheck8544]

theorem rawRowCheck8545 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form3 = rawRow8545 := by decide +kernel

theorem rowCheck8545 : row8545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8545 := by decide +kernel

theorem rowEval8545 (x : Key → ℝ) : Integer.Sparse.eval row8545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8545, Integer.Sparse.eval_collectBalanced, rawRowCheck8545]

theorem rawRowCheck8546 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form3 = rawRow8546 := by decide +kernel

theorem rowCheck8546 : row8546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8546 := by decide +kernel

theorem rowEval8546 (x : Key → ℝ) : Integer.Sparse.eval row8546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8546, Integer.Sparse.eval_collectBalanced, rawRowCheck8546]

theorem rawRowCheck8547 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form3 = rawRow8547 := by decide +kernel

theorem rowCheck8547 : row8547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8547 := by decide +kernel

theorem rowEval8547 (x : Key → ℝ) : Integer.Sparse.eval row8547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8547, Integer.Sparse.eval_collectBalanced, rawRowCheck8547]

theorem rawRowCheck8548 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form3 = rawRow8548 := by decide +kernel

theorem rowCheck8548 : row8548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8548 := by decide +kernel

theorem rowEval8548 (x : Key → ℝ) : Integer.Sparse.eval row8548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8548, Integer.Sparse.eval_collectBalanced, rawRowCheck8548]

theorem rawRowCheck8549 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8549 := by decide +kernel

theorem rowCheck8549 : row8549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8549 := by decide +kernel

theorem rowEval8549 (x : Key → ℝ) : Integer.Sparse.eval row8549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8549, Integer.Sparse.eval_collectBalanced, rawRowCheck8549]

theorem rawRowCheck8550 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4 = rawRow8550 := by decide +kernel

theorem rowCheck8550 : row8550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8550 := by decide +kernel

theorem rowEval8550 (x : Key → ℝ) : Integer.Sparse.eval row8550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8550, Integer.Sparse.eval_collectBalanced, rawRowCheck8550]

theorem rawRowCheck8551 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4 = rawRow8551 := by decide +kernel

theorem rowCheck8551 : row8551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8551 := by decide +kernel

theorem rowEval8551 (x : Key → ℝ) : Integer.Sparse.eval row8551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8551, Integer.Sparse.eval_collectBalanced, rawRowCheck8551]

theorem rawRowCheck8552 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4 = rawRow8552 := by decide +kernel

theorem rowCheck8552 : row8552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8552 := by decide +kernel

theorem rowEval8552 (x : Key → ℝ) : Integer.Sparse.eval row8552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8552, Integer.Sparse.eval_collectBalanced, rawRowCheck8552]

theorem rawRowCheck8553 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow8553 := by decide +kernel

theorem rowCheck8553 : row8553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8553 := by decide +kernel

theorem rowEval8553 (x : Key → ℝ) : Integer.Sparse.eval row8553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8553, Integer.Sparse.eval_collectBalanced, rawRowCheck8553]

theorem rawRowCheck8554 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow8554 := by decide +kernel

theorem rowCheck8554 : row8554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8554 := by decide +kernel

theorem rowEval8554 (x : Key → ℝ) : Integer.Sparse.eval row8554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8554, Integer.Sparse.eval_collectBalanced, rawRowCheck8554]

theorem rawRowCheck8555 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow8555 := by decide +kernel

theorem rowCheck8555 : row8555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8555 := by decide +kernel

theorem rowEval8555 (x : Key → ℝ) : Integer.Sparse.eval row8555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8555, Integer.Sparse.eval_collectBalanced, rawRowCheck8555]

theorem rawRowCheck8556 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow8556 := by decide +kernel

theorem rowCheck8556 : row8556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8556 := by decide +kernel

theorem rowEval8556 (x : Key → ℝ) : Integer.Sparse.eval row8556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8556, Integer.Sparse.eval_collectBalanced, rawRowCheck8556]

theorem rawRowCheck8557 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow8557 := by decide +kernel

theorem rowCheck8557 : row8557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8557 := by decide +kernel

theorem rowEval8557 (x : Key → ℝ) : Integer.Sparse.eval row8557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8557, Integer.Sparse.eval_collectBalanced, rawRowCheck8557]

theorem rawRowCheck8558 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow8558 := by decide +kernel

theorem rowCheck8558 : row8558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8558 := by decide +kernel

theorem rowEval8558 (x : Key → ℝ) : Integer.Sparse.eval row8558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8558, Integer.Sparse.eval_collectBalanced, rawRowCheck8558]

theorem rawRowCheck8559 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form4 = rawRow8559 := by decide +kernel

theorem rowCheck8559 : row8559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8559 := by decide +kernel

theorem rowEval8559 (x : Key → ℝ) : Integer.Sparse.eval row8559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8559, Integer.Sparse.eval_collectBalanced, rawRowCheck8559]

theorem rawRowCheck8560 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form4 = rawRow8560 := by decide +kernel

theorem rowCheck8560 : row8560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8560 := by decide +kernel

theorem rowEval8560 (x : Key → ℝ) : Integer.Sparse.eval row8560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8560, Integer.Sparse.eval_collectBalanced, rawRowCheck8560]

theorem rawRowCheck8561 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form4 = rawRow8561 := by decide +kernel

theorem rowCheck8561 : row8561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8561 := by decide +kernel

theorem rowEval8561 (x : Key → ℝ) : Integer.Sparse.eval row8561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8561, Integer.Sparse.eval_collectBalanced, rawRowCheck8561]

theorem rawRowCheck8562 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form4 = rawRow8562 := by decide +kernel

theorem rowCheck8562 : row8562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8562 := by decide +kernel

theorem rowEval8562 (x : Key → ℝ) : Integer.Sparse.eval row8562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8562, Integer.Sparse.eval_collectBalanced, rawRowCheck8562]

theorem rawRowCheck8563 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form4 = rawRow8563 := by decide +kernel

theorem rowCheck8563 : row8563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8563 := by decide +kernel

theorem rowEval8563 (x : Key → ℝ) : Integer.Sparse.eval row8563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8563, Integer.Sparse.eval_collectBalanced, rawRowCheck8563]

theorem rawRowCheck8564 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form4 = rawRow8564 := by decide +kernel

theorem rowCheck8564 : row8564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8564 := by decide +kernel

theorem rowEval8564 (x : Key → ℝ) : Integer.Sparse.eval row8564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8564, Integer.Sparse.eval_collectBalanced, rawRowCheck8564]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck8581 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8581 := by decide +kernel

theorem rowCheck8581 : row8581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8581 := by decide +kernel

theorem rowEval8581 (x : Key → ℝ) : Integer.Sparse.eval row8581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8581, Integer.Sparse.eval_collectBalanced, rawRowCheck8581]

theorem rawRowCheck8582 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8582 := by decide +kernel

theorem rowCheck8582 : row8582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8582 := by decide +kernel

theorem rowEval8582 (x : Key → ℝ) : Integer.Sparse.eval row8582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8582, Integer.Sparse.eval_collectBalanced, rawRowCheck8582]

theorem rawRowCheck8583 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8583 := by decide +kernel

theorem rowCheck8583 : row8583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8583 := by decide +kernel

theorem rowEval8583 (x : Key → ℝ) : Integer.Sparse.eval row8583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8583, Integer.Sparse.eval_collectBalanced, rawRowCheck8583]

theorem rawRowCheck8584 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8584 := by decide +kernel

theorem rowCheck8584 : row8584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8584 := by decide +kernel

theorem rowEval8584 (x : Key → ℝ) : Integer.Sparse.eval row8584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8584, Integer.Sparse.eval_collectBalanced, rawRowCheck8584]

theorem rawRowCheck8585 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow8585 := by decide +kernel

theorem rowCheck8585 : row8585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8585 := by decide +kernel

theorem rowEval8585 (x : Key → ℝ) : Integer.Sparse.eval row8585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8585, Integer.Sparse.eval_collectBalanced, rawRowCheck8585]

theorem rawRowCheck8586 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow8586 := by decide +kernel

theorem rowCheck8586 : row8586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8586 := by decide +kernel

theorem rowEval8586 (x : Key → ℝ) : Integer.Sparse.eval row8586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8586, Integer.Sparse.eval_collectBalanced, rawRowCheck8586]

theorem rawRowCheck8587 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow8587 := by decide +kernel

theorem rowCheck8587 : row8587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8587 := by decide +kernel

theorem rowEval8587 (x : Key → ℝ) : Integer.Sparse.eval row8587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8587, Integer.Sparse.eval_collectBalanced, rawRowCheck8587]

theorem rawRowCheck8588 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8588 := by decide +kernel

theorem rowCheck8588 : row8588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8588 := by decide +kernel

theorem rowEval8588 (x : Key → ℝ) : Integer.Sparse.eval row8588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8588, Integer.Sparse.eval_collectBalanced, rawRowCheck8588]

theorem rawRowCheck8589 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8589 := by decide +kernel

theorem rowCheck8589 : row8589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8589 := by decide +kernel

theorem rowEval8589 (x : Key → ℝ) : Integer.Sparse.eval row8589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8589, Integer.Sparse.eval_collectBalanced, rawRowCheck8589]

theorem rawRowCheck8590 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8590 := by decide +kernel

theorem rowCheck8590 : row8590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8590 := by decide +kernel

theorem rowEval8590 (x : Key → ℝ) : Integer.Sparse.eval row8590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8590, Integer.Sparse.eval_collectBalanced, rawRowCheck8590]

theorem rawRowCheck8591 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form6 = rawRow8591 := by decide +kernel

theorem rowCheck8591 : row8591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8591 := by decide +kernel

theorem rowEval8591 (x : Key → ℝ) : Integer.Sparse.eval row8591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8591, Integer.Sparse.eval_collectBalanced, rawRowCheck8591]

theorem rawRowCheck8592 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form6 = rawRow8592 := by decide +kernel

theorem rowCheck8592 : row8592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8592 := by decide +kernel

theorem rowEval8592 (x : Key → ℝ) : Integer.Sparse.eval row8592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8592, Integer.Sparse.eval_collectBalanced, rawRowCheck8592]

theorem rawRowCheck8593 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form6 = rawRow8593 := by decide +kernel

theorem rowCheck8593 : row8593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8593 := by decide +kernel

theorem rowEval8593 (x : Key → ℝ) : Integer.Sparse.eval row8593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8593, Integer.Sparse.eval_collectBalanced, rawRowCheck8593]

theorem rawRowCheck8594 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form6 = rawRow8594 := by decide +kernel

theorem rowCheck8594 : row8594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8594 := by decide +kernel

theorem rowEval8594 (x : Key → ℝ) : Integer.Sparse.eval row8594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8594, Integer.Sparse.eval_collectBalanced, rawRowCheck8594]

theorem rawRowCheck8595 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form6 = rawRow8595 := by decide +kernel

theorem rowCheck8595 : row8595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8595 := by decide +kernel

theorem rowEval8595 (x : Key → ℝ) : Integer.Sparse.eval row8595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8595, Integer.Sparse.eval_collectBalanced, rawRowCheck8595]

theorem rawRowCheck8596 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form6 = rawRow8596 := by decide +kernel

theorem rowCheck8596 : row8596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8596 := by decide +kernel

theorem rowEval8596 (x : Key → ℝ) : Integer.Sparse.eval row8596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8596, Integer.Sparse.eval_collectBalanced, rawRowCheck8596]

theorem rawRowCheck8597 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8597 := by decide +kernel

theorem rowCheck8597 : row8597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8597 := by decide +kernel

theorem rowEval8597 (x : Key → ℝ) : Integer.Sparse.eval row8597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8597, Integer.Sparse.eval_collectBalanced, rawRowCheck8597]

theorem rawRowCheck8598 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7 = rawRow8598 := by decide +kernel

theorem rowCheck8598 : row8598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8598 := by decide +kernel

theorem rowEval8598 (x : Key → ℝ) : Integer.Sparse.eval row8598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8598, Integer.Sparse.eval_collectBalanced, rawRowCheck8598]

theorem rawRowCheck8599 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7 = rawRow8599 := by decide +kernel

theorem rowCheck8599 : row8599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8599 := by decide +kernel

theorem rowEval8599 (x : Key → ℝ) : Integer.Sparse.eval row8599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8599, Integer.Sparse.eval_collectBalanced, rawRowCheck8599]

theorem rawRowCheck8600 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7 = rawRow8600 := by decide +kernel

theorem rowCheck8600 : row8600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8600 := by decide +kernel

theorem rowEval8600 (x : Key → ℝ) : Integer.Sparse.eval row8600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8600, Integer.Sparse.eval_collectBalanced, rawRowCheck8600]

theorem rawRowCheck8601 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow8601 := by decide +kernel

theorem rowCheck8601 : row8601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8601 := by decide +kernel

theorem rowEval8601 (x : Key → ℝ) : Integer.Sparse.eval row8601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8601, Integer.Sparse.eval_collectBalanced, rawRowCheck8601]

theorem rawRowCheck8602 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow8602 := by decide +kernel

theorem rowCheck8602 : row8602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8602 := by decide +kernel

theorem rowEval8602 (x : Key → ℝ) : Integer.Sparse.eval row8602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8602, Integer.Sparse.eval_collectBalanced, rawRowCheck8602]

theorem rawRowCheck8603 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow8603 := by decide +kernel

theorem rowCheck8603 : row8603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8603 := by decide +kernel

theorem rowEval8603 (x : Key → ℝ) : Integer.Sparse.eval row8603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8603, Integer.Sparse.eval_collectBalanced, rawRowCheck8603]

theorem rawRowCheck8604 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form7 = rawRow8604 := by decide +kernel

theorem rowCheck8604 : row8604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8604 := by decide +kernel

theorem rowEval8604 (x : Key → ℝ) : Integer.Sparse.eval row8604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8604, Integer.Sparse.eval_collectBalanced, rawRowCheck8604]

theorem rawRowCheck8605 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form7 = rawRow8605 := by decide +kernel

theorem rowCheck8605 : row8605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8605 := by decide +kernel

theorem rowEval8605 (x : Key → ℝ) : Integer.Sparse.eval row8605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8605, Integer.Sparse.eval_collectBalanced, rawRowCheck8605]

theorem rawRowCheck8606 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form7 = rawRow8606 := by decide +kernel

theorem rowCheck8606 : row8606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8606 := by decide +kernel

theorem rowEval8606 (x : Key → ℝ) : Integer.Sparse.eval row8606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8606, Integer.Sparse.eval_collectBalanced, rawRowCheck8606]

theorem rawRowCheck8607 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form7 = rawRow8607 := by decide +kernel

theorem rowCheck8607 : row8607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8607 := by decide +kernel

theorem rowEval8607 (x : Key → ℝ) : Integer.Sparse.eval row8607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8607, Integer.Sparse.eval_collectBalanced, rawRowCheck8607]

theorem rawRowCheck8608 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form7 = rawRow8608 := by decide +kernel

theorem rowCheck8608 : row8608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8608 := by decide +kernel

theorem rowEval8608 (x : Key → ℝ) : Integer.Sparse.eval row8608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8608, Integer.Sparse.eval_collectBalanced, rawRowCheck8608]

theorem rawRowCheck8609 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form7 = rawRow8609 := by decide +kernel

theorem rowCheck8609 : row8609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8609 := by decide +kernel

theorem rowEval8609 (x : Key → ℝ) : Integer.Sparse.eval row8609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8609, Integer.Sparse.eval_collectBalanced, rawRowCheck8609]

theorem rawRowCheck8610 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form7 = rawRow8610 := by decide +kernel

theorem rowCheck8610 : row8610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8610 := by decide +kernel

theorem rowEval8610 (x : Key → ℝ) : Integer.Sparse.eval row8610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8610, Integer.Sparse.eval_collectBalanced, rawRowCheck8610]

theorem rawRowCheck8611 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form7 = rawRow8611 := by decide +kernel

theorem rowCheck8611 : row8611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8611 := by decide +kernel

theorem rowEval8611 (x : Key → ℝ) : Integer.Sparse.eval row8611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8611, Integer.Sparse.eval_collectBalanced, rawRowCheck8611]

theorem rawRowCheck8612 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form7 = rawRow8612 := by decide +kernel

theorem rowCheck8612 : row8612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8612 := by decide +kernel

theorem rowEval8612 (x : Key → ℝ) : Integer.Sparse.eval row8612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8612, Integer.Sparse.eval_collectBalanced, rawRowCheck8612]

theorem rawRowCheck8613 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8613 := by decide +kernel

theorem rowCheck8613 : row8613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8613 := by decide +kernel

theorem rowEval8613 (x : Key → ℝ) : Integer.Sparse.eval row8613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8613, Integer.Sparse.eval_collectBalanced, rawRowCheck8613]

theorem rawRowCheck8614 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form8 = rawRow8614 := by decide +kernel

theorem rowCheck8614 : row8614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8614 := by decide +kernel

theorem rowEval8614 (x : Key → ℝ) : Integer.Sparse.eval row8614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8614, Integer.Sparse.eval_collectBalanced, rawRowCheck8614]

theorem rawRowCheck8615 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form8 = rawRow8615 := by decide +kernel

theorem rowCheck8615 : row8615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8615 := by decide +kernel

theorem rowEval8615 (x : Key → ℝ) : Integer.Sparse.eval row8615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8615, Integer.Sparse.eval_collectBalanced, rawRowCheck8615]

theorem rawRowCheck8616 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form8 = rawRow8616 := by decide +kernel

theorem rowCheck8616 : row8616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8616 := by decide +kernel

theorem rowEval8616 (x : Key → ℝ) : Integer.Sparse.eval row8616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8616, Integer.Sparse.eval_collectBalanced, rawRowCheck8616]

theorem rawRowCheck8617 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form8 = rawRow8617 := by decide +kernel

theorem rowCheck8617 : row8617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8617 := by decide +kernel

theorem rowEval8617 (x : Key → ℝ) : Integer.Sparse.eval row8617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8617, Integer.Sparse.eval_collectBalanced, rawRowCheck8617]

theorem rawRowCheck8618 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form8 = rawRow8618 := by decide +kernel

theorem rowCheck8618 : row8618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8618 := by decide +kernel

theorem rowEval8618 (x : Key → ℝ) : Integer.Sparse.eval row8618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8618, Integer.Sparse.eval_collectBalanced, rawRowCheck8618]

theorem rawRowCheck8619 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form8 = rawRow8619 := by decide +kernel

theorem rowCheck8619 : row8619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8619 := by decide +kernel

theorem rowEval8619 (x : Key → ℝ) : Integer.Sparse.eval row8619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8619, Integer.Sparse.eval_collectBalanced, rawRowCheck8619]

theorem rawRowCheck8620 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form8 = rawRow8620 := by decide +kernel

theorem rowCheck8620 : row8620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8620 := by decide +kernel

theorem rowEval8620 (x : Key → ℝ) : Integer.Sparse.eval row8620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8620, Integer.Sparse.eval_collectBalanced, rawRowCheck8620]

theorem rawRowCheck8621 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form8 = rawRow8621 := by decide +kernel

theorem rowCheck8621 : row8621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8621 := by decide +kernel

theorem rowEval8621 (x : Key → ℝ) : Integer.Sparse.eval row8621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8621, Integer.Sparse.eval_collectBalanced, rawRowCheck8621]

theorem rawRowCheck8622 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form8 = rawRow8622 := by decide +kernel

theorem rowCheck8622 : row8622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8622 := by decide +kernel

theorem rowEval8622 (x : Key → ℝ) : Integer.Sparse.eval row8622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8622, Integer.Sparse.eval_collectBalanced, rawRowCheck8622]

theorem rawRowCheck8623 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form8 = rawRow8623 := by decide +kernel

theorem rowCheck8623 : row8623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8623 := by decide +kernel

theorem rowEval8623 (x : Key → ℝ) : Integer.Sparse.eval row8623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8623, Integer.Sparse.eval_collectBalanced, rawRowCheck8623]

theorem rawRowCheck8624 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form8 = rawRow8624 := by decide +kernel

theorem rowCheck8624 : row8624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8624 := by decide +kernel

theorem rowEval8624 (x : Key → ℝ) : Integer.Sparse.eval row8624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8624, Integer.Sparse.eval_collectBalanced, rawRowCheck8624]

theorem rawRowCheck8625 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form8 = rawRow8625 := by decide +kernel

theorem rowCheck8625 : row8625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8625 := by decide +kernel

theorem rowEval8625 (x : Key → ℝ) : Integer.Sparse.eval row8625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8625, Integer.Sparse.eval_collectBalanced, rawRowCheck8625]

theorem rawRowCheck8626 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form8 = rawRow8626 := by decide +kernel

theorem rowCheck8626 : row8626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8626 := by decide +kernel

theorem rowEval8626 (x : Key → ℝ) : Integer.Sparse.eval row8626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8626, Integer.Sparse.eval_collectBalanced, rawRowCheck8626]

theorem rawRowCheck8627 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form8 = rawRow8627 := by decide +kernel

theorem rowCheck8627 : row8627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8627 := by decide +kernel

theorem rowEval8627 (x : Key → ℝ) : Integer.Sparse.eval row8627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8627, Integer.Sparse.eval_collectBalanced, rawRowCheck8627]

theorem rawRowCheck8628 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form8 = rawRow8628 := by decide +kernel

theorem rowCheck8628 : row8628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8628 := by decide +kernel

theorem rowEval8628 (x : Key → ℝ) : Integer.Sparse.eval row8628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8628, Integer.Sparse.eval_collectBalanced, rawRowCheck8628]

theorem rawRowCheck8629 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8629 := by decide +kernel

theorem rowCheck8629 : row8629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8629 := by decide +kernel

theorem rowEval8629 (x : Key → ℝ) : Integer.Sparse.eval row8629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8629, Integer.Sparse.eval_collectBalanced, rawRowCheck8629]

theorem rawRowCheck8630 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form9 = rawRow8630 := by decide +kernel

theorem rowCheck8630 : row8630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8630 := by decide +kernel

theorem rowEval8630 (x : Key → ℝ) : Integer.Sparse.eval row8630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8630, Integer.Sparse.eval_collectBalanced, rawRowCheck8630]

theorem rawRowCheck8631 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form9 = rawRow8631 := by decide +kernel

theorem rowCheck8631 : row8631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8631 := by decide +kernel

theorem rowEval8631 (x : Key → ℝ) : Integer.Sparse.eval row8631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8631, Integer.Sparse.eval_collectBalanced, rawRowCheck8631]

theorem rawRowCheck8632 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form9 = rawRow8632 := by decide +kernel

theorem rowCheck8632 : row8632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8632 := by decide +kernel

theorem rowEval8632 (x : Key → ℝ) : Integer.Sparse.eval row8632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8632, Integer.Sparse.eval_collectBalanced, rawRowCheck8632]

theorem rawRowCheck8633 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form9 = rawRow8633 := by decide +kernel

theorem rowCheck8633 : row8633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8633 := by decide +kernel

theorem rowEval8633 (x : Key → ℝ) : Integer.Sparse.eval row8633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8633, Integer.Sparse.eval_collectBalanced, rawRowCheck8633]

theorem rawRowCheck8634 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form9 = rawRow8634 := by decide +kernel

theorem rowCheck8634 : row8634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8634 := by decide +kernel

theorem rowEval8634 (x : Key → ℝ) : Integer.Sparse.eval row8634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8634, Integer.Sparse.eval_collectBalanced, rawRowCheck8634]

theorem rawRowCheck8635 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form9 = rawRow8635 := by decide +kernel

theorem rowCheck8635 : row8635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8635 := by decide +kernel

theorem rowEval8635 (x : Key → ℝ) : Integer.Sparse.eval row8635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8635, Integer.Sparse.eval_collectBalanced, rawRowCheck8635]

theorem rawRowCheck8636 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form9 = rawRow8636 := by decide +kernel

theorem rowCheck8636 : row8636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8636 := by decide +kernel

theorem rowEval8636 (x : Key → ℝ) : Integer.Sparse.eval row8636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8636, Integer.Sparse.eval_collectBalanced, rawRowCheck8636]

theorem rawRowCheck8637 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form9 = rawRow8637 := by decide +kernel

theorem rowCheck8637 : row8637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8637 := by decide +kernel

theorem rowEval8637 (x : Key → ℝ) : Integer.Sparse.eval row8637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8637, Integer.Sparse.eval_collectBalanced, rawRowCheck8637]

theorem rawRowCheck8638 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form9 = rawRow8638 := by decide +kernel

theorem rowCheck8638 : row8638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8638 := by decide +kernel

theorem rowEval8638 (x : Key → ℝ) : Integer.Sparse.eval row8638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8638, Integer.Sparse.eval_collectBalanced, rawRowCheck8638]

theorem rawRowCheck8639 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form9 = rawRow8639 := by decide +kernel

theorem rowCheck8639 : row8639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8639 := by decide +kernel

theorem rowEval8639 (x : Key → ℝ) : Integer.Sparse.eval row8639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8639, Integer.Sparse.eval_collectBalanced, rawRowCheck8639]

theorem rawRowCheck8640 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form9 = rawRow8640 := by decide +kernel

theorem rowCheck8640 : row8640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8640 := by decide +kernel

theorem rowEval8640 (x : Key → ℝ) : Integer.Sparse.eval row8640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8640, Integer.Sparse.eval_collectBalanced, rawRowCheck8640]

theorem rawRowCheck8641 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form9 = rawRow8641 := by decide +kernel

theorem rowCheck8641 : row8641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8641 := by decide +kernel

theorem rowEval8641 (x : Key → ℝ) : Integer.Sparse.eval row8641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8641, Integer.Sparse.eval_collectBalanced, rawRowCheck8641]

theorem rawRowCheck8642 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form9 = rawRow8642 := by decide +kernel

theorem rowCheck8642 : row8642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8642 := by decide +kernel

theorem rowEval8642 (x : Key → ℝ) : Integer.Sparse.eval row8642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8642, Integer.Sparse.eval_collectBalanced, rawRowCheck8642]

theorem rawRowCheck8643 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form9 = rawRow8643 := by decide +kernel

theorem rowCheck8643 : row8643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8643 := by decide +kernel

theorem rowEval8643 (x : Key → ℝ) : Integer.Sparse.eval row8643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8643, Integer.Sparse.eval_collectBalanced, rawRowCheck8643]

theorem rawRowCheck8644 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form9 = rawRow8644 := by decide +kernel

theorem rowCheck8644 : row8644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8644 := by decide +kernel

theorem rowEval8644 (x : Key → ℝ) : Integer.Sparse.eval row8644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8644, Integer.Sparse.eval_collectBalanced, rawRowCheck8644]

theorem rawRowCheck8645 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8645 := by decide +kernel

theorem rowCheck8645 : row8645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8645 := by decide +kernel

theorem rowEval8645 (x : Key → ℝ) : Integer.Sparse.eval row8645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8645, Integer.Sparse.eval_collectBalanced, rawRowCheck8645]

theorem rawRowCheck8646 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10 = rawRow8646 := by decide +kernel

theorem rowCheck8646 : row8646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8646 := by decide +kernel

theorem rowEval8646 (x : Key → ℝ) : Integer.Sparse.eval row8646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8646, Integer.Sparse.eval_collectBalanced, rawRowCheck8646]

theorem rawRowCheck8647 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10 = rawRow8647 := by decide +kernel

theorem rowCheck8647 : row8647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8647 := by decide +kernel

theorem rowEval8647 (x : Key → ℝ) : Integer.Sparse.eval row8647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8647, Integer.Sparse.eval_collectBalanced, rawRowCheck8647]

theorem rawRowCheck8648 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10 = rawRow8648 := by decide +kernel

theorem rowCheck8648 : row8648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8648 := by decide +kernel

theorem rowEval8648 (x : Key → ℝ) : Integer.Sparse.eval row8648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8648, Integer.Sparse.eval_collectBalanced, rawRowCheck8648]

theorem rawRowCheck8649 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form10 = rawRow8649 := by decide +kernel

theorem rowCheck8649 : row8649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8649 := by decide +kernel

theorem rowEval8649 (x : Key → ℝ) : Integer.Sparse.eval row8649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8649, Integer.Sparse.eval_collectBalanced, rawRowCheck8649]

theorem rawRowCheck8650 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form10 = rawRow8650 := by decide +kernel

theorem rowCheck8650 : row8650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8650 := by decide +kernel

theorem rowEval8650 (x : Key → ℝ) : Integer.Sparse.eval row8650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8650, Integer.Sparse.eval_collectBalanced, rawRowCheck8650]

theorem rawRowCheck8651 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form10 = rawRow8651 := by decide +kernel

theorem rowCheck8651 : row8651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8651 := by decide +kernel

theorem rowEval8651 (x : Key → ℝ) : Integer.Sparse.eval row8651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8651, Integer.Sparse.eval_collectBalanced, rawRowCheck8651]

theorem rawRowCheck8652 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form10 = rawRow8652 := by decide +kernel

theorem rowCheck8652 : row8652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8652 := by decide +kernel

theorem rowEval8652 (x : Key → ℝ) : Integer.Sparse.eval row8652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8652, Integer.Sparse.eval_collectBalanced, rawRowCheck8652]

theorem rawRowCheck8653 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form10 = rawRow8653 := by decide +kernel

theorem rowCheck8653 : row8653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8653 := by decide +kernel

theorem rowEval8653 (x : Key → ℝ) : Integer.Sparse.eval row8653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8653, Integer.Sparse.eval_collectBalanced, rawRowCheck8653]

theorem rawRowCheck8654 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form10 = rawRow8654 := by decide +kernel

theorem rowCheck8654 : row8654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8654 := by decide +kernel

theorem rowEval8654 (x : Key → ℝ) : Integer.Sparse.eval row8654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8654, Integer.Sparse.eval_collectBalanced, rawRowCheck8654]

theorem rawRowCheck8655 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form10 = rawRow8655 := by decide +kernel

theorem rowCheck8655 : row8655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8655 := by decide +kernel

theorem rowEval8655 (x : Key → ℝ) : Integer.Sparse.eval row8655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8655, Integer.Sparse.eval_collectBalanced, rawRowCheck8655]

theorem rawRowCheck8656 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form10 = rawRow8656 := by decide +kernel

theorem rowCheck8656 : row8656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8656 := by decide +kernel

theorem rowEval8656 (x : Key → ℝ) : Integer.Sparse.eval row8656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8656, Integer.Sparse.eval_collectBalanced, rawRowCheck8656]

theorem rawRowCheck8657 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form10 = rawRow8657 := by decide +kernel

theorem rowCheck8657 : row8657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8657 := by decide +kernel

theorem rowEval8657 (x : Key → ℝ) : Integer.Sparse.eval row8657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8657, Integer.Sparse.eval_collectBalanced, rawRowCheck8657]

theorem rawRowCheck8658 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form10 = rawRow8658 := by decide +kernel

theorem rowCheck8658 : row8658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8658 := by decide +kernel

theorem rowEval8658 (x : Key → ℝ) : Integer.Sparse.eval row8658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8658, Integer.Sparse.eval_collectBalanced, rawRowCheck8658]

theorem rawRowCheck8659 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form10 = rawRow8659 := by decide +kernel

theorem rowCheck8659 : row8659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8659 := by decide +kernel

theorem rowEval8659 (x : Key → ℝ) : Integer.Sparse.eval row8659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8659, Integer.Sparse.eval_collectBalanced, rawRowCheck8659]

theorem rawRowCheck8660 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form10 = rawRow8660 := by decide +kernel

theorem rowCheck8660 : row8660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8660 := by decide +kernel

theorem rowEval8660 (x : Key → ℝ) : Integer.Sparse.eval row8660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8660, Integer.Sparse.eval_collectBalanced, rawRowCheck8660]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8485 x
  · exact rowEval8486 x
  · exact rowEval8487 x
  · exact rowEval8488 x
  · exact rowEval8489 x
  · exact rowEval8490 x
  · exact rowEval8491 x
  · exact rowEval8492 x
  · exact rowEval8493 x
  · exact rowEval8494 x
  · exact rowEval8495 x
  · exact rowEval8496 x
  · exact rowEval8497 x
  · exact rowEval8498 x
  · exact rowEval8499 x
  · exact rowEval8500 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8501 x
  · exact rowEval8502 x
  · exact rowEval8503 x
  · exact rowEval8504 x
  · exact rowEval8505 x
  · exact rowEval8506 x
  · exact rowEval8507 x
  · exact rowEval8508 x
  · exact rowEval8509 x
  · exact rowEval8510 x
  · exact rowEval8511 x
  · exact rowEval8512 x
  · exact rowEval8513 x
  · exact rowEval8514 x
  · exact rowEval8515 x
  · exact rowEval8516 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8517 x
  · exact rowEval8518 x
  · exact rowEval8519 x
  · exact rowEval8520 x
  · exact rowEval8521 x
  · exact rowEval8522 x
  · exact rowEval8523 x
  · exact rowEval8524 x
  · exact rowEval8525 x
  · exact rowEval8526 x
  · exact rowEval8527 x
  · exact rowEval8528 x
  · exact rowEval8529 x
  · exact rowEval8530 x
  · exact rowEval8531 x
  · exact rowEval8532 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8533 x
  · exact rowEval8534 x
  · exact rowEval8535 x
  · exact rowEval8536 x
  · exact rowEval8537 x
  · exact rowEval8538 x
  · exact rowEval8539 x
  · exact rowEval8540 x
  · exact rowEval8541 x
  · exact rowEval8542 x
  · exact rowEval8543 x
  · exact rowEval8544 x
  · exact rowEval8545 x
  · exact rowEval8546 x
  · exact rowEval8547 x
  · exact rowEval8548 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8549 x
  · exact rowEval8550 x
  · exact rowEval8551 x
  · exact rowEval8552 x
  · exact rowEval8553 x
  · exact rowEval8554 x
  · exact rowEval8555 x
  · exact rowEval8556 x
  · exact rowEval8557 x
  · exact rowEval8558 x
  · exact rowEval8559 x
  · exact rowEval8560 x
  · exact rowEval8561 x
  · exact rowEval8562 x
  · exact rowEval8563 x
  · exact rowEval8564 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8581 x
  · exact rowEval8582 x
  · exact rowEval8583 x
  · exact rowEval8584 x
  · exact rowEval8585 x
  · exact rowEval8586 x
  · exact rowEval8587 x
  · exact rowEval8588 x
  · exact rowEval8589 x
  · exact rowEval8590 x
  · exact rowEval8591 x
  · exact rowEval8592 x
  · exact rowEval8593 x
  · exact rowEval8594 x
  · exact rowEval8595 x
  · exact rowEval8596 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8597 x
  · exact rowEval8598 x
  · exact rowEval8599 x
  · exact rowEval8600 x
  · exact rowEval8601 x
  · exact rowEval8602 x
  · exact rowEval8603 x
  · exact rowEval8604 x
  · exact rowEval8605 x
  · exact rowEval8606 x
  · exact rowEval8607 x
  · exact rowEval8608 x
  · exact rowEval8609 x
  · exact rowEval8610 x
  · exact rowEval8611 x
  · exact rowEval8612 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8613 x
  · exact rowEval8614 x
  · exact rowEval8615 x
  · exact rowEval8616 x
  · exact rowEval8617 x
  · exact rowEval8618 x
  · exact rowEval8619 x
  · exact rowEval8620 x
  · exact rowEval8621 x
  · exact rowEval8622 x
  · exact rowEval8623 x
  · exact rowEval8624 x
  · exact rowEval8625 x
  · exact rowEval8626 x
  · exact rowEval8627 x
  · exact rowEval8628 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8629 x
  · exact rowEval8630 x
  · exact rowEval8631 x
  · exact rowEval8632 x
  · exact rowEval8633 x
  · exact rowEval8634 x
  · exact rowEval8635 x
  · exact rowEval8636 x
  · exact rowEval8637 x
  · exact rowEval8638 x
  · exact rowEval8639 x
  · exact rowEval8640 x
  · exact rowEval8641 x
  · exact rowEval8642 x
  · exact rowEval8643 x
  · exact rowEval8644 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8645 x
  · exact rowEval8646 x
  · exact rowEval8647 x
  · exact rowEval8648 x
  · exact rowEval8649 x
  · exact rowEval8650 x
  · exact rowEval8651 x
  · exact rowEval8652 x
  · exact rowEval8653 x
  · exact rowEval8654 x
  · exact rowEval8655 x
  · exact rowEval8656 x
  · exact rowEval8657 x
  · exact rowEval8658 x
  · exact rowEval8659 x
  · exact rowEval8660 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck8745 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8745 := by decide +kernel

theorem rowCheck8745 : row8745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8745 := by decide +kernel

theorem rowEval8745 (x : Key → ℝ) : Integer.Sparse.eval row8745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8745, Integer.Sparse.eval_collectBalanced, rawRowCheck8745]

theorem rawRowCheck8746 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow8746 := by decide +kernel

theorem rowCheck8746 : row8746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8746 := by decide +kernel

theorem rowEval8746 (x : Key → ℝ) : Integer.Sparse.eval row8746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8746, Integer.Sparse.eval_collectBalanced, rawRowCheck8746]

theorem rawRowCheck8747 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow8747 := by decide +kernel

theorem rowCheck8747 : row8747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8747 := by decide +kernel

theorem rowEval8747 (x : Key → ℝ) : Integer.Sparse.eval row8747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8747, Integer.Sparse.eval_collectBalanced, rawRowCheck8747]

theorem rawRowCheck8748 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow8748 := by decide +kernel

theorem rowCheck8748 : row8748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8748 := by decide +kernel

theorem rowEval8748 (x : Key → ℝ) : Integer.Sparse.eval row8748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck8748, Integer.Sparse.eval_collectBalanced, rawRowCheck8748]

theorem rawRowCheck8817 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow8817 := by decide +kernel

theorem rowCheck8817 : row8817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8817 := by decide +kernel

theorem rowEval8817 (x : Key → ℝ) : Integer.Sparse.eval row8817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8817, Integer.Sparse.eval_collectBalanced, rawRowCheck8817]

theorem rawRowCheck8818 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow8818 := by decide +kernel

theorem rowCheck8818 : row8818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8818 := by decide +kernel

theorem rowEval8818 (x : Key → ℝ) : Integer.Sparse.eval row8818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8818, Integer.Sparse.eval_collectBalanced, rawRowCheck8818]

theorem rawRowCheck8819 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow8819 := by decide +kernel

theorem rowCheck8819 : row8819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8819 := by decide +kernel

theorem rowEval8819 (x : Key → ℝ) : Integer.Sparse.eval row8819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8819, Integer.Sparse.eval_collectBalanced, rawRowCheck8819]

theorem rawRowCheck8820 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8820 := by decide +kernel

theorem rowCheck8820 : row8820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8820 := by decide +kernel

theorem rowEval8820 (x : Key → ℝ) : Integer.Sparse.eval row8820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8820, Integer.Sparse.eval_collectBalanced, rawRowCheck8820]

theorem rawRowCheck8821 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8821 := by decide +kernel

theorem rowCheck8821 : row8821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8821 := by decide +kernel

theorem rowEval8821 (x : Key → ℝ) : Integer.Sparse.eval row8821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8821, Integer.Sparse.eval_collectBalanced, rawRowCheck8821]

theorem rawRowCheck8822 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow8822 := by decide +kernel

theorem rowCheck8822 : row8822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8822 := by decide +kernel

theorem rowEval8822 (x : Key → ℝ) : Integer.Sparse.eval row8822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8822, Integer.Sparse.eval_collectBalanced, rawRowCheck8822]

theorem rawRowCheck8823 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow8823 := by decide +kernel

theorem rowCheck8823 : row8823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8823 := by decide +kernel

theorem rowEval8823 (x : Key → ℝ) : Integer.Sparse.eval row8823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8823, Integer.Sparse.eval_collectBalanced, rawRowCheck8823]

theorem rawRowCheck8824 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow8824 := by decide +kernel

theorem rowCheck8824 : row8824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8824 := by decide +kernel

theorem rowEval8824 (x : Key → ℝ) : Integer.Sparse.eval row8824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck8824, Integer.Sparse.eval_collectBalanced, rawRowCheck8824]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck11_10 : entry11_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_10 k)) := by decide +kernel

theorem rowsSound11_10 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8741 x
  · exact rowEval8742 x
  · exact rowEval8743 x
  · exact rowEval8744 x
  · exact rowEval8745 x
  · exact rowEval8746 x
  · exact rowEval8747 x
  · exact rowEval8748 x

theorem entryEval11_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_10 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck11_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_10]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck12_10 : entry12_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_10 k)) := by decide +kernel

theorem rowsSound12_10 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8817 x
  · exact rowEval8818 x
  · exact rowEval8819 x
  · exact rowEval8820 x
  · exact rowEval8821 x
  · exact rowEval8822 x
  · exact rowEval8823 x
  · exact rowEval8824 x

theorem entryEval12_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_10 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck12_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_10]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck9133 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow9133 := by decide +kernel

theorem rowCheck9133 : row9133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9133 := by decide +kernel

theorem rowEval9133 (x : Key → ℝ) : Integer.Sparse.eval row9133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9133, Integer.Sparse.eval_collectBalanced, rawRowCheck9133]

theorem rawRowCheck9134 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow9134 := by decide +kernel

theorem rowCheck9134 : row9134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9134 := by decide +kernel

theorem rowEval9134 (x : Key → ℝ) : Integer.Sparse.eval row9134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9134, Integer.Sparse.eval_collectBalanced, rawRowCheck9134]

theorem rawRowCheck9135 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow9135 := by decide +kernel

theorem rowCheck9135 : row9135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9135 := by decide +kernel

theorem rowEval9135 (x : Key → ℝ) : Integer.Sparse.eval row9135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9135, Integer.Sparse.eval_collectBalanced, rawRowCheck9135]

theorem rawRowCheck9136 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9136 := by decide +kernel

theorem rowCheck9136 : row9136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9136 := by decide +kernel

theorem rowEval9136 (x : Key → ℝ) : Integer.Sparse.eval row9136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9136, Integer.Sparse.eval_collectBalanced, rawRowCheck9136]

theorem rawRowCheck9137 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9137 := by decide +kernel

theorem rowCheck9137 : row9137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9137 := by decide +kernel

theorem rowEval9137 (x : Key → ℝ) : Integer.Sparse.eval row9137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9137, Integer.Sparse.eval_collectBalanced, rawRowCheck9137]

theorem rawRowCheck9138 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow9138 := by decide +kernel

theorem rowCheck9138 : row9138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9138 := by decide +kernel

theorem rowEval9138 (x : Key → ℝ) : Integer.Sparse.eval row9138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9138, Integer.Sparse.eval_collectBalanced, rawRowCheck9138]

theorem rawRowCheck9139 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow9139 := by decide +kernel

theorem rowCheck9139 : row9139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9139 := by decide +kernel

theorem rowEval9139 (x : Key → ℝ) : Integer.Sparse.eval row9139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9139, Integer.Sparse.eval_collectBalanced, rawRowCheck9139]

theorem rawRowCheck9140 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow9140 := by decide +kernel

theorem rowCheck9140 : row9140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9140 := by decide +kernel

theorem rowEval9140 (x : Key → ℝ) : Integer.Sparse.eval row9140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9140, Integer.Sparse.eval_collectBalanced, rawRowCheck9140]

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

theorem entryCheck14_10 : entry14_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_10 k)) := by decide +kernel

theorem rowsSound14_10 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9133 x
  · exact rowEval9134 x
  · exact rowEval9135 x
  · exact rowEval9136 x
  · exact rowEval9137 x
  · exact rowEval9138 x
  · exact rowEval9139 x
  · exact rowEval9140 x

theorem entryEval14_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_10 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck14_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_10]

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

theorem rawRowCheck9445 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9445 := by decide +kernel

theorem rowCheck9445 : row9445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9445 := by decide +kernel

theorem rowEval9445 (x : Key → ℝ) : Integer.Sparse.eval row9445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9445, Integer.Sparse.eval_collectBalanced, rawRowCheck9445]

theorem rawRowCheck9446 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form10 = rawRow9446 := by decide +kernel

theorem rowCheck9446 : row9446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9446 := by decide +kernel

theorem rowEval9446 (x : Key → ℝ) : Integer.Sparse.eval row9446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9446, Integer.Sparse.eval_collectBalanced, rawRowCheck9446]

theorem rawRowCheck9447 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form10 = rawRow9447 := by decide +kernel

theorem rowCheck9447 : row9447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9447 := by decide +kernel

theorem rowEval9447 (x : Key → ℝ) : Integer.Sparse.eval row9447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9447, Integer.Sparse.eval_collectBalanced, rawRowCheck9447]

theorem rawRowCheck9448 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form10 = rawRow9448 := by decide +kernel

theorem rowCheck9448 : row9448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9448 := by decide +kernel

theorem rowEval9448 (x : Key → ℝ) : Integer.Sparse.eval row9448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9448, Integer.Sparse.eval_collectBalanced, rawRowCheck9448]

theorem rawRowCheck9449 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9449 := by decide +kernel

theorem rowCheck9449 : row9449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9449 := by decide +kernel

theorem rowEval9449 (x : Key → ℝ) : Integer.Sparse.eval row9449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9449, Integer.Sparse.eval_collectBalanced, rawRowCheck9449]

theorem rawRowCheck9450 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10 = rawRow9450 := by decide +kernel

theorem rowCheck9450 : row9450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9450 := by decide +kernel

theorem rowEval9450 (x : Key → ℝ) : Integer.Sparse.eval row9450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9450, Integer.Sparse.eval_collectBalanced, rawRowCheck9450]

theorem rawRowCheck9451 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10 = rawRow9451 := by decide +kernel

theorem rowCheck9451 : row9451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9451 := by decide +kernel

theorem rowEval9451 (x : Key → ℝ) : Integer.Sparse.eval row9451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9451, Integer.Sparse.eval_collectBalanced, rawRowCheck9451]

theorem rawRowCheck9452 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10 = rawRow9452 := by decide +kernel

theorem rowCheck9452 : row9452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9452 := by decide +kernel

theorem rowEval9452 (x : Key → ℝ) : Integer.Sparse.eval row9452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9452, Integer.Sparse.eval_collectBalanced, rawRowCheck9452]

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

end MUB6.Certificate.GramEntries.Block3

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

theorem entryCheck16_10 : entry16_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_10 k)) := by decide +kernel

theorem rowsSound16_10 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9445 x
  · exact rowEval9446 x
  · exact rowEval9447 x
  · exact rowEval9448 x
  · exact rowEval9449 x
  · exact rowEval9450 x
  · exact rowEval9451 x
  · exact rowEval9452 x

theorem entryEval16_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_10 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck16_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_10]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10489 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form10 = rawRow10489 := by decide +kernel

theorem rowCheck10489 : row10489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10489 := by decide +kernel

theorem rowEval10489 (x : Key → ℝ) : Integer.Sparse.eval row10489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10489, Integer.Sparse.eval_collectBalanced, rawRowCheck10489]

theorem rawRowCheck10490 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form10 = rawRow10490 := by decide +kernel

theorem rowCheck10490 : row10490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10490 := by decide +kernel

theorem rowEval10490 (x : Key → ℝ) : Integer.Sparse.eval row10490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10490, Integer.Sparse.eval_collectBalanced, rawRowCheck10490]

theorem rawRowCheck10491 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form10 = rawRow10491 := by decide +kernel

theorem rowCheck10491 : row10491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10491 := by decide +kernel

theorem rowEval10491 (x : Key → ℝ) : Integer.Sparse.eval row10491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10491, Integer.Sparse.eval_collectBalanced, rawRowCheck10491]

theorem rawRowCheck10492 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form10 = rawRow10492 := by decide +kernel

theorem rowCheck10492 : row10492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10492 := by decide +kernel

theorem rowEval10492 (x : Key → ℝ) : Integer.Sparse.eval row10492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10492, Integer.Sparse.eval_collectBalanced, rawRowCheck10492]

theorem rawRowCheck10493 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form10 = rawRow10493 := by decide +kernel

theorem rowCheck10493 : row10493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10493 := by decide +kernel

theorem rowEval10493 (x : Key → ℝ) : Integer.Sparse.eval row10493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10493, Integer.Sparse.eval_collectBalanced, rawRowCheck10493]

theorem rawRowCheck10494 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form10 = rawRow10494 := by decide +kernel

theorem rowCheck10494 : row10494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10494 := by decide +kernel

theorem rowEval10494 (x : Key → ℝ) : Integer.Sparse.eval row10494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10494, Integer.Sparse.eval_collectBalanced, rawRowCheck10494]

theorem rawRowCheck10495 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form10 = rawRow10495 := by decide +kernel

theorem rowCheck10495 : row10495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10495 := by decide +kernel

theorem rowEval10495 (x : Key → ℝ) : Integer.Sparse.eval row10495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10495, Integer.Sparse.eval_collectBalanced, rawRowCheck10495]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck10496 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form10 = rawRow10496 := by decide +kernel

theorem rowCheck10496 : row10496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10496 := by decide +kernel

theorem rowEval10496 (x : Key → ℝ) : Integer.Sparse.eval row10496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10496, Integer.Sparse.eval_collectBalanced, rawRowCheck10496]

theorem rawRowCheck10497 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form10 = rawRow10497 := by decide +kernel

theorem rowCheck10497 : row10497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10497 := by decide +kernel

theorem rowEval10497 (x : Key → ℝ) : Integer.Sparse.eval row10497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10497, Integer.Sparse.eval_collectBalanced, rawRowCheck10497]

theorem rawRowCheck10498 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form10 = rawRow10498 := by decide +kernel

theorem rowCheck10498 : row10498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10498 := by decide +kernel

theorem rowEval10498 (x : Key → ℝ) : Integer.Sparse.eval row10498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10498, Integer.Sparse.eval_collectBalanced, rawRowCheck10498]

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

theorem entryCheck19_10 : entry19_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_10 k)) := by decide +kernel

theorem rowsSound19_10 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval10489 x
  · exact rowEval10490 x
  · exact rowEval10491 x
  · exact rowEval10492 x
  · exact rowEval10493 x
  · exact rowEval10494 x
  · exact rowEval10495 x
  · exact rowEval10496 x
  · exact rowEval10497 x
  · exact rowEval10498 x

theorem entryEval19_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_10 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck19_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_10]

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

theorem rawRowCheck10639 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow10639 := by decide +kernel

theorem rowCheck10639 : row10639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10639 := by decide +kernel

theorem rowEval10639 (x : Key → ℝ) : Integer.Sparse.eval row10639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck10639, Integer.Sparse.eval_collectBalanced, rawRowCheck10639]

theorem rawRowCheck10640 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow10640 := by decide +kernel

theorem rowCheck10640 : row10640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10640 := by decide +kernel

theorem rowEval10640 (x : Key → ℝ) : Integer.Sparse.eval row10640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10640, Integer.Sparse.eval_collectBalanced, rawRowCheck10640]

theorem rawRowCheck10641 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow10641 := by decide +kernel

theorem rowCheck10641 : row10641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10641 := by decide +kernel

theorem rowEval10641 (x : Key → ℝ) : Integer.Sparse.eval row10641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10641, Integer.Sparse.eval_collectBalanced, rawRowCheck10641]

theorem rawRowCheck10642 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow10642 := by decide +kernel

theorem rowCheck10642 : row10642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10642 := by decide +kernel

theorem rowEval10642 (x : Key → ℝ) : Integer.Sparse.eval row10642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10642, Integer.Sparse.eval_collectBalanced, rawRowCheck10642]

theorem rawRowCheck10643 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form10 = rawRow10643 := by decide +kernel

theorem rowCheck10643 : row10643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10643 := by decide +kernel

theorem rowEval10643 (x : Key → ℝ) : Integer.Sparse.eval row10643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10643, Integer.Sparse.eval_collectBalanced, rawRowCheck10643]

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

theorem entryCheck20_10 : entry20_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_10 k)) := by decide +kernel

theorem rowsSound20_10 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval10639 x
  · exact rowEval10640 x
  · exact rowEval10641 x
  · exact rowEval10642 x
  · exact rowEval10643 x

theorem entryEval20_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_10 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck20_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_10]

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

theorem rawRowCheck12256 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form10 = rawRow12256 := by decide +kernel

theorem rowCheck12256 : row12256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12256 := by decide +kernel

theorem rowEval12256 (x : Key → ℝ) : Integer.Sparse.eval row12256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12256, Integer.Sparse.eval_collectBalanced, rawRowCheck12256]

theorem rawRowCheck12257 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow12257 := by decide +kernel

theorem rowCheck12257 : row12257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12257 := by decide +kernel

theorem rowEval12257 (x : Key → ℝ) : Integer.Sparse.eval row12257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12257, Integer.Sparse.eval_collectBalanced, rawRowCheck12257]

theorem rawRowCheck12258 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form10 = rawRow12258 := by decide +kernel

theorem rowCheck12258 : row12258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12258 := by decide +kernel

theorem rowEval12258 (x : Key → ℝ) : Integer.Sparse.eval row12258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12258, Integer.Sparse.eval_collectBalanced, rawRowCheck12258]

theorem rawRowCheck12259 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form10 = rawRow12259 := by decide +kernel

theorem rowCheck12259 : row12259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12259 := by decide +kernel

theorem rowEval12259 (x : Key → ℝ) : Integer.Sparse.eval row12259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12259, Integer.Sparse.eval_collectBalanced, rawRowCheck12259]

theorem rawRowCheck12260 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form10 = rawRow12260 := by decide +kernel

theorem rowCheck12260 : row12260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12260 := by decide +kernel

theorem rowEval12260 (x : Key → ℝ) : Integer.Sparse.eval row12260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12260, Integer.Sparse.eval_collectBalanced, rawRowCheck12260]

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

theorem rawRowCheck12411 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form10 = rawRow12411 := by decide +kernel

theorem rowCheck12411 : row12411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12411 := by decide +kernel

theorem rowEval12411 (x : Key → ℝ) : Integer.Sparse.eval row12411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12411, Integer.Sparse.eval_collectBalanced, rawRowCheck12411]

theorem rawRowCheck12412 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form10 = rawRow12412 := by decide +kernel

theorem rowCheck12412 : row12412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12412 := by decide +kernel

theorem rowEval12412 (x : Key → ℝ) : Integer.Sparse.eval row12412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12412, Integer.Sparse.eval_collectBalanced, rawRowCheck12412]

theorem rawRowCheck12413 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form10 = rawRow12413 := by decide +kernel

theorem rowCheck12413 : row12413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12413 := by decide +kernel

theorem rowEval12413 (x : Key → ℝ) : Integer.Sparse.eval row12413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12413, Integer.Sparse.eval_collectBalanced, rawRowCheck12413]

theorem rawRowCheck12414 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form10 = rawRow12414 := by decide +kernel

theorem rowCheck12414 : row12414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12414 := by decide +kernel

theorem rowEval12414 (x : Key → ℝ) : Integer.Sparse.eval row12414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12414, Integer.Sparse.eval_collectBalanced, rawRowCheck12414]

theorem rawRowCheck12415 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form10 = rawRow12415 := by decide +kernel

theorem rowCheck12415 : row12415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12415 := by decide +kernel

theorem rowEval12415 (x : Key → ℝ) : Integer.Sparse.eval row12415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12415, Integer.Sparse.eval_collectBalanced, rawRowCheck12415]

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

theorem entryCheck24_10 : entry24_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_10 k)) := by decide +kernel

theorem rowsSound24_10 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval12256 x
  · exact rowEval12257 x
  · exact rowEval12258 x
  · exact rowEval12259 x
  · exact rowEval12260 x

theorem entryEval24_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_10 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck24_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_10]

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

theorem rawRowCheck12416 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form10 = rawRow12416 := by decide +kernel

theorem rowCheck12416 : row12416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12416 := by decide +kernel

theorem rowEval12416 (x : Key → ℝ) : Integer.Sparse.eval row12416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12416, Integer.Sparse.eval_collectBalanced, rawRowCheck12416]

theorem rawRowCheck12417 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form10 = rawRow12417 := by decide +kernel

theorem rowCheck12417 : row12417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12417 := by decide +kernel

theorem rowEval12417 (x : Key → ℝ) : Integer.Sparse.eval row12417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12417, Integer.Sparse.eval_collectBalanced, rawRowCheck12417]

theorem rawRowCheck12418 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form10 = rawRow12418 := by decide +kernel

theorem rowCheck12418 : row12418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12418 := by decide +kernel

theorem rowEval12418 (x : Key → ℝ) : Integer.Sparse.eval row12418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12418, Integer.Sparse.eval_collectBalanced, rawRowCheck12418]

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

theorem entryCheck25_10 : entry25_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_10 k)) := by decide +kernel

theorem rowsSound25_10 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval12411 x
  · exact rowEval12412 x
  · exact rowEval12413 x
  · exact rowEval12414 x
  · exact rowEval12415 x
  · exact rowEval12416 x
  · exact rowEval12417 x
  · exact rowEval12418 x

theorem entryEval25_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_10 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck25_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_10]

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

theorem entryEvalRow10_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 10 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 10).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval10_0 B hB
  · exact entryEval10_1 B hB
  · exact entryEval10_2 B hB
  · exact entryEval10_3 B hB
  · exact entryEval10_4 B hB
  · exact entryEval10_5_e B hB
  · exact entryEval10_6 B hB
  · exact entryEval10_7 B hB
  · exact entryEval10_8 B hB
  · exact entryEval10_9 B hB
  · exact entryEval10_10 B hB
  · exact (entryEval11_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e_oai
