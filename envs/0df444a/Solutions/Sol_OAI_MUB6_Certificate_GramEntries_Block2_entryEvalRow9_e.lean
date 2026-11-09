-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:52:52.941273+00:00
-- url     : https://prove2.me/submissions/c8404bde-9c4f-41f0-89ac-87e3c0747aff

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval9_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval9_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval9_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval9_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval9_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval9_8_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck6912 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form6 = rawRow6912 := by decide +kernel

theorem rowCheck6912 : row6912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6912 := by decide +kernel

theorem rowEval6912 (x : Key → ℝ) : Integer.Sparse.eval row6912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6912, Integer.Sparse.eval_collectBalanced, rawRowCheck6912]

theorem rawRowCheck6913 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form6 = rawRow6913 := by decide +kernel

theorem rowCheck6913 : row6913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6913 := by decide +kernel

theorem rowEval6913 (x : Key → ℝ) : Integer.Sparse.eval row6913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6913, Integer.Sparse.eval_collectBalanced, rawRowCheck6913]

theorem rawRowCheck6914 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6914 := by decide +kernel

theorem rowCheck6914 : row6914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6914 := by decide +kernel

theorem rowEval6914 (x : Key → ℝ) : Integer.Sparse.eval row6914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6914, Integer.Sparse.eval_collectBalanced, rawRowCheck6914]

theorem rawRowCheck6915 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6915 := by decide +kernel

theorem rowCheck6915 : row6915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6915 := by decide +kernel

theorem rowEval6915 (x : Key → ℝ) : Integer.Sparse.eval row6915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6915, Integer.Sparse.eval_collectBalanced, rawRowCheck6915]

theorem rawRowCheck6916 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form6 = rawRow6916 := by decide +kernel

theorem rowCheck6916 : row6916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6916 := by decide +kernel

theorem rowEval6916 (x : Key → ℝ) : Integer.Sparse.eval row6916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6916, Integer.Sparse.eval_collectBalanced, rawRowCheck6916]

theorem rawRowCheck6917 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form6 = rawRow6917 := by decide +kernel

theorem rowCheck6917 : row6917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6917 := by decide +kernel

theorem rowEval6917 (x : Key → ℝ) : Integer.Sparse.eval row6917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6917, Integer.Sparse.eval_collectBalanced, rawRowCheck6917]

theorem rawRowCheck6918 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form6 = rawRow6918 := by decide +kernel

theorem rowCheck6918 : row6918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6918 := by decide +kernel

theorem rowEval6918 (x : Key → ℝ) : Integer.Sparse.eval row6918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6918, Integer.Sparse.eval_collectBalanced, rawRowCheck6918]

theorem rawRowCheck6919 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form6 = rawRow6919 := by decide +kernel

theorem rowCheck6919 : row6919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6919 := by decide +kernel

theorem rowEval6919 (x : Key → ℝ) : Integer.Sparse.eval row6919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6919, Integer.Sparse.eval_collectBalanced, rawRowCheck6919]

theorem rawRowCheck6920 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form6 = rawRow6920 := by decide +kernel

theorem rowCheck6920 : row6920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6920 := by decide +kernel

theorem rowEval6920 (x : Key → ℝ) : Integer.Sparse.eval row6920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6920, Integer.Sparse.eval_collectBalanced, rawRowCheck6920]

theorem rawRowCheck6921 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form6 = rawRow6921 := by decide +kernel

theorem rowCheck6921 : row6921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6921 := by decide +kernel

theorem rowEval6921 (x : Key → ℝ) : Integer.Sparse.eval row6921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6921, Integer.Sparse.eval_collectBalanced, rawRowCheck6921]

theorem rawRowCheck6922 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form6 = rawRow6922 := by decide +kernel

theorem rowCheck6922 : row6922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6922 := by decide +kernel

theorem rowEval6922 (x : Key → ℝ) : Integer.Sparse.eval row6922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6922, Integer.Sparse.eval_collectBalanced, rawRowCheck6922]

theorem rawRowCheck6923 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form6 = rawRow6923 := by decide +kernel

theorem rowCheck6923 : row6923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6923 := by decide +kernel

theorem rowEval6923 (x : Key → ℝ) : Integer.Sparse.eval row6923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6923, Integer.Sparse.eval_collectBalanced, rawRowCheck6923]

theorem rawRowCheck6924 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form6 = rawRow6924 := by decide +kernel

theorem rowCheck6924 : row6924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6924 := by decide +kernel

theorem rowEval6924 (x : Key → ℝ) : Integer.Sparse.eval row6924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6924, Integer.Sparse.eval_collectBalanced, rawRowCheck6924]

theorem rawRowCheck6925 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form6 = rawRow6925 := by decide +kernel

theorem rowCheck6925 : row6925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6925 := by decide +kernel

theorem rowEval6925 (x : Key → ℝ) : Integer.Sparse.eval row6925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6925, Integer.Sparse.eval_collectBalanced, rawRowCheck6925]

theorem rawRowCheck6926 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form6 = rawRow6926 := by decide +kernel

theorem rowCheck6926 : row6926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6926 := by decide +kernel

theorem rowEval6926 (x : Key → ℝ) : Integer.Sparse.eval row6926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6926, Integer.Sparse.eval_collectBalanced, rawRowCheck6926]

theorem rawRowCheck6927 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form6 = rawRow6927 := by decide +kernel

theorem rowCheck6927 : row6927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6927 := by decide +kernel

theorem rowEval6927 (x : Key → ℝ) : Integer.Sparse.eval row6927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6927, Integer.Sparse.eval_collectBalanced, rawRowCheck6927]

theorem rawRowCheck6988 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form9 = rawRow6988 := by decide +kernel

theorem rowCheck6988 : row6988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6988 := by decide +kernel

theorem rowEval6988 (x : Key → ℝ) : Integer.Sparse.eval row6988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6988, Integer.Sparse.eval_collectBalanced, rawRowCheck6988]

theorem rawRowCheck6989 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form9 = rawRow6989 := by decide +kernel

theorem rowCheck6989 : row6989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6989 := by decide +kernel

theorem rowEval6989 (x : Key → ℝ) : Integer.Sparse.eval row6989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6989, Integer.Sparse.eval_collectBalanced, rawRowCheck6989]

theorem rawRowCheck6990 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form9 = rawRow6990 := by decide +kernel

theorem rowCheck6990 : row6990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6990 := by decide +kernel

theorem rowEval6990 (x : Key → ℝ) : Integer.Sparse.eval row6990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6990, Integer.Sparse.eval_collectBalanced, rawRowCheck6990]

theorem rawRowCheck6991 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form9 = rawRow6991 := by decide +kernel

theorem rowCheck6991 : row6991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6991 := by decide +kernel

theorem rowEval6991 (x : Key → ℝ) : Integer.Sparse.eval row6991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6991, Integer.Sparse.eval_collectBalanced, rawRowCheck6991]

theorem rawRowCheck6992 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form9 = rawRow6992 := by decide +kernel

theorem rowCheck6992 : row6992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6992 := by decide +kernel

theorem rowEval6992 (x : Key → ℝ) : Integer.Sparse.eval row6992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6992, Integer.Sparse.eval_collectBalanced, rawRowCheck6992]

theorem rawRowCheck6993 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form9 = rawRow6993 := by decide +kernel

theorem rowCheck6993 : row6993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6993 := by decide +kernel

theorem rowEval6993 (x : Key → ℝ) : Integer.Sparse.eval row6993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6993, Integer.Sparse.eval_collectBalanced, rawRowCheck6993]

theorem rawRowCheck6994 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form9 = rawRow6994 := by decide +kernel

theorem rowCheck6994 : row6994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6994 := by decide +kernel

theorem rowEval6994 (x : Key → ℝ) : Integer.Sparse.eval row6994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6994, Integer.Sparse.eval_collectBalanced, rawRowCheck6994]

theorem rawRowCheck6995 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form9 = rawRow6995 := by decide +kernel

theorem rowCheck6995 : row6995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6995 := by decide +kernel

theorem rowEval6995 (x : Key → ℝ) : Integer.Sparse.eval row6995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6995, Integer.Sparse.eval_collectBalanced, rawRowCheck6995]

theorem rawRowCheck6996 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form9 = rawRow6996 := by decide +kernel

theorem rowCheck6996 : row6996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6996 := by decide +kernel

theorem rowEval6996 (x : Key → ℝ) : Integer.Sparse.eval row6996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6996, Integer.Sparse.eval_collectBalanced, rawRowCheck6996]

theorem rawRowCheck6997 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form9 = rawRow6997 := by decide +kernel

theorem rowCheck6997 : row6997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6997 := by decide +kernel

theorem rowEval6997 (x : Key → ℝ) : Integer.Sparse.eval row6997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6997, Integer.Sparse.eval_collectBalanced, rawRowCheck6997]

theorem rawRowCheck6998 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form9 = rawRow6998 := by decide +kernel

theorem rowCheck6998 : row6998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6998 := by decide +kernel

theorem rowEval6998 (x : Key → ℝ) : Integer.Sparse.eval row6998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck6998, Integer.Sparse.eval_collectBalanced, rawRowCheck6998]

theorem rawRowCheck6999 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form9 = rawRow6999 := by decide +kernel

theorem rowCheck6999 : row6999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6999 := by decide +kernel

theorem rowEval6999 (x : Key → ℝ) : Integer.Sparse.eval row6999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck6999, Integer.Sparse.eval_collectBalanced, rawRowCheck6999]

theorem rawRowCheck7000 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form9 = rawRow7000 := by decide +kernel

theorem rowCheck7000 : row7000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7000 := by decide +kernel

theorem rowEval7000 (x : Key → ℝ) : Integer.Sparse.eval row7000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7000, Integer.Sparse.eval_collectBalanced, rawRowCheck7000]

theorem rawRowCheck7001 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form9 = rawRow7001 := by decide +kernel

theorem rowCheck7001 : row7001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7001 := by decide +kernel

theorem rowEval7001 (x : Key → ℝ) : Integer.Sparse.eval row7001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7001, Integer.Sparse.eval_collectBalanced, rawRowCheck7001]

theorem rawRowCheck7002 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form9 = rawRow7002 := by decide +kernel

theorem rowCheck7002 : row7002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7002 := by decide +kernel

theorem rowEval7002 (x : Key → ℝ) : Integer.Sparse.eval row7002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7002, Integer.Sparse.eval_collectBalanced, rawRowCheck7002]

theorem rawRowCheck7003 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form9 = rawRow7003 := by decide +kernel

theorem rowCheck7003 : row7003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7003 := by decide +kernel

theorem rowEval7003 (x : Key → ℝ) : Integer.Sparse.eval row7003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7003, Integer.Sparse.eval_collectBalanced, rawRowCheck7003]

theorem rawRowCheck7004 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form9 = rawRow7004 := by decide +kernel

theorem rowCheck7004 : row7004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7004 := by decide +kernel

theorem rowEval7004 (x : Key → ℝ) : Integer.Sparse.eval row7004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7004, Integer.Sparse.eval_collectBalanced, rawRowCheck7004]

theorem rawRowCheck7005 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form9 = rawRow7005 := by decide +kernel

theorem rowCheck7005 : row7005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7005 := by decide +kernel

theorem rowEval7005 (x : Key → ℝ) : Integer.Sparse.eval row7005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7005, Integer.Sparse.eval_collectBalanced, rawRowCheck7005]

theorem rawRowCheck7006 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form9 = rawRow7006 := by decide +kernel

theorem rowCheck7006 : row7006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7006 := by decide +kernel

theorem rowEval7006 (x : Key → ℝ) : Integer.Sparse.eval row7006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7006, Integer.Sparse.eval_collectBalanced, rawRowCheck7006]

theorem rawRowCheck7007 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form9 = rawRow7007 := by decide +kernel

theorem rowCheck7007 : row7007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7007 := by decide +kernel

theorem rowEval7007 (x : Key → ℝ) : Integer.Sparse.eval row7007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7007, Integer.Sparse.eval_collectBalanced, rawRowCheck7007]

theorem rawRowCheck7008 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form9 = rawRow7008 := by decide +kernel

theorem rowCheck7008 : row7008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7008 := by decide +kernel

theorem rowEval7008 (x : Key → ℝ) : Integer.Sparse.eval row7008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7008, Integer.Sparse.eval_collectBalanced, rawRowCheck7008]

theorem rawRowCheck7009 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form9 = rawRow7009 := by decide +kernel

theorem rowCheck7009 : row7009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7009 := by decide +kernel

theorem rowEval7009 (x : Key → ℝ) : Integer.Sparse.eval row7009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7009, Integer.Sparse.eval_collectBalanced, rawRowCheck7009]

theorem rawRowCheck7010 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form9 = rawRow7010 := by decide +kernel

theorem rowCheck7010 : row7010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7010 := by decide +kernel

theorem rowEval7010 (x : Key → ℝ) : Integer.Sparse.eval row7010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7010, Integer.Sparse.eval_collectBalanced, rawRowCheck7010]

theorem rawRowCheck7011 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form9 = rawRow7011 := by decide +kernel

theorem rowCheck7011 : row7011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7011 := by decide +kernel

theorem rowEval7011 (x : Key → ℝ) : Integer.Sparse.eval row7011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7011, Integer.Sparse.eval_collectBalanced, rawRowCheck7011]

theorem rawRowCheck7012 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form9 = rawRow7012 := by decide +kernel

theorem rowCheck7012 : row7012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7012 := by decide +kernel

theorem rowEval7012 (x : Key → ℝ) : Integer.Sparse.eval row7012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7012, Integer.Sparse.eval_collectBalanced, rawRowCheck7012]

theorem rawRowCheck7013 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form9 = rawRow7013 := by decide +kernel

theorem rowCheck7013 : row7013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7013 := by decide +kernel

theorem rowEval7013 (x : Key → ℝ) : Integer.Sparse.eval row7013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7013, Integer.Sparse.eval_collectBalanced, rawRowCheck7013]

theorem rawRowCheck7014 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form9 = rawRow7014 := by decide +kernel

theorem rowCheck7014 : row7014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7014 := by decide +kernel

theorem rowEval7014 (x : Key → ℝ) : Integer.Sparse.eval row7014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7014, Integer.Sparse.eval_collectBalanced, rawRowCheck7014]

theorem rawRowCheck7015 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form9 = rawRow7015 := by decide +kernel

theorem rowCheck7015 : row7015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7015 := by decide +kernel

theorem rowEval7015 (x : Key → ℝ) : Integer.Sparse.eval row7015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7015, Integer.Sparse.eval_collectBalanced, rawRowCheck7015]

theorem rawRowCheck7016 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form9 = rawRow7016 := by decide +kernel

theorem rowCheck7016 : row7016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7016 := by decide +kernel

theorem rowEval7016 (x : Key → ℝ) : Integer.Sparse.eval row7016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7016, Integer.Sparse.eval_collectBalanced, rawRowCheck7016]

theorem rawRowCheck7017 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form9 = rawRow7017 := by decide +kernel

theorem rowCheck7017 : row7017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7017 := by decide +kernel

theorem rowEval7017 (x : Key → ℝ) : Integer.Sparse.eval row7017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7017, Integer.Sparse.eval_collectBalanced, rawRowCheck7017]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7288 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form9 = rawRow7288 := by decide +kernel

theorem rowCheck7288 : row7288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7288 := by decide +kernel

theorem rowEval7288 (x : Key → ℝ) : Integer.Sparse.eval row7288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7288, Integer.Sparse.eval_collectBalanced, rawRowCheck7288]

theorem rawRowCheck7289 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form9 = rawRow7289 := by decide +kernel

theorem rowCheck7289 : row7289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7289 := by decide +kernel

theorem rowEval7289 (x : Key → ℝ) : Integer.Sparse.eval row7289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7289, Integer.Sparse.eval_collectBalanced, rawRowCheck7289]

theorem rawRowCheck7290 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form9 = rawRow7290 := by decide +kernel

theorem rowCheck7290 : row7290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7290 := by decide +kernel

theorem rowEval7290 (x : Key → ℝ) : Integer.Sparse.eval row7290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7290, Integer.Sparse.eval_collectBalanced, rawRowCheck7290]

theorem rawRowCheck7291 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form9 = rawRow7291 := by decide +kernel

theorem rowCheck7291 : row7291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7291 := by decide +kernel

theorem rowEval7291 (x : Key → ℝ) : Integer.Sparse.eval row7291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7291, Integer.Sparse.eval_collectBalanced, rawRowCheck7291]

theorem rawRowCheck7292 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form9 = rawRow7292 := by decide +kernel

theorem rowCheck7292 : row7292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7292 := by decide +kernel

theorem rowEval7292 (x : Key → ℝ) : Integer.Sparse.eval row7292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7292, Integer.Sparse.eval_collectBalanced, rawRowCheck7292]

theorem rawRowCheck7293 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form9 = rawRow7293 := by decide +kernel

theorem rowCheck7293 : row7293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7293 := by decide +kernel

theorem rowEval7293 (x : Key → ℝ) : Integer.Sparse.eval row7293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7293, Integer.Sparse.eval_collectBalanced, rawRowCheck7293]

theorem rawRowCheck7294 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form9 = rawRow7294 := by decide +kernel

theorem rowCheck7294 : row7294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7294 := by decide +kernel

theorem rowEval7294 (x : Key → ℝ) : Integer.Sparse.eval row7294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7294, Integer.Sparse.eval_collectBalanced, rawRowCheck7294]

theorem rawRowCheck7295 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form9 = rawRow7295 := by decide +kernel

theorem rowCheck7295 : row7295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7295 := by decide +kernel

theorem rowEval7295 (x : Key → ℝ) : Integer.Sparse.eval row7295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7295, Integer.Sparse.eval_collectBalanced, rawRowCheck7295]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7296 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form9 = rawRow7296 := by decide +kernel

theorem rowCheck7296 : row7296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7296 := by decide +kernel

theorem rowEval7296 (x : Key → ℝ) : Integer.Sparse.eval row7296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7296, Integer.Sparse.eval_collectBalanced, rawRowCheck7296]

theorem rawRowCheck7297 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form9 = rawRow7297 := by decide +kernel

theorem rowCheck7297 : row7297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7297 := by decide +kernel

theorem rowEval7297 (x : Key → ℝ) : Integer.Sparse.eval row7297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7297, Integer.Sparse.eval_collectBalanced, rawRowCheck7297]

theorem rawRowCheck7298 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form9 = rawRow7298 := by decide +kernel

theorem rowCheck7298 : row7298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7298 := by decide +kernel

theorem rowEval7298 (x : Key → ℝ) : Integer.Sparse.eval row7298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7298, Integer.Sparse.eval_collectBalanced, rawRowCheck7298]

theorem rawRowCheck7299 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form9 = rawRow7299 := by decide +kernel

theorem rowCheck7299 : row7299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7299 := by decide +kernel

theorem rowEval7299 (x : Key → ℝ) : Integer.Sparse.eval row7299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7299, Integer.Sparse.eval_collectBalanced, rawRowCheck7299]

theorem rawRowCheck7300 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form9 = rawRow7300 := by decide +kernel

theorem rowCheck7300 : row7300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7300 := by decide +kernel

theorem rowEval7300 (x : Key → ℝ) : Integer.Sparse.eval row7300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7300, Integer.Sparse.eval_collectBalanced, rawRowCheck7300]

theorem rawRowCheck7301 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form9 = rawRow7301 := by decide +kernel

theorem rowCheck7301 : row7301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7301 := by decide +kernel

theorem rowEval7301 (x : Key → ℝ) : Integer.Sparse.eval row7301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7301, Integer.Sparse.eval_collectBalanced, rawRowCheck7301]

theorem rawRowCheck7302 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form9 = rawRow7302 := by decide +kernel

theorem rowCheck7302 : row7302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7302 := by decide +kernel

theorem rowEval7302 (x : Key → ℝ) : Integer.Sparse.eval row7302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7302, Integer.Sparse.eval_collectBalanced, rawRowCheck7302]

theorem rawRowCheck7303 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form9 = rawRow7303 := by decide +kernel

theorem rowCheck7303 : row7303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7303 := by decide +kernel

theorem rowEval7303 (x : Key → ℝ) : Integer.Sparse.eval row7303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7303, Integer.Sparse.eval_collectBalanced, rawRowCheck7303]

theorem rawRowCheck7304 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form9 = rawRow7304 := by decide +kernel

theorem rowCheck7304 : row7304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7304 := by decide +kernel

theorem rowEval7304 (x : Key → ℝ) : Integer.Sparse.eval row7304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7304, Integer.Sparse.eval_collectBalanced, rawRowCheck7304]

theorem rawRowCheck7305 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form9 = rawRow7305 := by decide +kernel

theorem rowCheck7305 : row7305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7305 := by decide +kernel

theorem rowEval7305 (x : Key → ℝ) : Integer.Sparse.eval row7305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7305, Integer.Sparse.eval_collectBalanced, rawRowCheck7305]

theorem rawRowCheck7306 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form9 = rawRow7306 := by decide +kernel

theorem rowCheck7306 : row7306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7306 := by decide +kernel

theorem rowEval7306 (x : Key → ℝ) : Integer.Sparse.eval row7306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7306, Integer.Sparse.eval_collectBalanced, rawRowCheck7306]

theorem rawRowCheck7307 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form9 = rawRow7307 := by decide +kernel

theorem rowCheck7307 : row7307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7307 := by decide +kernel

theorem rowEval7307 (x : Key → ℝ) : Integer.Sparse.eval row7307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7307, Integer.Sparse.eval_collectBalanced, rawRowCheck7307]

theorem rawRowCheck7308 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form9 = rawRow7308 := by decide +kernel

theorem rowCheck7308 : row7308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7308 := by decide +kernel

theorem rowEval7308 (x : Key → ℝ) : Integer.Sparse.eval row7308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7308, Integer.Sparse.eval_collectBalanced, rawRowCheck7308]

theorem rawRowCheck7309 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form9 = rawRow7309 := by decide +kernel

theorem rowCheck7309 : row7309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7309 := by decide +kernel

theorem rowEval7309 (x : Key → ℝ) : Integer.Sparse.eval row7309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7309, Integer.Sparse.eval_collectBalanced, rawRowCheck7309]

theorem rawRowCheck7310 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form9 = rawRow7310 := by decide +kernel

theorem rowCheck7310 : row7310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7310 := by decide +kernel

theorem rowEval7310 (x : Key → ℝ) : Integer.Sparse.eval row7310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7310, Integer.Sparse.eval_collectBalanced, rawRowCheck7310]

theorem rawRowCheck7311 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form9 = rawRow7311 := by decide +kernel

theorem rowCheck7311 : row7311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7311 := by decide +kernel

theorem rowEval7311 (x : Key → ℝ) : Integer.Sparse.eval row7311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7311, Integer.Sparse.eval_collectBalanced, rawRowCheck7311]

theorem rawRowCheck7312 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form9 = rawRow7312 := by decide +kernel

theorem rowCheck7312 : row7312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7312 := by decide +kernel

theorem rowEval7312 (x : Key → ℝ) : Integer.Sparse.eval row7312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7312, Integer.Sparse.eval_collectBalanced, rawRowCheck7312]

theorem rawRowCheck7313 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form9 = rawRow7313 := by decide +kernel

theorem rowCheck7313 : row7313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7313 := by decide +kernel

theorem rowEval7313 (x : Key → ℝ) : Integer.Sparse.eval row7313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7313, Integer.Sparse.eval_collectBalanced, rawRowCheck7313]

theorem rawRowCheck7314 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form9 = rawRow7314 := by decide +kernel

theorem rowCheck7314 : row7314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7314 := by decide +kernel

theorem rowEval7314 (x : Key → ℝ) : Integer.Sparse.eval row7314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7314, Integer.Sparse.eval_collectBalanced, rawRowCheck7314]

theorem rawRowCheck7315 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form9 = rawRow7315 := by decide +kernel

theorem rowCheck7315 : row7315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7315 := by decide +kernel

theorem rowEval7315 (x : Key → ℝ) : Integer.Sparse.eval row7315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7315, Integer.Sparse.eval_collectBalanced, rawRowCheck7315]

theorem rawRowCheck7316 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form9 = rawRow7316 := by decide +kernel

theorem rowCheck7316 : row7316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7316 := by decide +kernel

theorem rowEval7316 (x : Key → ℝ) : Integer.Sparse.eval row7316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7316, Integer.Sparse.eval_collectBalanced, rawRowCheck7316]

theorem rawRowCheck7317 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form9 = rawRow7317 := by decide +kernel

theorem rowCheck7317 : row7317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7317 := by decide +kernel

theorem rowEval7317 (x : Key → ℝ) : Integer.Sparse.eval row7317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7317, Integer.Sparse.eval_collectBalanced, rawRowCheck7317]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form9) x := by
  fin_cases k
  · exact rowEval7288 x
  · exact rowEval7289 x
  · exact rowEval7290 x
  · exact rowEval7291 x
  · exact rowEval7292 x
  · exact rowEval7293 x
  · exact rowEval7294 x
  · exact rowEval7295 x
  · exact rowEval7296 x
  · exact rowEval7297 x
  · exact rowEval7298 x
  · exact rowEval7299 x
  · exact rowEval7300 x
  · exact rowEval7301 x
  · exact rowEval7302 x
  · exact rowEval7303 x
  · exact rowEval7304 x
  · exact rowEval7305 x
  · exact rowEval7306 x
  · exact rowEval7307 x
  · exact rowEval7308 x
  · exact rowEval7309 x
  · exact rowEval7310 x
  · exact rowEval7311 x
  · exact rowEval7312 x
  · exact rowEval7313 x
  · exact rowEval7314 x
  · exact rowEval7315 x
  · exact rowEval7316 x
  · exact rowEval7317 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck6808 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow6808 := by decide +kernel

theorem rowCheck6808 : row6808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6808 := by decide +kernel

theorem rowEval6808 (x : Key → ℝ) : Integer.Sparse.eval row6808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6808, Integer.Sparse.eval_collectBalanced, rawRowCheck6808]

theorem rawRowCheck6809 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow6809 := by decide +kernel

theorem rowCheck6809 : row6809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6809 := by decide +kernel

theorem rowEval6809 (x : Key → ℝ) : Integer.Sparse.eval row6809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6809, Integer.Sparse.eval_collectBalanced, rawRowCheck6809]

theorem rawRowCheck6810 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow6810 := by decide +kernel

theorem rowCheck6810 : row6810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6810 := by decide +kernel

theorem rowEval6810 (x : Key → ℝ) : Integer.Sparse.eval row6810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6810, Integer.Sparse.eval_collectBalanced, rawRowCheck6810]

theorem rawRowCheck6811 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form3 = rawRow6811 := by decide +kernel

theorem rowCheck6811 : row6811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6811 := by decide +kernel

theorem rowEval6811 (x : Key → ℝ) : Integer.Sparse.eval row6811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6811, Integer.Sparse.eval_collectBalanced, rawRowCheck6811]

theorem rawRowCheck6812 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form3 = rawRow6812 := by decide +kernel

theorem rowCheck6812 : row6812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6812 := by decide +kernel

theorem rowEval6812 (x : Key → ℝ) : Integer.Sparse.eval row6812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6812, Integer.Sparse.eval_collectBalanced, rawRowCheck6812]

theorem rawRowCheck6813 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form3 = rawRow6813 := by decide +kernel

theorem rowCheck6813 : row6813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6813 := by decide +kernel

theorem rowEval6813 (x : Key → ℝ) : Integer.Sparse.eval row6813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6813, Integer.Sparse.eval_collectBalanced, rawRowCheck6813]

theorem rawRowCheck6814 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form3 = rawRow6814 := by decide +kernel

theorem rowCheck6814 : row6814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6814 := by decide +kernel

theorem rowEval6814 (x : Key → ℝ) : Integer.Sparse.eval row6814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6814, Integer.Sparse.eval_collectBalanced, rawRowCheck6814]

theorem rawRowCheck6815 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form3 = rawRow6815 := by decide +kernel

theorem rowCheck6815 : row6815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6815 := by decide +kernel

theorem rowEval6815 (x : Key → ℝ) : Integer.Sparse.eval row6815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6815, Integer.Sparse.eval_collectBalanced, rawRowCheck6815]

theorem rawRowCheck6816 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form3 = rawRow6816 := by decide +kernel

theorem rowCheck6816 : row6816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6816 := by decide +kernel

theorem rowEval6816 (x : Key → ℝ) : Integer.Sparse.eval row6816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6816, Integer.Sparse.eval_collectBalanced, rawRowCheck6816]

theorem rawRowCheck6817 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form3 = rawRow6817 := by decide +kernel

theorem rowCheck6817 : row6817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6817 := by decide +kernel

theorem rowEval6817 (x : Key → ℝ) : Integer.Sparse.eval row6817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6817, Integer.Sparse.eval_collectBalanced, rawRowCheck6817]

theorem rawRowCheck6818 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form3 = rawRow6818 := by decide +kernel

theorem rowCheck6818 : row6818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6818 := by decide +kernel

theorem rowEval6818 (x : Key → ℝ) : Integer.Sparse.eval row6818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6818, Integer.Sparse.eval_collectBalanced, rawRowCheck6818]

theorem rawRowCheck6819 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form3 = rawRow6819 := by decide +kernel

theorem rowCheck6819 : row6819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6819 := by decide +kernel

theorem rowEval6819 (x : Key → ℝ) : Integer.Sparse.eval row6819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6819, Integer.Sparse.eval_collectBalanced, rawRowCheck6819]

theorem rawRowCheck6820 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form3 = rawRow6820 := by decide +kernel

theorem rowCheck6820 : row6820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6820 := by decide +kernel

theorem rowEval6820 (x : Key → ℝ) : Integer.Sparse.eval row6820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6820, Integer.Sparse.eval_collectBalanced, rawRowCheck6820]

theorem rawRowCheck6821 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form3 = rawRow6821 := by decide +kernel

theorem rowCheck6821 : row6821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6821 := by decide +kernel

theorem rowEval6821 (x : Key → ℝ) : Integer.Sparse.eval row6821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6821, Integer.Sparse.eval_collectBalanced, rawRowCheck6821]

theorem rawRowCheck6822 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form3 = rawRow6822 := by decide +kernel

theorem rowCheck6822 : row6822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6822 := by decide +kernel

theorem rowEval6822 (x : Key → ℝ) : Integer.Sparse.eval row6822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6822, Integer.Sparse.eval_collectBalanced, rawRowCheck6822]

theorem rawRowCheck6823 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form3 = rawRow6823 := by decide +kernel

theorem rowCheck6823 : row6823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6823 := by decide +kernel

theorem rowEval6823 (x : Key → ℝ) : Integer.Sparse.eval row6823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6823, Integer.Sparse.eval_collectBalanced, rawRowCheck6823]

theorem rawRowCheck6824 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form3 = rawRow6824 := by decide +kernel

theorem rowCheck6824 : row6824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6824 := by decide +kernel

theorem rowEval6824 (x : Key → ℝ) : Integer.Sparse.eval row6824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6824, Integer.Sparse.eval_collectBalanced, rawRowCheck6824]

theorem rawRowCheck6825 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form3 = rawRow6825 := by decide +kernel

theorem rowCheck6825 : row6825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6825 := by decide +kernel

theorem rowEval6825 (x : Key → ℝ) : Integer.Sparse.eval row6825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6825, Integer.Sparse.eval_collectBalanced, rawRowCheck6825]

theorem rawRowCheck6826 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form3 = rawRow6826 := by decide +kernel

theorem rowCheck6826 : row6826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6826 := by decide +kernel

theorem rowEval6826 (x : Key → ℝ) : Integer.Sparse.eval row6826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6826, Integer.Sparse.eval_collectBalanced, rawRowCheck6826]

theorem rawRowCheck6827 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form3 = rawRow6827 := by decide +kernel

theorem rowCheck6827 : row6827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6827 := by decide +kernel

theorem rowEval6827 (x : Key → ℝ) : Integer.Sparse.eval row6827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6827, Integer.Sparse.eval_collectBalanced, rawRowCheck6827]

theorem rawRowCheck6828 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form3 = rawRow6828 := by decide +kernel

theorem rowCheck6828 : row6828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6828 := by decide +kernel

theorem rowEval6828 (x : Key → ℝ) : Integer.Sparse.eval row6828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6828, Integer.Sparse.eval_collectBalanced, rawRowCheck6828]

theorem rawRowCheck6829 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form3 = rawRow6829 := by decide +kernel

theorem rowCheck6829 : row6829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6829 := by decide +kernel

theorem rowEval6829 (x : Key → ℝ) : Integer.Sparse.eval row6829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6829, Integer.Sparse.eval_collectBalanced, rawRowCheck6829]

theorem rawRowCheck6830 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form3 = rawRow6830 := by decide +kernel

theorem rowCheck6830 : row6830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6830 := by decide +kernel

theorem rowEval6830 (x : Key → ℝ) : Integer.Sparse.eval row6830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6830, Integer.Sparse.eval_collectBalanced, rawRowCheck6830]

theorem rawRowCheck6831 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form3 = rawRow6831 := by decide +kernel

theorem rowCheck6831 : row6831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6831 := by decide +kernel

theorem rowEval6831 (x : Key → ℝ) : Integer.Sparse.eval row6831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6831, Integer.Sparse.eval_collectBalanced, rawRowCheck6831]

theorem rawRowCheck6832 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form3 = rawRow6832 := by decide +kernel

theorem rowCheck6832 : row6832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6832 := by decide +kernel

theorem rowEval6832 (x : Key → ℝ) : Integer.Sparse.eval row6832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6832, Integer.Sparse.eval_collectBalanced, rawRowCheck6832]

theorem rawRowCheck6833 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form3 = rawRow6833 := by decide +kernel

theorem rowCheck6833 : row6833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6833 := by decide +kernel

theorem rowEval6833 (x : Key → ℝ) : Integer.Sparse.eval row6833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6833, Integer.Sparse.eval_collectBalanced, rawRowCheck6833]

theorem rawRowCheck6834 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form3 = rawRow6834 := by decide +kernel

theorem rowCheck6834 : row6834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6834 := by decide +kernel

theorem rowEval6834 (x : Key → ℝ) : Integer.Sparse.eval row6834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6834, Integer.Sparse.eval_collectBalanced, rawRowCheck6834]

theorem rawRowCheck6835 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form3 = rawRow6835 := by decide +kernel

theorem rowCheck6835 : row6835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6835 := by decide +kernel

theorem rowEval6835 (x : Key → ℝ) : Integer.Sparse.eval row6835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6835, Integer.Sparse.eval_collectBalanced, rawRowCheck6835]

theorem rawRowCheck6836 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form3 = rawRow6836 := by decide +kernel

theorem rowCheck6836 : row6836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6836 := by decide +kernel

theorem rowEval6836 (x : Key → ℝ) : Integer.Sparse.eval row6836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6836, Integer.Sparse.eval_collectBalanced, rawRowCheck6836]

theorem rawRowCheck6837 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form3 = rawRow6837 := by decide +kernel

theorem rowCheck6837 : row6837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6837 := by decide +kernel

theorem rowEval6837 (x : Key → ℝ) : Integer.Sparse.eval row6837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6837, Integer.Sparse.eval_collectBalanced, rawRowCheck6837]

theorem rawRowCheck6838 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow6838 := by decide +kernel

theorem rowCheck6838 : row6838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6838 := by decide +kernel

theorem rowEval6838 (x : Key → ℝ) : Integer.Sparse.eval row6838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6838, Integer.Sparse.eval_collectBalanced, rawRowCheck6838]

theorem rawRowCheck6839 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow6839 := by decide +kernel

theorem rowCheck6839 : row6839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6839 := by decide +kernel

theorem rowEval6839 (x : Key → ℝ) : Integer.Sparse.eval row6839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6839, Integer.Sparse.eval_collectBalanced, rawRowCheck6839]

theorem rawRowCheck6840 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow6840 := by decide +kernel

theorem rowCheck6840 : row6840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6840 := by decide +kernel

theorem rowEval6840 (x : Key → ℝ) : Integer.Sparse.eval row6840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6840, Integer.Sparse.eval_collectBalanced, rawRowCheck6840]

theorem rawRowCheck6841 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form4 = rawRow6841 := by decide +kernel

theorem rowCheck6841 : row6841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6841 := by decide +kernel

theorem rowEval6841 (x : Key → ℝ) : Integer.Sparse.eval row6841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6841, Integer.Sparse.eval_collectBalanced, rawRowCheck6841]

theorem rawRowCheck6842 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form4 = rawRow6842 := by decide +kernel

theorem rowCheck6842 : row6842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6842 := by decide +kernel

theorem rowEval6842 (x : Key → ℝ) : Integer.Sparse.eval row6842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6842, Integer.Sparse.eval_collectBalanced, rawRowCheck6842]

theorem rawRowCheck6843 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6843 := by decide +kernel

theorem rowCheck6843 : row6843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6843 := by decide +kernel

theorem rowEval6843 (x : Key → ℝ) : Integer.Sparse.eval row6843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6843, Integer.Sparse.eval_collectBalanced, rawRowCheck6843]

theorem rawRowCheck6844 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6844 := by decide +kernel

theorem rowCheck6844 : row6844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6844 := by decide +kernel

theorem rowEval6844 (x : Key → ℝ) : Integer.Sparse.eval row6844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6844, Integer.Sparse.eval_collectBalanced, rawRowCheck6844]

theorem rawRowCheck6845 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6845 := by decide +kernel

theorem rowCheck6845 : row6845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6845 := by decide +kernel

theorem rowEval6845 (x : Key → ℝ) : Integer.Sparse.eval row6845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6845, Integer.Sparse.eval_collectBalanced, rawRowCheck6845]

theorem rawRowCheck6846 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6846 := by decide +kernel

theorem rowCheck6846 : row6846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6846 := by decide +kernel

theorem rowEval6846 (x : Key → ℝ) : Integer.Sparse.eval row6846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6846, Integer.Sparse.eval_collectBalanced, rawRowCheck6846]

theorem rawRowCheck6847 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow6847 := by decide +kernel

theorem rowCheck6847 : row6847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6847 := by decide +kernel

theorem rowEval6847 (x : Key → ℝ) : Integer.Sparse.eval row6847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6847, Integer.Sparse.eval_collectBalanced, rawRowCheck6847]

theorem rawRowCheck6848 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow6848 := by decide +kernel

theorem rowCheck6848 : row6848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6848 := by decide +kernel

theorem rowEval6848 (x : Key → ℝ) : Integer.Sparse.eval row6848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6848, Integer.Sparse.eval_collectBalanced, rawRowCheck6848]

theorem rawRowCheck6849 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow6849 := by decide +kernel

theorem rowCheck6849 : row6849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6849 := by decide +kernel

theorem rowEval6849 (x : Key → ℝ) : Integer.Sparse.eval row6849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6849, Integer.Sparse.eval_collectBalanced, rawRowCheck6849]

theorem rawRowCheck6850 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form4 = rawRow6850 := by decide +kernel

theorem rowCheck6850 : row6850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6850 := by decide +kernel

theorem rowEval6850 (x : Key → ℝ) : Integer.Sparse.eval row6850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6850, Integer.Sparse.eval_collectBalanced, rawRowCheck6850]

theorem rawRowCheck6851 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form4 = rawRow6851 := by decide +kernel

theorem rowCheck6851 : row6851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6851 := by decide +kernel

theorem rowEval6851 (x : Key → ℝ) : Integer.Sparse.eval row6851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6851, Integer.Sparse.eval_collectBalanced, rawRowCheck6851]

theorem rawRowCheck6852 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6852 := by decide +kernel

theorem rowCheck6852 : row6852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6852 := by decide +kernel

theorem rowEval6852 (x : Key → ℝ) : Integer.Sparse.eval row6852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6852, Integer.Sparse.eval_collectBalanced, rawRowCheck6852]

theorem rawRowCheck6853 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6853 := by decide +kernel

theorem rowCheck6853 : row6853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6853 := by decide +kernel

theorem rowEval6853 (x : Key → ℝ) : Integer.Sparse.eval row6853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6853, Integer.Sparse.eval_collectBalanced, rawRowCheck6853]

theorem rawRowCheck6854 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6854 := by decide +kernel

theorem rowCheck6854 : row6854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6854 := by decide +kernel

theorem rowEval6854 (x : Key → ℝ) : Integer.Sparse.eval row6854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6854, Integer.Sparse.eval_collectBalanced, rawRowCheck6854]

theorem rawRowCheck6855 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6855 := by decide +kernel

theorem rowCheck6855 : row6855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6855 := by decide +kernel

theorem rowEval6855 (x : Key → ℝ) : Integer.Sparse.eval row6855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6855, Integer.Sparse.eval_collectBalanced, rawRowCheck6855]

theorem rawRowCheck6856 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form4 = rawRow6856 := by decide +kernel

theorem rowCheck6856 : row6856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6856 := by decide +kernel

theorem rowEval6856 (x : Key → ℝ) : Integer.Sparse.eval row6856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6856, Integer.Sparse.eval_collectBalanced, rawRowCheck6856]

theorem rawRowCheck6857 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form4 = rawRow6857 := by decide +kernel

theorem rowCheck6857 : row6857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6857 := by decide +kernel

theorem rowEval6857 (x : Key → ℝ) : Integer.Sparse.eval row6857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6857, Integer.Sparse.eval_collectBalanced, rawRowCheck6857]

theorem rawRowCheck6858 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form4 = rawRow6858 := by decide +kernel

theorem rowCheck6858 : row6858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6858 := by decide +kernel

theorem rowEval6858 (x : Key → ℝ) : Integer.Sparse.eval row6858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6858, Integer.Sparse.eval_collectBalanced, rawRowCheck6858]

theorem rawRowCheck6859 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form4 = rawRow6859 := by decide +kernel

theorem rowCheck6859 : row6859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6859 := by decide +kernel

theorem rowEval6859 (x : Key → ℝ) : Integer.Sparse.eval row6859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6859, Integer.Sparse.eval_collectBalanced, rawRowCheck6859]

theorem rawRowCheck6860 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form4 = rawRow6860 := by decide +kernel

theorem rowCheck6860 : row6860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6860 := by decide +kernel

theorem rowEval6860 (x : Key → ℝ) : Integer.Sparse.eval row6860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6860, Integer.Sparse.eval_collectBalanced, rawRowCheck6860]

theorem rawRowCheck6861 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form4 = rawRow6861 := by decide +kernel

theorem rowCheck6861 : row6861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6861 := by decide +kernel

theorem rowEval6861 (x : Key → ℝ) : Integer.Sparse.eval row6861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6861, Integer.Sparse.eval_collectBalanced, rawRowCheck6861]

theorem rawRowCheck6862 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow6862 := by decide +kernel

theorem rowCheck6862 : row6862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6862 := by decide +kernel

theorem rowEval6862 (x : Key → ℝ) : Integer.Sparse.eval row6862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6862, Integer.Sparse.eval_collectBalanced, rawRowCheck6862]

theorem rawRowCheck6863 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow6863 := by decide +kernel

theorem rowCheck6863 : row6863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6863 := by decide +kernel

theorem rowEval6863 (x : Key → ℝ) : Integer.Sparse.eval row6863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6863, Integer.Sparse.eval_collectBalanced, rawRowCheck6863]

theorem rawRowCheck6864 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow6864 := by decide +kernel

theorem rowCheck6864 : row6864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6864 := by decide +kernel

theorem rowEval6864 (x : Key → ℝ) : Integer.Sparse.eval row6864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6864, Integer.Sparse.eval_collectBalanced, rawRowCheck6864]

theorem rawRowCheck6865 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form4 = rawRow6865 := by decide +kernel

theorem rowCheck6865 : row6865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6865 := by decide +kernel

theorem rowEval6865 (x : Key → ℝ) : Integer.Sparse.eval row6865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6865, Integer.Sparse.eval_collectBalanced, rawRowCheck6865]

theorem rawRowCheck6866 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form4 = rawRow6866 := by decide +kernel

theorem rowCheck6866 : row6866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6866 := by decide +kernel

theorem rowEval6866 (x : Key → ℝ) : Integer.Sparse.eval row6866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6866, Integer.Sparse.eval_collectBalanced, rawRowCheck6866]

theorem rawRowCheck6867 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form4 = rawRow6867 := by decide +kernel

theorem rowCheck6867 : row6867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6867 := by decide +kernel

theorem rowEval6867 (x : Key → ℝ) : Integer.Sparse.eval row6867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6867, Integer.Sparse.eval_collectBalanced, rawRowCheck6867]

theorem rawRowCheck6898 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form6 = rawRow6898 := by decide +kernel

theorem rowCheck6898 : row6898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6898 := by decide +kernel

theorem rowEval6898 (x : Key → ℝ) : Integer.Sparse.eval row6898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6898, Integer.Sparse.eval_collectBalanced, rawRowCheck6898]

theorem rawRowCheck6899 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form6 = rawRow6899 := by decide +kernel

theorem rowCheck6899 : row6899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6899 := by decide +kernel

theorem rowEval6899 (x : Key → ℝ) : Integer.Sparse.eval row6899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6899, Integer.Sparse.eval_collectBalanced, rawRowCheck6899]

theorem rawRowCheck6900 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form6 = rawRow6900 := by decide +kernel

theorem rowCheck6900 : row6900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6900 := by decide +kernel

theorem rowEval6900 (x : Key → ℝ) : Integer.Sparse.eval row6900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6900, Integer.Sparse.eval_collectBalanced, rawRowCheck6900]

theorem rawRowCheck6901 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6901 := by decide +kernel

theorem rowCheck6901 : row6901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6901 := by decide +kernel

theorem rowEval6901 (x : Key → ℝ) : Integer.Sparse.eval row6901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6901, Integer.Sparse.eval_collectBalanced, rawRowCheck6901]

theorem rawRowCheck6902 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6902 := by decide +kernel

theorem rowCheck6902 : row6902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6902 := by decide +kernel

theorem rowEval6902 (x : Key → ℝ) : Integer.Sparse.eval row6902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6902, Integer.Sparse.eval_collectBalanced, rawRowCheck6902]

theorem rawRowCheck6903 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form6 = rawRow6903 := by decide +kernel

theorem rowCheck6903 : row6903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6903 := by decide +kernel

theorem rowEval6903 (x : Key → ℝ) : Integer.Sparse.eval row6903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6903, Integer.Sparse.eval_collectBalanced, rawRowCheck6903]

theorem rawRowCheck6904 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form6 = rawRow6904 := by decide +kernel

theorem rowCheck6904 : row6904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6904 := by decide +kernel

theorem rowEval6904 (x : Key → ℝ) : Integer.Sparse.eval row6904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6904, Integer.Sparse.eval_collectBalanced, rawRowCheck6904]

theorem rawRowCheck6905 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6905 := by decide +kernel

theorem rowCheck6905 : row6905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6905 := by decide +kernel

theorem rowEval6905 (x : Key → ℝ) : Integer.Sparse.eval row6905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6905, Integer.Sparse.eval_collectBalanced, rawRowCheck6905]

theorem rawRowCheck6906 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6906 := by decide +kernel

theorem rowCheck6906 : row6906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6906 := by decide +kernel

theorem rowEval6906 (x : Key → ℝ) : Integer.Sparse.eval row6906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6906, Integer.Sparse.eval_collectBalanced, rawRowCheck6906]

theorem rawRowCheck6907 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form6 = rawRow6907 := by decide +kernel

theorem rowCheck6907 : row6907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6907 := by decide +kernel

theorem rowEval6907 (x : Key → ℝ) : Integer.Sparse.eval row6907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6907, Integer.Sparse.eval_collectBalanced, rawRowCheck6907]

theorem rawRowCheck6908 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form6 = rawRow6908 := by decide +kernel

theorem rowCheck6908 : row6908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6908 := by decide +kernel

theorem rowEval6908 (x : Key → ℝ) : Integer.Sparse.eval row6908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6908, Integer.Sparse.eval_collectBalanced, rawRowCheck6908]

theorem rawRowCheck6909 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form6 = rawRow6909 := by decide +kernel

theorem rowCheck6909 : row6909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6909 := by decide +kernel

theorem rowEval6909 (x : Key → ℝ) : Integer.Sparse.eval row6909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6909, Integer.Sparse.eval_collectBalanced, rawRowCheck6909]

theorem rawRowCheck6910 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6910 := by decide +kernel

theorem rowCheck6910 : row6910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6910 := by decide +kernel

theorem rowEval6910 (x : Key → ℝ) : Integer.Sparse.eval row6910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6910, Integer.Sparse.eval_collectBalanced, rawRowCheck6910]

theorem rawRowCheck6911 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6911 := by decide +kernel

theorem rowCheck6911 : row6911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6911 := by decide +kernel

theorem rowEval6911 (x : Key → ℝ) : Integer.Sparse.eval row6911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6911, Integer.Sparse.eval_collectBalanced, rawRowCheck6911]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval6808 x
  · exact rowEval6809 x
  · exact rowEval6810 x
  · exact rowEval6811 x
  · exact rowEval6812 x
  · exact rowEval6813 x
  · exact rowEval6814 x
  · exact rowEval6815 x
  · exact rowEval6816 x
  · exact rowEval6817 x
  · exact rowEval6818 x
  · exact rowEval6819 x
  · exact rowEval6820 x
  · exact rowEval6821 x
  · exact rowEval6822 x
  · exact rowEval6823 x
  · exact rowEval6824 x
  · exact rowEval6825 x
  · exact rowEval6826 x
  · exact rowEval6827 x
  · exact rowEval6828 x
  · exact rowEval6829 x
  · exact rowEval6830 x
  · exact rowEval6831 x
  · exact rowEval6832 x
  · exact rowEval6833 x
  · exact rowEval6834 x
  · exact rowEval6835 x
  · exact rowEval6836 x
  · exact rowEval6837 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval6838 x
  · exact rowEval6839 x
  · exact rowEval6840 x
  · exact rowEval6841 x
  · exact rowEval6842 x
  · exact rowEval6843 x
  · exact rowEval6844 x
  · exact rowEval6845 x
  · exact rowEval6846 x
  · exact rowEval6847 x
  · exact rowEval6848 x
  · exact rowEval6849 x
  · exact rowEval6850 x
  · exact rowEval6851 x
  · exact rowEval6852 x
  · exact rowEval6853 x
  · exact rowEval6854 x
  · exact rowEval6855 x
  · exact rowEval6856 x
  · exact rowEval6857 x
  · exact rowEval6858 x
  · exact rowEval6859 x
  · exact rowEval6860 x
  · exact rowEval6861 x
  · exact rowEval6862 x
  · exact rowEval6863 x
  · exact rowEval6864 x
  · exact rowEval6865 x
  · exact rowEval6866 x
  · exact rowEval6867 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form6) x := by
  fin_cases k
  · exact rowEval6898 x
  · exact rowEval6899 x
  · exact rowEval6900 x
  · exact rowEval6901 x
  · exact rowEval6902 x
  · exact rowEval6903 x
  · exact rowEval6904 x
  · exact rowEval6905 x
  · exact rowEval6906 x
  · exact rowEval6907 x
  · exact rowEval6908 x
  · exact rowEval6909 x
  · exact rowEval6910 x
  · exact rowEval6911 x
  · exact rowEval6912 x
  · exact rowEval6913 x
  · exact rowEval6914 x
  · exact rowEval6915 x
  · exact rowEval6916 x
  · exact rowEval6917 x
  · exact rowEval6918 x
  · exact rowEval6919 x
  · exact rowEval6920 x
  · exact rowEval6921 x
  · exact rowEval6922 x
  · exact rowEval6923 x
  · exact rowEval6924 x
  · exact rowEval6925 x
  · exact rowEval6926 x
  · exact rowEval6927 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

theorem entryCheck9_9 : entry9_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_9 k)) := by decide +kernel

theorem rowsSound9_9 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form9) x := by
  fin_cases k
  · exact rowEval6988 x
  · exact rowEval6989 x
  · exact rowEval6990 x
  · exact rowEval6991 x
  · exact rowEval6992 x
  · exact rowEval6993 x
  · exact rowEval6994 x
  · exact rowEval6995 x
  · exact rowEval6996 x
  · exact rowEval6997 x
  · exact rowEval6998 x
  · exact rowEval6999 x
  · exact rowEval7000 x
  · exact rowEval7001 x
  · exact rowEval7002 x
  · exact rowEval7003 x
  · exact rowEval7004 x
  · exact rowEval7005 x
  · exact rowEval7006 x
  · exact rowEval7007 x
  · exact rowEval7008 x
  · exact rowEval7009 x
  · exact rowEval7010 x
  · exact rowEval7011 x
  · exact rowEval7012 x
  · exact rowEval7013 x
  · exact rowEval7014 x
  · exact rowEval7015 x
  · exact rowEval7016 x
  · exact rowEval7017 x

theorem entryEval9_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_9 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form9 B := by
  rw [entryCheck9_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_9]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

theorem entryEvalRow9_e_oai (j : Fin 11) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 9 j) (GramNormalization.eval B) =
      (GramFunctions.Block2.forms 9).mixedGram (GramFunctions.Block2.forms j) B := by
  fin_cases j
  · exact entryEval9_0_e B hB
  · exact entryEval9_1_e B hB
  · exact entryEval9_2_e B hB
  · exact entryEval9_3 B hB
  · exact entryEval9_4 B hB
  · exact entryEval9_5_e B hB
  · exact entryEval9_6 B hB
  · exact entryEval9_7_e B hB
  · exact entryEval9_8_e B hB
  · exact entryEval9_9 B hB
  · exact (entryEval10_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow9_e_oai := @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow9_e_oai
