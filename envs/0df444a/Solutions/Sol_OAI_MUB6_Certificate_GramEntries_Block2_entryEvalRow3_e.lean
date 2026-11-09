-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:52:19.94819+00:00
-- url     : https://prove2.me/submissions/ecde1afb-ac34-4b6d-9f33-d1485c71ec50

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E053
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval3_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval3_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval5_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval6_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval7_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_3_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7108 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form3 = rawRow7108 := by decide +kernel

theorem rowCheck7108 : row7108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7108 := by decide +kernel

theorem rowEval7108 (x : Key → ℝ) : Integer.Sparse.eval row7108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7108, Integer.Sparse.eval_collectBalanced, rawRowCheck7108]

theorem rawRowCheck7109 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form3 = rawRow7109 := by decide +kernel

theorem rowCheck7109 : row7109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7109 := by decide +kernel

theorem rowEval7109 (x : Key → ℝ) : Integer.Sparse.eval row7109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7109, Integer.Sparse.eval_collectBalanced, rawRowCheck7109]

theorem rawRowCheck7110 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form3 = rawRow7110 := by decide +kernel

theorem rowCheck7110 : row7110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7110 := by decide +kernel

theorem rowEval7110 (x : Key → ℝ) : Integer.Sparse.eval row7110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7110, Integer.Sparse.eval_collectBalanced, rawRowCheck7110]

theorem rawRowCheck7111 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow7111 := by decide +kernel

theorem rowCheck7111 : row7111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7111 := by decide +kernel

theorem rowEval7111 (x : Key → ℝ) : Integer.Sparse.eval row7111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7111, Integer.Sparse.eval_collectBalanced, rawRowCheck7111]

theorem rawRowCheck7112 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow7112 := by decide +kernel

theorem rowCheck7112 : row7112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7112 := by decide +kernel

theorem rowEval7112 (x : Key → ℝ) : Integer.Sparse.eval row7112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7112, Integer.Sparse.eval_collectBalanced, rawRowCheck7112]

theorem rawRowCheck7113 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow7113 := by decide +kernel

theorem rowCheck7113 : row7113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7113 := by decide +kernel

theorem rowEval7113 (x : Key → ℝ) : Integer.Sparse.eval row7113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7113, Integer.Sparse.eval_collectBalanced, rawRowCheck7113]

theorem rawRowCheck7114 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form3 = rawRow7114 := by decide +kernel

theorem rowCheck7114 : row7114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7114 := by decide +kernel

theorem rowEval7114 (x : Key → ℝ) : Integer.Sparse.eval row7114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7114, Integer.Sparse.eval_collectBalanced, rawRowCheck7114]

theorem rawRowCheck7115 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form3 = rawRow7115 := by decide +kernel

theorem rowCheck7115 : row7115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7115 := by decide +kernel

theorem rowEval7115 (x : Key → ℝ) : Integer.Sparse.eval row7115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7115, Integer.Sparse.eval_collectBalanced, rawRowCheck7115]

theorem rawRowCheck7116 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form3 = rawRow7116 := by decide +kernel

theorem rowCheck7116 : row7116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7116 := by decide +kernel

theorem rowEval7116 (x : Key → ℝ) : Integer.Sparse.eval row7116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7116, Integer.Sparse.eval_collectBalanced, rawRowCheck7116]

theorem rawRowCheck7117 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form3 = rawRow7117 := by decide +kernel

theorem rowCheck7117 : row7117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7117 := by decide +kernel

theorem rowEval7117 (x : Key → ℝ) : Integer.Sparse.eval row7117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7117, Integer.Sparse.eval_collectBalanced, rawRowCheck7117]

theorem rawRowCheck7118 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form3 = rawRow7118 := by decide +kernel

theorem rowCheck7118 : row7118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7118 := by decide +kernel

theorem rowEval7118 (x : Key → ℝ) : Integer.Sparse.eval row7118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7118, Integer.Sparse.eval_collectBalanced, rawRowCheck7118]

theorem rawRowCheck7119 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form3 = rawRow7119 := by decide +kernel

theorem rowCheck7119 : row7119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7119 := by decide +kernel

theorem rowEval7119 (x : Key → ℝ) : Integer.Sparse.eval row7119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7119, Integer.Sparse.eval_collectBalanced, rawRowCheck7119]

theorem rawRowCheck7120 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form3 = rawRow7120 := by decide +kernel

theorem rowCheck7120 : row7120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7120 := by decide +kernel

theorem rowEval7120 (x : Key → ℝ) : Integer.Sparse.eval row7120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7120, Integer.Sparse.eval_collectBalanced, rawRowCheck7120]

theorem rawRowCheck7121 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form3 = rawRow7121 := by decide +kernel

theorem rowCheck7121 : row7121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7121 := by decide +kernel

theorem rowEval7121 (x : Key → ℝ) : Integer.Sparse.eval row7121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7121, Integer.Sparse.eval_collectBalanced, rawRowCheck7121]

theorem rawRowCheck7122 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form3 = rawRow7122 := by decide +kernel

theorem rowCheck7122 : row7122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7122 := by decide +kernel

theorem rowEval7122 (x : Key → ℝ) : Integer.Sparse.eval row7122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7122, Integer.Sparse.eval_collectBalanced, rawRowCheck7122]

theorem rawRowCheck7123 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form3 = rawRow7123 := by decide +kernel

theorem rowCheck7123 : row7123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7123 := by decide +kernel

theorem rowEval7123 (x : Key → ℝ) : Integer.Sparse.eval row7123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7123, Integer.Sparse.eval_collectBalanced, rawRowCheck7123]

theorem rawRowCheck7124 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form3 = rawRow7124 := by decide +kernel

theorem rowCheck7124 : row7124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7124 := by decide +kernel

theorem rowEval7124 (x : Key → ℝ) : Integer.Sparse.eval row7124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7124, Integer.Sparse.eval_collectBalanced, rawRowCheck7124]

theorem rawRowCheck7125 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form3 = rawRow7125 := by decide +kernel

theorem rowCheck7125 : row7125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7125 := by decide +kernel

theorem rowEval7125 (x : Key → ℝ) : Integer.Sparse.eval row7125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7125, Integer.Sparse.eval_collectBalanced, rawRowCheck7125]

theorem rawRowCheck7126 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow7126 := by decide +kernel

theorem rowCheck7126 : row7126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7126 := by decide +kernel

theorem rowEval7126 (x : Key → ℝ) : Integer.Sparse.eval row7126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7126, Integer.Sparse.eval_collectBalanced, rawRowCheck7126]

theorem rawRowCheck7127 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow7127 := by decide +kernel

theorem rowCheck7127 : row7127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7127 := by decide +kernel

theorem rowEval7127 (x : Key → ℝ) : Integer.Sparse.eval row7127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7127, Integer.Sparse.eval_collectBalanced, rawRowCheck7127]

theorem rawRowCheck7128 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow7128 := by decide +kernel

theorem rowCheck7128 : row7128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7128 := by decide +kernel

theorem rowEval7128 (x : Key → ℝ) : Integer.Sparse.eval row7128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7128, Integer.Sparse.eval_collectBalanced, rawRowCheck7128]

theorem rawRowCheck7129 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form3 = rawRow7129 := by decide +kernel

theorem rowCheck7129 : row7129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7129 := by decide +kernel

theorem rowEval7129 (x : Key → ℝ) : Integer.Sparse.eval row7129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7129, Integer.Sparse.eval_collectBalanced, rawRowCheck7129]

theorem rawRowCheck7130 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form3 = rawRow7130 := by decide +kernel

theorem rowCheck7130 : row7130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7130 := by decide +kernel

theorem rowEval7130 (x : Key → ℝ) : Integer.Sparse.eval row7130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7130, Integer.Sparse.eval_collectBalanced, rawRowCheck7130]

theorem rawRowCheck7131 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form3 = rawRow7131 := by decide +kernel

theorem rowCheck7131 : row7131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7131 := by decide +kernel

theorem rowEval7131 (x : Key → ℝ) : Integer.Sparse.eval row7131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7131, Integer.Sparse.eval_collectBalanced, rawRowCheck7131]

theorem rawRowCheck7132 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form3 = rawRow7132 := by decide +kernel

theorem rowCheck7132 : row7132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7132 := by decide +kernel

theorem rowEval7132 (x : Key → ℝ) : Integer.Sparse.eval row7132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7132, Integer.Sparse.eval_collectBalanced, rawRowCheck7132]

theorem rawRowCheck7133 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form3 = rawRow7133 := by decide +kernel

theorem rowCheck7133 : row7133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7133 := by decide +kernel

theorem rowEval7133 (x : Key → ℝ) : Integer.Sparse.eval row7133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7133, Integer.Sparse.eval_collectBalanced, rawRowCheck7133]

theorem rawRowCheck7134 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form3 = rawRow7134 := by decide +kernel

theorem rowCheck7134 : row7134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7134 := by decide +kernel

theorem rowEval7134 (x : Key → ℝ) : Integer.Sparse.eval row7134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7134, Integer.Sparse.eval_collectBalanced, rawRowCheck7134]

theorem rawRowCheck7135 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form3 = rawRow7135 := by decide +kernel

theorem rowCheck7135 : row7135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7135 := by decide +kernel

theorem rowEval7135 (x : Key → ℝ) : Integer.Sparse.eval row7135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7135, Integer.Sparse.eval_collectBalanced, rawRowCheck7135]

theorem rawRowCheck7136 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form3 = rawRow7136 := by decide +kernel

theorem rowCheck7136 : row7136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7136 := by decide +kernel

theorem rowEval7136 (x : Key → ℝ) : Integer.Sparse.eval row7136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7136, Integer.Sparse.eval_collectBalanced, rawRowCheck7136]

theorem rawRowCheck7137 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form3 = rawRow7137 := by decide +kernel

theorem rowCheck7137 : row7137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7137 := by decide +kernel

theorem rowEval7137 (x : Key → ℝ) : Integer.Sparse.eval row7137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7137, Integer.Sparse.eval_collectBalanced, rawRowCheck7137]

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

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval7108 x
  · exact rowEval7109 x
  · exact rowEval7110 x
  · exact rowEval7111 x
  · exact rowEval7112 x
  · exact rowEval7113 x
  · exact rowEval7114 x
  · exact rowEval7115 x
  · exact rowEval7116 x
  · exact rowEval7117 x
  · exact rowEval7118 x
  · exact rowEval7119 x
  · exact rowEval7120 x
  · exact rowEval7121 x
  · exact rowEval7122 x
  · exact rowEval7123 x
  · exact rowEval7124 x
  · exact rowEval7125 x
  · exact rowEval7126 x
  · exact rowEval7127 x
  · exact rowEval7128 x
  · exact rowEval7129 x
  · exact rowEval7130 x
  · exact rowEval7131 x
  · exact rowEval7132 x
  · exact rowEval7133 x
  · exact rowEval7134 x
  · exact rowEval7135 x
  · exact rowEval7136 x
  · exact rowEval7137 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck5418 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5418 := by decide +kernel

theorem rowCheck5418 : row5418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5418 := by decide +kernel

theorem rowEval5418 (x : Key → ℝ) : Integer.Sparse.eval row5418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5418, Integer.Sparse.eval_collectBalanced, rawRowCheck5418]

theorem rawRowCheck5419 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5419 := by decide +kernel

theorem rowCheck5419 : row5419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5419 := by decide +kernel

theorem rowEval5419 (x : Key → ℝ) : Integer.Sparse.eval row5419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5419, Integer.Sparse.eval_collectBalanced, rawRowCheck5419]

theorem rawRowCheck5420 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5420 := by decide +kernel

theorem rowCheck5420 : row5420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5420 := by decide +kernel

theorem rowEval5420 (x : Key → ℝ) : Integer.Sparse.eval row5420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5420, Integer.Sparse.eval_collectBalanced, rawRowCheck5420]

theorem rawRowCheck5421 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5421 := by decide +kernel

theorem rowCheck5421 : row5421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5421 := by decide +kernel

theorem rowEval5421 (x : Key → ℝ) : Integer.Sparse.eval row5421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5421, Integer.Sparse.eval_collectBalanced, rawRowCheck5421]

theorem rawRowCheck5422 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5422 := by decide +kernel

theorem rowCheck5422 : row5422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5422 := by decide +kernel

theorem rowEval5422 (x : Key → ℝ) : Integer.Sparse.eval row5422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5422, Integer.Sparse.eval_collectBalanced, rawRowCheck5422]

theorem rawRowCheck5423 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5423 := by decide +kernel

theorem rowCheck5423 : row5423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5423 := by decide +kernel

theorem rowEval5423 (x : Key → ℝ) : Integer.Sparse.eval row5423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5423, Integer.Sparse.eval_collectBalanced, rawRowCheck5423]

theorem rawRowCheck5424 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5424 := by decide +kernel

theorem rowCheck5424 : row5424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5424 := by decide +kernel

theorem rowEval5424 (x : Key → ℝ) : Integer.Sparse.eval row5424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5424, Integer.Sparse.eval_collectBalanced, rawRowCheck5424]

theorem rawRowCheck5425 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5425 := by decide +kernel

theorem rowCheck5425 : row5425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5425 := by decide +kernel

theorem rowEval5425 (x : Key → ℝ) : Integer.Sparse.eval row5425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5425, Integer.Sparse.eval_collectBalanced, rawRowCheck5425]

theorem rawRowCheck5426 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5426 := by decide +kernel

theorem rowCheck5426 : row5426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5426 := by decide +kernel

theorem rowEval5426 (x : Key → ℝ) : Integer.Sparse.eval row5426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5426, Integer.Sparse.eval_collectBalanced, rawRowCheck5426]

theorem rawRowCheck5427 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1 = rawRow5427 := by decide +kernel

theorem rowCheck5427 : row5427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5427 := by decide +kernel

theorem rowEval5427 (x : Key → ℝ) : Integer.Sparse.eval row5427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5427, Integer.Sparse.eval_collectBalanced, rawRowCheck5427]

theorem rawRowCheck5428 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1 = rawRow5428 := by decide +kernel

theorem rowCheck5428 : row5428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5428 := by decide +kernel

theorem rowEval5428 (x : Key → ℝ) : Integer.Sparse.eval row5428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5428, Integer.Sparse.eval_collectBalanced, rawRowCheck5428]

theorem rawRowCheck5429 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1 = rawRow5429 := by decide +kernel

theorem rowCheck5429 : row5429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5429 := by decide +kernel

theorem rowEval5429 (x : Key → ℝ) : Integer.Sparse.eval row5429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5429, Integer.Sparse.eval_collectBalanced, rawRowCheck5429]

theorem rawRowCheck5430 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5430 := by decide +kernel

theorem rowCheck5430 : row5430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5430 := by decide +kernel

theorem rowEval5430 (x : Key → ℝ) : Integer.Sparse.eval row5430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5430, Integer.Sparse.eval_collectBalanced, rawRowCheck5430]

theorem rawRowCheck5431 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5431 := by decide +kernel

theorem rowCheck5431 : row5431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5431 := by decide +kernel

theorem rowEval5431 (x : Key → ℝ) : Integer.Sparse.eval row5431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5431, Integer.Sparse.eval_collectBalanced, rawRowCheck5431]

theorem rawRowCheck5432 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5432 := by decide +kernel

theorem rowCheck5432 : row5432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5432 := by decide +kernel

theorem rowEval5432 (x : Key → ℝ) : Integer.Sparse.eval row5432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5432, Integer.Sparse.eval_collectBalanced, rawRowCheck5432]

theorem rawRowCheck5433 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5433 := by decide +kernel

theorem rowCheck5433 : row5433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5433 := by decide +kernel

theorem rowEval5433 (x : Key → ℝ) : Integer.Sparse.eval row5433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5433, Integer.Sparse.eval_collectBalanced, rawRowCheck5433]

theorem rawRowCheck5434 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5434 := by decide +kernel

theorem rowCheck5434 : row5434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5434 := by decide +kernel

theorem rowEval5434 (x : Key → ℝ) : Integer.Sparse.eval row5434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5434, Integer.Sparse.eval_collectBalanced, rawRowCheck5434]

theorem rawRowCheck5435 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5435 := by decide +kernel

theorem rowCheck5435 : row5435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5435 := by decide +kernel

theorem rowEval5435 (x : Key → ℝ) : Integer.Sparse.eval row5435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5435, Integer.Sparse.eval_collectBalanced, rawRowCheck5435]

theorem rawRowCheck5436 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5436 := by decide +kernel

theorem rowCheck5436 : row5436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5436 := by decide +kernel

theorem rowEval5436 (x : Key → ℝ) : Integer.Sparse.eval row5436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5436, Integer.Sparse.eval_collectBalanced, rawRowCheck5436]

theorem rawRowCheck5437 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5437 := by decide +kernel

theorem rowCheck5437 : row5437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5437 := by decide +kernel

theorem rowEval5437 (x : Key → ℝ) : Integer.Sparse.eval row5437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5437, Integer.Sparse.eval_collectBalanced, rawRowCheck5437]

theorem rawRowCheck5438 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5438 := by decide +kernel

theorem rowCheck5438 : row5438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5438 := by decide +kernel

theorem rowEval5438 (x : Key → ℝ) : Integer.Sparse.eval row5438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5438, Integer.Sparse.eval_collectBalanced, rawRowCheck5438]

theorem rawRowCheck5439 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5439 := by decide +kernel

theorem rowCheck5439 : row5439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5439 := by decide +kernel

theorem rowEval5439 (x : Key → ℝ) : Integer.Sparse.eval row5439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5439, Integer.Sparse.eval_collectBalanced, rawRowCheck5439]

theorem rawRowCheck5440 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5440 := by decide +kernel

theorem rowCheck5440 : row5440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5440 := by decide +kernel

theorem rowEval5440 (x : Key → ℝ) : Integer.Sparse.eval row5440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5440, Integer.Sparse.eval_collectBalanced, rawRowCheck5440]

theorem rawRowCheck5441 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5441 := by decide +kernel

theorem rowCheck5441 : row5441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5441 := by decide +kernel

theorem rowEval5441 (x : Key → ℝ) : Integer.Sparse.eval row5441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5441, Integer.Sparse.eval_collectBalanced, rawRowCheck5441]

theorem rawRowCheck5442 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5442 := by decide +kernel

theorem rowCheck5442 : row5442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5442 := by decide +kernel

theorem rowEval5442 (x : Key → ℝ) : Integer.Sparse.eval row5442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5442, Integer.Sparse.eval_collectBalanced, rawRowCheck5442]

theorem rawRowCheck5443 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5443 := by decide +kernel

theorem rowCheck5443 : row5443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5443 := by decide +kernel

theorem rowEval5443 (x : Key → ℝ) : Integer.Sparse.eval row5443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5443, Integer.Sparse.eval_collectBalanced, rawRowCheck5443]

theorem rawRowCheck5444 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5444 := by decide +kernel

theorem rowCheck5444 : row5444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5444 := by decide +kernel

theorem rowEval5444 (x : Key → ℝ) : Integer.Sparse.eval row5444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5444, Integer.Sparse.eval_collectBalanced, rawRowCheck5444]

theorem rawRowCheck5445 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1 = rawRow5445 := by decide +kernel

theorem rowCheck5445 : row5445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5445 := by decide +kernel

theorem rowEval5445 (x : Key → ℝ) : Integer.Sparse.eval row5445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5445, Integer.Sparse.eval_collectBalanced, rawRowCheck5445]

theorem rawRowCheck5446 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1 = rawRow5446 := by decide +kernel

theorem rowCheck5446 : row5446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5446 := by decide +kernel

theorem rowEval5446 (x : Key → ℝ) : Integer.Sparse.eval row5446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5446, Integer.Sparse.eval_collectBalanced, rawRowCheck5446]

theorem rawRowCheck5447 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1 = rawRow5447 := by decide +kernel

theorem rowCheck5447 : row5447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5447 := by decide +kernel

theorem rowEval5447 (x : Key → ℝ) : Integer.Sparse.eval row5447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5447, Integer.Sparse.eval_collectBalanced, rawRowCheck5447]

theorem rawRowCheck5478 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5478 := by decide +kernel

theorem rowCheck5478 : row5478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5478 := by decide +kernel

theorem rowEval5478 (x : Key → ℝ) : Integer.Sparse.eval row5478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5478, Integer.Sparse.eval_collectBalanced, rawRowCheck5478]

theorem rawRowCheck5479 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5479 := by decide +kernel

theorem rowCheck5479 : row5479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5479 := by decide +kernel

theorem rowEval5479 (x : Key → ℝ) : Integer.Sparse.eval row5479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5479, Integer.Sparse.eval_collectBalanced, rawRowCheck5479]

theorem rawRowCheck5480 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5480 := by decide +kernel

theorem rowCheck5480 : row5480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5480 := by decide +kernel

theorem rowEval5480 (x : Key → ℝ) : Integer.Sparse.eval row5480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5480, Integer.Sparse.eval_collectBalanced, rawRowCheck5480]

theorem rawRowCheck5481 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5481 := by decide +kernel

theorem rowCheck5481 : row5481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5481 := by decide +kernel

theorem rowEval5481 (x : Key → ℝ) : Integer.Sparse.eval row5481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5481, Integer.Sparse.eval_collectBalanced, rawRowCheck5481]

theorem rawRowCheck5482 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5482 := by decide +kernel

theorem rowCheck5482 : row5482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5482 := by decide +kernel

theorem rowEval5482 (x : Key → ℝ) : Integer.Sparse.eval row5482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5482, Integer.Sparse.eval_collectBalanced, rawRowCheck5482]

theorem rawRowCheck5483 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5483 := by decide +kernel

theorem rowCheck5483 : row5483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5483 := by decide +kernel

theorem rowEval5483 (x : Key → ℝ) : Integer.Sparse.eval row5483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5483, Integer.Sparse.eval_collectBalanced, rawRowCheck5483]

theorem rawRowCheck5484 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5484 := by decide +kernel

theorem rowCheck5484 : row5484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5484 := by decide +kernel

theorem rowEval5484 (x : Key → ℝ) : Integer.Sparse.eval row5484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5484, Integer.Sparse.eval_collectBalanced, rawRowCheck5484]

theorem rawRowCheck5485 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5485 := by decide +kernel

theorem rowCheck5485 : row5485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5485 := by decide +kernel

theorem rowEval5485 (x : Key → ℝ) : Integer.Sparse.eval row5485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5485, Integer.Sparse.eval_collectBalanced, rawRowCheck5485]

theorem rawRowCheck5486 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5486 := by decide +kernel

theorem rowCheck5486 : row5486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5486 := by decide +kernel

theorem rowEval5486 (x : Key → ℝ) : Integer.Sparse.eval row5486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5486, Integer.Sparse.eval_collectBalanced, rawRowCheck5486]

theorem rawRowCheck5487 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3 = rawRow5487 := by decide +kernel

theorem rowCheck5487 : row5487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5487 := by decide +kernel

theorem rowEval5487 (x : Key → ℝ) : Integer.Sparse.eval row5487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5487, Integer.Sparse.eval_collectBalanced, rawRowCheck5487]

theorem rawRowCheck5488 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3 = rawRow5488 := by decide +kernel

theorem rowCheck5488 : row5488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5488 := by decide +kernel

theorem rowEval5488 (x : Key → ℝ) : Integer.Sparse.eval row5488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5488, Integer.Sparse.eval_collectBalanced, rawRowCheck5488]

theorem rawRowCheck5489 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3 = rawRow5489 := by decide +kernel

theorem rowCheck5489 : row5489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5489 := by decide +kernel

theorem rowEval5489 (x : Key → ℝ) : Integer.Sparse.eval row5489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5489, Integer.Sparse.eval_collectBalanced, rawRowCheck5489]

theorem rawRowCheck5490 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5490 := by decide +kernel

theorem rowCheck5490 : row5490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5490 := by decide +kernel

theorem rowEval5490 (x : Key → ℝ) : Integer.Sparse.eval row5490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5490, Integer.Sparse.eval_collectBalanced, rawRowCheck5490]

theorem rawRowCheck5491 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5491 := by decide +kernel

theorem rowCheck5491 : row5491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5491 := by decide +kernel

theorem rowEval5491 (x : Key → ℝ) : Integer.Sparse.eval row5491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5491, Integer.Sparse.eval_collectBalanced, rawRowCheck5491]

theorem rawRowCheck5492 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5492 := by decide +kernel

theorem rowCheck5492 : row5492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5492 := by decide +kernel

theorem rowEval5492 (x : Key → ℝ) : Integer.Sparse.eval row5492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5492, Integer.Sparse.eval_collectBalanced, rawRowCheck5492]

theorem rawRowCheck5493 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5493 := by decide +kernel

theorem rowCheck5493 : row5493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5493 := by decide +kernel

theorem rowEval5493 (x : Key → ℝ) : Integer.Sparse.eval row5493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5493, Integer.Sparse.eval_collectBalanced, rawRowCheck5493]

theorem rawRowCheck5494 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5494 := by decide +kernel

theorem rowCheck5494 : row5494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5494 := by decide +kernel

theorem rowEval5494 (x : Key → ℝ) : Integer.Sparse.eval row5494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5494, Integer.Sparse.eval_collectBalanced, rawRowCheck5494]

theorem rawRowCheck5495 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5495 := by decide +kernel

theorem rowCheck5495 : row5495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5495 := by decide +kernel

theorem rowEval5495 (x : Key → ℝ) : Integer.Sparse.eval row5495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5495, Integer.Sparse.eval_collectBalanced, rawRowCheck5495]

theorem rawRowCheck5496 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5496 := by decide +kernel

theorem rowCheck5496 : row5496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5496 := by decide +kernel

theorem rowEval5496 (x : Key → ℝ) : Integer.Sparse.eval row5496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5496, Integer.Sparse.eval_collectBalanced, rawRowCheck5496]

theorem rawRowCheck5497 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5497 := by decide +kernel

theorem rowCheck5497 : row5497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5497 := by decide +kernel

theorem rowEval5497 (x : Key → ℝ) : Integer.Sparse.eval row5497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5497, Integer.Sparse.eval_collectBalanced, rawRowCheck5497]

theorem rawRowCheck5498 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5498 := by decide +kernel

theorem rowCheck5498 : row5498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5498 := by decide +kernel

theorem rowEval5498 (x : Key → ℝ) : Integer.Sparse.eval row5498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5498, Integer.Sparse.eval_collectBalanced, rawRowCheck5498]

theorem rawRowCheck5499 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5499 := by decide +kernel

theorem rowCheck5499 : row5499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5499 := by decide +kernel

theorem rowEval5499 (x : Key → ℝ) : Integer.Sparse.eval row5499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5499, Integer.Sparse.eval_collectBalanced, rawRowCheck5499]

theorem rawRowCheck5500 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5500 := by decide +kernel

theorem rowCheck5500 : row5500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5500 := by decide +kernel

theorem rowEval5500 (x : Key → ℝ) : Integer.Sparse.eval row5500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5500, Integer.Sparse.eval_collectBalanced, rawRowCheck5500]

theorem rawRowCheck5501 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5501 := by decide +kernel

theorem rowCheck5501 : row5501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5501 := by decide +kernel

theorem rowEval5501 (x : Key → ℝ) : Integer.Sparse.eval row5501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5501, Integer.Sparse.eval_collectBalanced, rawRowCheck5501]

theorem rawRowCheck5502 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5502 := by decide +kernel

theorem rowCheck5502 : row5502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5502 := by decide +kernel

theorem rowEval5502 (x : Key → ℝ) : Integer.Sparse.eval row5502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5502, Integer.Sparse.eval_collectBalanced, rawRowCheck5502]

theorem rawRowCheck5503 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5503 := by decide +kernel

theorem rowCheck5503 : row5503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5503 := by decide +kernel

theorem rowEval5503 (x : Key → ℝ) : Integer.Sparse.eval row5503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5503, Integer.Sparse.eval_collectBalanced, rawRowCheck5503]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck5504 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5504 := by decide +kernel

theorem rowCheck5504 : row5504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5504 := by decide +kernel

theorem rowEval5504 (x : Key → ℝ) : Integer.Sparse.eval row5504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5504, Integer.Sparse.eval_collectBalanced, rawRowCheck5504]

theorem rawRowCheck5505 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3 = rawRow5505 := by decide +kernel

theorem rowCheck5505 : row5505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5505 := by decide +kernel

theorem rowEval5505 (x : Key → ℝ) : Integer.Sparse.eval row5505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5505, Integer.Sparse.eval_collectBalanced, rawRowCheck5505]

theorem rawRowCheck5506 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3 = rawRow5506 := by decide +kernel

theorem rowCheck5506 : row5506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5506 := by decide +kernel

theorem rowEval5506 (x : Key → ℝ) : Integer.Sparse.eval row5506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5506, Integer.Sparse.eval_collectBalanced, rawRowCheck5506]

theorem rawRowCheck5507 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3 = rawRow5507 := by decide +kernel

theorem rowCheck5507 : row5507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5507 := by decide +kernel

theorem rowEval5507 (x : Key → ℝ) : Integer.Sparse.eval row5507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5507, Integer.Sparse.eval_collectBalanced, rawRowCheck5507]

theorem rawRowCheck5598 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5598 := by decide +kernel

theorem rowCheck5598 : row5598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5598 := by decide +kernel

theorem rowEval5598 (x : Key → ℝ) : Integer.Sparse.eval row5598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5598, Integer.Sparse.eval_collectBalanced, rawRowCheck5598]

theorem rawRowCheck5599 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5599 := by decide +kernel

theorem rowCheck5599 : row5599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5599 := by decide +kernel

theorem rowEval5599 (x : Key → ℝ) : Integer.Sparse.eval row5599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5599, Integer.Sparse.eval_collectBalanced, rawRowCheck5599]

theorem rawRowCheck5600 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5600 := by decide +kernel

theorem rowCheck5600 : row5600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5600 := by decide +kernel

theorem rowEval5600 (x : Key → ℝ) : Integer.Sparse.eval row5600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5600, Integer.Sparse.eval_collectBalanced, rawRowCheck5600]

theorem rawRowCheck5601 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5601 := by decide +kernel

theorem rowCheck5601 : row5601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5601 := by decide +kernel

theorem rowEval5601 (x : Key → ℝ) : Integer.Sparse.eval row5601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5601, Integer.Sparse.eval_collectBalanced, rawRowCheck5601]

theorem rawRowCheck5602 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5602 := by decide +kernel

theorem rowCheck5602 : row5602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5602 := by decide +kernel

theorem rowEval5602 (x : Key → ℝ) : Integer.Sparse.eval row5602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5602, Integer.Sparse.eval_collectBalanced, rawRowCheck5602]

theorem rawRowCheck5603 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5603 := by decide +kernel

theorem rowCheck5603 : row5603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5603 := by decide +kernel

theorem rowEval5603 (x : Key → ℝ) : Integer.Sparse.eval row5603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5603, Integer.Sparse.eval_collectBalanced, rawRowCheck5603]

theorem rawRowCheck5604 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5604 := by decide +kernel

theorem rowCheck5604 : row5604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5604 := by decide +kernel

theorem rowEval5604 (x : Key → ℝ) : Integer.Sparse.eval row5604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5604, Integer.Sparse.eval_collectBalanced, rawRowCheck5604]

theorem rawRowCheck5605 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5605 := by decide +kernel

theorem rowCheck5605 : row5605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5605 := by decide +kernel

theorem rowEval5605 (x : Key → ℝ) : Integer.Sparse.eval row5605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5605, Integer.Sparse.eval_collectBalanced, rawRowCheck5605]

theorem rawRowCheck5606 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5606 := by decide +kernel

theorem rowCheck5606 : row5606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5606 := by decide +kernel

theorem rowEval5606 (x : Key → ℝ) : Integer.Sparse.eval row5606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5606, Integer.Sparse.eval_collectBalanced, rawRowCheck5606]

theorem rawRowCheck5607 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3 = rawRow5607 := by decide +kernel

theorem rowCheck5607 : row5607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5607 := by decide +kernel

theorem rowEval5607 (x : Key → ℝ) : Integer.Sparse.eval row5607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5607, Integer.Sparse.eval_collectBalanced, rawRowCheck5607]

theorem rawRowCheck5608 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3 = rawRow5608 := by decide +kernel

theorem rowCheck5608 : row5608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5608 := by decide +kernel

theorem rowEval5608 (x : Key → ℝ) : Integer.Sparse.eval row5608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5608, Integer.Sparse.eval_collectBalanced, rawRowCheck5608]

theorem rawRowCheck5609 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3 = rawRow5609 := by decide +kernel

theorem rowCheck5609 : row5609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5609 := by decide +kernel

theorem rowEval5609 (x : Key → ℝ) : Integer.Sparse.eval row5609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5609, Integer.Sparse.eval_collectBalanced, rawRowCheck5609]

theorem rawRowCheck5610 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5610 := by decide +kernel

theorem rowCheck5610 : row5610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5610 := by decide +kernel

theorem rowEval5610 (x : Key → ℝ) : Integer.Sparse.eval row5610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5610, Integer.Sparse.eval_collectBalanced, rawRowCheck5610]

theorem rawRowCheck5611 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5611 := by decide +kernel

theorem rowCheck5611 : row5611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5611 := by decide +kernel

theorem rowEval5611 (x : Key → ℝ) : Integer.Sparse.eval row5611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5611, Integer.Sparse.eval_collectBalanced, rawRowCheck5611]

theorem rawRowCheck5612 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5612 := by decide +kernel

theorem rowCheck5612 : row5612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5612 := by decide +kernel

theorem rowEval5612 (x : Key → ℝ) : Integer.Sparse.eval row5612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5612, Integer.Sparse.eval_collectBalanced, rawRowCheck5612]

theorem rawRowCheck5613 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5613 := by decide +kernel

theorem rowCheck5613 : row5613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5613 := by decide +kernel

theorem rowEval5613 (x : Key → ℝ) : Integer.Sparse.eval row5613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5613, Integer.Sparse.eval_collectBalanced, rawRowCheck5613]

theorem rawRowCheck5614 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5614 := by decide +kernel

theorem rowCheck5614 : row5614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5614 := by decide +kernel

theorem rowEval5614 (x : Key → ℝ) : Integer.Sparse.eval row5614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5614, Integer.Sparse.eval_collectBalanced, rawRowCheck5614]

theorem rawRowCheck5615 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5615 := by decide +kernel

theorem rowCheck5615 : row5615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5615 := by decide +kernel

theorem rowEval5615 (x : Key → ℝ) : Integer.Sparse.eval row5615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5615, Integer.Sparse.eval_collectBalanced, rawRowCheck5615]

theorem rawRowCheck5616 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5616 := by decide +kernel

theorem rowCheck5616 : row5616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5616 := by decide +kernel

theorem rowEval5616 (x : Key → ℝ) : Integer.Sparse.eval row5616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5616, Integer.Sparse.eval_collectBalanced, rawRowCheck5616]

theorem rawRowCheck5617 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5617 := by decide +kernel

theorem rowCheck5617 : row5617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5617 := by decide +kernel

theorem rowEval5617 (x : Key → ℝ) : Integer.Sparse.eval row5617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5617, Integer.Sparse.eval_collectBalanced, rawRowCheck5617]

theorem rawRowCheck5618 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5618 := by decide +kernel

theorem rowCheck5618 : row5618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5618 := by decide +kernel

theorem rowEval5618 (x : Key → ℝ) : Integer.Sparse.eval row5618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5618, Integer.Sparse.eval_collectBalanced, rawRowCheck5618]

theorem rawRowCheck5619 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5619 := by decide +kernel

theorem rowCheck5619 : row5619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5619 := by decide +kernel

theorem rowEval5619 (x : Key → ℝ) : Integer.Sparse.eval row5619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5619, Integer.Sparse.eval_collectBalanced, rawRowCheck5619]

theorem rawRowCheck5620 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5620 := by decide +kernel

theorem rowCheck5620 : row5620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5620 := by decide +kernel

theorem rowEval5620 (x : Key → ℝ) : Integer.Sparse.eval row5620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5620, Integer.Sparse.eval_collectBalanced, rawRowCheck5620]

theorem rawRowCheck5621 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5621 := by decide +kernel

theorem rowCheck5621 : row5621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5621 := by decide +kernel

theorem rowEval5621 (x : Key → ℝ) : Integer.Sparse.eval row5621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5621, Integer.Sparse.eval_collectBalanced, rawRowCheck5621]

theorem rawRowCheck5622 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5622 := by decide +kernel

theorem rowCheck5622 : row5622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5622 := by decide +kernel

theorem rowEval5622 (x : Key → ℝ) : Integer.Sparse.eval row5622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5622, Integer.Sparse.eval_collectBalanced, rawRowCheck5622]

theorem rawRowCheck5623 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5623 := by decide +kernel

theorem rowCheck5623 : row5623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5623 := by decide +kernel

theorem rowEval5623 (x : Key → ℝ) : Integer.Sparse.eval row5623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5623, Integer.Sparse.eval_collectBalanced, rawRowCheck5623]

theorem rawRowCheck5624 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5624 := by decide +kernel

theorem rowCheck5624 : row5624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5624 := by decide +kernel

theorem rowEval5624 (x : Key → ℝ) : Integer.Sparse.eval row5624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5624, Integer.Sparse.eval_collectBalanced, rawRowCheck5624]

theorem rawRowCheck5625 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3 = rawRow5625 := by decide +kernel

theorem rowCheck5625 : row5625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5625 := by decide +kernel

theorem rowEval5625 (x : Key → ℝ) : Integer.Sparse.eval row5625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5625, Integer.Sparse.eval_collectBalanced, rawRowCheck5625]

theorem rawRowCheck5626 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3 = rawRow5626 := by decide +kernel

theorem rowCheck5626 : row5626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5626 := by decide +kernel

theorem rowEval5626 (x : Key → ℝ) : Integer.Sparse.eval row5626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5626, Integer.Sparse.eval_collectBalanced, rawRowCheck5626]

theorem rawRowCheck5627 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3 = rawRow5627 := by decide +kernel

theorem rowCheck5627 : row5627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5627 := by decide +kernel

theorem rowEval5627 (x : Key → ℝ) : Integer.Sparse.eval row5627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5627, Integer.Sparse.eval_collectBalanced, rawRowCheck5627]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block2.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form3.terms k).tag (GramFunctions.Block2.form3.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5418 x
  · exact rowEval5419 x
  · exact rowEval5420 x
  · exact rowEval5421 x
  · exact rowEval5422 x
  · exact rowEval5423 x
  · exact rowEval5424 x
  · exact rowEval5425 x
  · exact rowEval5426 x
  · exact rowEval5427 x
  · exact rowEval5428 x
  · exact rowEval5429 x
  · exact rowEval5430 x
  · exact rowEval5431 x
  · exact rowEval5432 x
  · exact rowEval5433 x
  · exact rowEval5434 x
  · exact rowEval5435 x
  · exact rowEval5436 x
  · exact rowEval5437 x
  · exact rowEval5438 x
  · exact rowEval5439 x
  · exact rowEval5440 x
  · exact rowEval5441 x
  · exact rowEval5442 x
  · exact rowEval5443 x
  · exact rowEval5444 x
  · exact rowEval5445 x
  · exact rowEval5446 x
  · exact rowEval5447 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block2.form3.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form3 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block2.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form3.terms k).tag (GramFunctions.Block2.form3.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval5478 x
  · exact rowEval5479 x
  · exact rowEval5480 x
  · exact rowEval5481 x
  · exact rowEval5482 x
  · exact rowEval5483 x
  · exact rowEval5484 x
  · exact rowEval5485 x
  · exact rowEval5486 x
  · exact rowEval5487 x
  · exact rowEval5488 x
  · exact rowEval5489 x
  · exact rowEval5490 x
  · exact rowEval5491 x
  · exact rowEval5492 x
  · exact rowEval5493 x
  · exact rowEval5494 x
  · exact rowEval5495 x
  · exact rowEval5496 x
  · exact rowEval5497 x
  · exact rowEval5498 x
  · exact rowEval5499 x
  · exact rowEval5500 x
  · exact rowEval5501 x
  · exact rowEval5502 x
  · exact rowEval5503 x
  · exact rowEval5504 x
  · exact rowEval5505 x
  · exact rowEval5506 x
  · exact rowEval5507 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block2.form3.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form3 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval5598 x
  · exact rowEval5599 x
  · exact rowEval5600 x
  · exact rowEval5601 x
  · exact rowEval5602 x
  · exact rowEval5603 x
  · exact rowEval5604 x
  · exact rowEval5605 x
  · exact rowEval5606 x
  · exact rowEval5607 x
  · exact rowEval5608 x
  · exact rowEval5609 x
  · exact rowEval5610 x
  · exact rowEval5611 x
  · exact rowEval5612 x
  · exact rowEval5613 x
  · exact rowEval5614 x
  · exact rowEval5615 x
  · exact rowEval5616 x
  · exact rowEval5617 x
  · exact rowEval5618 x
  · exact rowEval5619 x
  · exact rowEval5620 x
  · exact rowEval5621 x
  · exact rowEval5622 x
  · exact rowEval5623 x
  · exact rowEval5624 x
  · exact rowEval5625 x
  · exact rowEval5626 x
  · exact rowEval5627 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

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

theorem entryEvalRow3_e_oai (j : Fin 11) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block2.forms 3).mixedGram (GramFunctions.Block2.forms j) B := by
  fin_cases j
  · exact entryEval3_0_e B hB
  · exact entryEval3_1 B hB
  · exact entryEval3_2_e B hB
  · exact entryEval3_3 B hB
  · exact (entryEval4_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow3_e_oai := @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow3_e_oai
