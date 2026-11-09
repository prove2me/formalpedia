-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:25:01.947206+00:00
-- url     : https://prove2.me/submissions/f34d377d-9ddd-4300-b718-77af5fa6d81a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E030
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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval5_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval8_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval9_3_e

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

theorem rawRowCheck8685 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form3 = rawRow8685 := by decide +kernel

theorem rowCheck8685 : row8685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8685 := by decide +kernel

theorem rowEval8685 (x : Key → ℝ) : Integer.Sparse.eval row8685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8685, Integer.Sparse.eval_collectBalanced, rawRowCheck8685]

theorem rawRowCheck8686 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form3 = rawRow8686 := by decide +kernel

theorem rowCheck8686 : row8686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8686 := by decide +kernel

theorem rowEval8686 (x : Key → ℝ) : Integer.Sparse.eval row8686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8686, Integer.Sparse.eval_collectBalanced, rawRowCheck8686]

theorem rawRowCheck8687 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form3 = rawRow8687 := by decide +kernel

theorem rowCheck8687 : row8687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8687 := by decide +kernel

theorem rowEval8687 (x : Key → ℝ) : Integer.Sparse.eval row8687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8687, Integer.Sparse.eval_collectBalanced, rawRowCheck8687]

theorem rawRowCheck8688 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8688 := by decide +kernel

theorem rowCheck8688 : row8688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8688 := by decide +kernel

theorem rowEval8688 (x : Key → ℝ) : Integer.Sparse.eval row8688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8688, Integer.Sparse.eval_collectBalanced, rawRowCheck8688]

theorem rawRowCheck8689 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8689 := by decide +kernel

theorem rowCheck8689 : row8689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8689 := by decide +kernel

theorem rowEval8689 (x : Key → ℝ) : Integer.Sparse.eval row8689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8689, Integer.Sparse.eval_collectBalanced, rawRowCheck8689]

theorem rawRowCheck8690 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow8690 := by decide +kernel

theorem rowCheck8690 : row8690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8690 := by decide +kernel

theorem rowEval8690 (x : Key → ℝ) : Integer.Sparse.eval row8690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8690, Integer.Sparse.eval_collectBalanced, rawRowCheck8690]

theorem rawRowCheck8691 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow8691 := by decide +kernel

theorem rowCheck8691 : row8691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8691 := by decide +kernel

theorem rowEval8691 (x : Key → ℝ) : Integer.Sparse.eval row8691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8691, Integer.Sparse.eval_collectBalanced, rawRowCheck8691]

theorem rawRowCheck8692 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow8692 := by decide +kernel

theorem rowCheck8692 : row8692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8692 := by decide +kernel

theorem rowEval8692 (x : Key → ℝ) : Integer.Sparse.eval row8692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck8692, Integer.Sparse.eval_collectBalanced, rawRowCheck8692]

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

theorem rawRowCheck8769 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8769 := by decide +kernel

theorem rowCheck8769 : row8769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8769 := by decide +kernel

theorem rowEval8769 (x : Key → ℝ) : Integer.Sparse.eval row8769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8769, Integer.Sparse.eval_collectBalanced, rawRowCheck8769]

theorem rawRowCheck8770 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow8770 := by decide +kernel

theorem rowCheck8770 : row8770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8770 := by decide +kernel

theorem rowEval8770 (x : Key → ℝ) : Integer.Sparse.eval row8770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8770, Integer.Sparse.eval_collectBalanced, rawRowCheck8770]

theorem rawRowCheck8771 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow8771 := by decide +kernel

theorem rowCheck8771 : row8771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8771 := by decide +kernel

theorem rowEval8771 (x : Key → ℝ) : Integer.Sparse.eval row8771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8771, Integer.Sparse.eval_collectBalanced, rawRowCheck8771]

theorem rawRowCheck8772 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow8772 := by decide +kernel

theorem rowCheck8772 : row8772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8772 := by decide +kernel

theorem rowEval8772 (x : Key → ℝ) : Integer.Sparse.eval row8772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck8772, Integer.Sparse.eval_collectBalanced, rawRowCheck8772]

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

theorem entryCheck11_3 : entry11_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_3 k)) := by decide +kernel

theorem rowsSound11_3 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8685 x
  · exact rowEval8686 x
  · exact rowEval8687 x
  · exact rowEval8688 x
  · exact rowEval8689 x
  · exact rowEval8690 x
  · exact rowEval8691 x
  · exact rowEval8692 x

theorem entryEval11_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_3 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck11_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7430 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7430 := by decide +kernel

theorem rowCheck7430 : row7430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7430 := by decide +kernel

theorem rowEval7430 (x : Key → ℝ) : Integer.Sparse.eval row7430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7430, Integer.Sparse.eval_collectBalanced, rawRowCheck7430]

theorem rawRowCheck7431 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7431 := by decide +kernel

theorem rowCheck7431 : row7431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7431 := by decide +kernel

theorem rowEval7431 (x : Key → ℝ) : Integer.Sparse.eval row7431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7431, Integer.Sparse.eval_collectBalanced, rawRowCheck7431]

theorem rawRowCheck7432 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7432 := by decide +kernel

theorem rowCheck7432 : row7432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7432 := by decide +kernel

theorem rowEval7432 (x : Key → ℝ) : Integer.Sparse.eval row7432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7432, Integer.Sparse.eval_collectBalanced, rawRowCheck7432]

theorem rawRowCheck7433 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7433 := by decide +kernel

theorem rowCheck7433 : row7433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7433 := by decide +kernel

theorem rowEval7433 (x : Key → ℝ) : Integer.Sparse.eval row7433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7433, Integer.Sparse.eval_collectBalanced, rawRowCheck7433]

theorem rawRowCheck7434 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow7434 := by decide +kernel

theorem rowCheck7434 : row7434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7434 := by decide +kernel

theorem rowEval7434 (x : Key → ℝ) : Integer.Sparse.eval row7434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7434, Integer.Sparse.eval_collectBalanced, rawRowCheck7434]

theorem rawRowCheck7435 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow7435 := by decide +kernel

theorem rowCheck7435 : row7435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7435 := by decide +kernel

theorem rowEval7435 (x : Key → ℝ) : Integer.Sparse.eval row7435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7435, Integer.Sparse.eval_collectBalanced, rawRowCheck7435]

theorem rawRowCheck7436 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow7436 := by decide +kernel

theorem rowCheck7436 : row7436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7436 := by decide +kernel

theorem rowEval7436 (x : Key → ℝ) : Integer.Sparse.eval row7436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7436, Integer.Sparse.eval_collectBalanced, rawRowCheck7436]

theorem rawRowCheck7437 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7437 := by decide +kernel

theorem rowCheck7437 : row7437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7437 := by decide +kernel

theorem rowEval7437 (x : Key → ℝ) : Integer.Sparse.eval row7437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7437, Integer.Sparse.eval_collectBalanced, rawRowCheck7437]

theorem rawRowCheck7438 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7438 := by decide +kernel

theorem rowCheck7438 : row7438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7438 := by decide +kernel

theorem rowEval7438 (x : Key → ℝ) : Integer.Sparse.eval row7438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7438, Integer.Sparse.eval_collectBalanced, rawRowCheck7438]

theorem rawRowCheck7439 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7439 := by decide +kernel

theorem rowCheck7439 : row7439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7439 := by decide +kernel

theorem rowEval7439 (x : Key → ℝ) : Integer.Sparse.eval row7439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7439, Integer.Sparse.eval_collectBalanced, rawRowCheck7439]

theorem rawRowCheck7440 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0 = rawRow7440 := by decide +kernel

theorem rowCheck7440 : row7440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7440 := by decide +kernel

theorem rowEval7440 (x : Key → ℝ) : Integer.Sparse.eval row7440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7440, Integer.Sparse.eval_collectBalanced, rawRowCheck7440]

theorem rawRowCheck7441 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0 = rawRow7441 := by decide +kernel

theorem rowCheck7441 : row7441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7441 := by decide +kernel

theorem rowEval7441 (x : Key → ℝ) : Integer.Sparse.eval row7441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7441, Integer.Sparse.eval_collectBalanced, rawRowCheck7441]

theorem rawRowCheck7442 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0 = rawRow7442 := by decide +kernel

theorem rowCheck7442 : row7442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7442 := by decide +kernel

theorem rowEval7442 (x : Key → ℝ) : Integer.Sparse.eval row7442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7442, Integer.Sparse.eval_collectBalanced, rawRowCheck7442]

theorem rawRowCheck7443 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0 = rawRow7443 := by decide +kernel

theorem rowCheck7443 : row7443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7443 := by decide +kernel

theorem rowEval7443 (x : Key → ℝ) : Integer.Sparse.eval row7443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7443, Integer.Sparse.eval_collectBalanced, rawRowCheck7443]

theorem rawRowCheck7444 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0 = rawRow7444 := by decide +kernel

theorem rowCheck7444 : row7444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7444 := by decide +kernel

theorem rowEval7444 (x : Key → ℝ) : Integer.Sparse.eval row7444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7444, Integer.Sparse.eval_collectBalanced, rawRowCheck7444]

theorem rawRowCheck7445 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0 = rawRow7445 := by decide +kernel

theorem rowCheck7445 : row7445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7445 := by decide +kernel

theorem rowEval7445 (x : Key → ℝ) : Integer.Sparse.eval row7445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7445, Integer.Sparse.eval_collectBalanced, rawRowCheck7445]

theorem rawRowCheck7446 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7446 := by decide +kernel

theorem rowCheck7446 : row7446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7446 := by decide +kernel

theorem rowEval7446 (x : Key → ℝ) : Integer.Sparse.eval row7446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7446, Integer.Sparse.eval_collectBalanced, rawRowCheck7446]

theorem rawRowCheck7447 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7447 := by decide +kernel

theorem rowCheck7447 : row7447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7447 := by decide +kernel

theorem rowEval7447 (x : Key → ℝ) : Integer.Sparse.eval row7447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7447, Integer.Sparse.eval_collectBalanced, rawRowCheck7447]

theorem rawRowCheck7448 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7448 := by decide +kernel

theorem rowCheck7448 : row7448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7448 := by decide +kernel

theorem rowEval7448 (x : Key → ℝ) : Integer.Sparse.eval row7448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7448, Integer.Sparse.eval_collectBalanced, rawRowCheck7448]

theorem rawRowCheck7449 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7449 := by decide +kernel

theorem rowCheck7449 : row7449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7449 := by decide +kernel

theorem rowEval7449 (x : Key → ℝ) : Integer.Sparse.eval row7449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7449, Integer.Sparse.eval_collectBalanced, rawRowCheck7449]

theorem rawRowCheck7450 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow7450 := by decide +kernel

theorem rowCheck7450 : row7450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7450 := by decide +kernel

theorem rowEval7450 (x : Key → ℝ) : Integer.Sparse.eval row7450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7450, Integer.Sparse.eval_collectBalanced, rawRowCheck7450]

theorem rawRowCheck7451 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow7451 := by decide +kernel

theorem rowCheck7451 : row7451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7451 := by decide +kernel

theorem rowEval7451 (x : Key → ℝ) : Integer.Sparse.eval row7451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7451, Integer.Sparse.eval_collectBalanced, rawRowCheck7451]

theorem rawRowCheck7452 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow7452 := by decide +kernel

theorem rowCheck7452 : row7452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7452 := by decide +kernel

theorem rowEval7452 (x : Key → ℝ) : Integer.Sparse.eval row7452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7452, Integer.Sparse.eval_collectBalanced, rawRowCheck7452]

theorem rawRowCheck7453 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7453 := by decide +kernel

theorem rowCheck7453 : row7453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7453 := by decide +kernel

theorem rowEval7453 (x : Key → ℝ) : Integer.Sparse.eval row7453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7453, Integer.Sparse.eval_collectBalanced, rawRowCheck7453]

theorem rawRowCheck7454 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7454 := by decide +kernel

theorem rowCheck7454 : row7454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7454 := by decide +kernel

theorem rowEval7454 (x : Key → ℝ) : Integer.Sparse.eval row7454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7454, Integer.Sparse.eval_collectBalanced, rawRowCheck7454]

theorem rawRowCheck7455 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7455 := by decide +kernel

theorem rowCheck7455 : row7455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7455 := by decide +kernel

theorem rowEval7455 (x : Key → ℝ) : Integer.Sparse.eval row7455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7455, Integer.Sparse.eval_collectBalanced, rawRowCheck7455]

theorem rawRowCheck7456 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form1 = rawRow7456 := by decide +kernel

theorem rowCheck7456 : row7456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7456 := by decide +kernel

theorem rowEval7456 (x : Key → ℝ) : Integer.Sparse.eval row7456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7456, Integer.Sparse.eval_collectBalanced, rawRowCheck7456]

theorem rawRowCheck7457 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form1 = rawRow7457 := by decide +kernel

theorem rowCheck7457 : row7457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7457 := by decide +kernel

theorem rowEval7457 (x : Key → ℝ) : Integer.Sparse.eval row7457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7457, Integer.Sparse.eval_collectBalanced, rawRowCheck7457]

theorem rawRowCheck7458 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form1 = rawRow7458 := by decide +kernel

theorem rowCheck7458 : row7458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7458 := by decide +kernel

theorem rowEval7458 (x : Key → ℝ) : Integer.Sparse.eval row7458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7458, Integer.Sparse.eval_collectBalanced, rawRowCheck7458]

theorem rawRowCheck7459 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form1 = rawRow7459 := by decide +kernel

theorem rowCheck7459 : row7459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7459 := by decide +kernel

theorem rowEval7459 (x : Key → ℝ) : Integer.Sparse.eval row7459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7459, Integer.Sparse.eval_collectBalanced, rawRowCheck7459]

theorem rawRowCheck7460 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form1 = rawRow7460 := by decide +kernel

theorem rowCheck7460 : row7460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7460 := by decide +kernel

theorem rowEval7460 (x : Key → ℝ) : Integer.Sparse.eval row7460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7460, Integer.Sparse.eval_collectBalanced, rawRowCheck7460]

theorem rawRowCheck7461 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form1 = rawRow7461 := by decide +kernel

theorem rowCheck7461 : row7461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7461 := by decide +kernel

theorem rowEval7461 (x : Key → ℝ) : Integer.Sparse.eval row7461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7461, Integer.Sparse.eval_collectBalanced, rawRowCheck7461]

theorem rawRowCheck7462 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7462 := by decide +kernel

theorem rowCheck7462 : row7462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7462 := by decide +kernel

theorem rowEval7462 (x : Key → ℝ) : Integer.Sparse.eval row7462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7462, Integer.Sparse.eval_collectBalanced, rawRowCheck7462]

theorem rawRowCheck7463 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2 = rawRow7463 := by decide +kernel

theorem rowCheck7463 : row7463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7463 := by decide +kernel

theorem rowEval7463 (x : Key → ℝ) : Integer.Sparse.eval row7463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7463, Integer.Sparse.eval_collectBalanced, rawRowCheck7463]

theorem rawRowCheck7464 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2 = rawRow7464 := by decide +kernel

theorem rowCheck7464 : row7464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7464 := by decide +kernel

theorem rowEval7464 (x : Key → ℝ) : Integer.Sparse.eval row7464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7464, Integer.Sparse.eval_collectBalanced, rawRowCheck7464]

theorem rawRowCheck7465 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2 = rawRow7465 := by decide +kernel

theorem rowCheck7465 : row7465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7465 := by decide +kernel

theorem rowEval7465 (x : Key → ℝ) : Integer.Sparse.eval row7465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7465, Integer.Sparse.eval_collectBalanced, rawRowCheck7465]

theorem rawRowCheck7466 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow7466 := by decide +kernel

theorem rowCheck7466 : row7466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7466 := by decide +kernel

theorem rowEval7466 (x : Key → ℝ) : Integer.Sparse.eval row7466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7466, Integer.Sparse.eval_collectBalanced, rawRowCheck7466]

theorem rawRowCheck7467 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow7467 := by decide +kernel

theorem rowCheck7467 : row7467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7467 := by decide +kernel

theorem rowEval7467 (x : Key → ℝ) : Integer.Sparse.eval row7467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7467, Integer.Sparse.eval_collectBalanced, rawRowCheck7467]

theorem rawRowCheck7468 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow7468 := by decide +kernel

theorem rowCheck7468 : row7468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7468 := by decide +kernel

theorem rowEval7468 (x : Key → ℝ) : Integer.Sparse.eval row7468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7468, Integer.Sparse.eval_collectBalanced, rawRowCheck7468]

theorem rawRowCheck7469 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow7469 := by decide +kernel

theorem rowCheck7469 : row7469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7469 := by decide +kernel

theorem rowEval7469 (x : Key → ℝ) : Integer.Sparse.eval row7469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7469, Integer.Sparse.eval_collectBalanced, rawRowCheck7469]

theorem rawRowCheck7470 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow7470 := by decide +kernel

theorem rowCheck7470 : row7470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7470 := by decide +kernel

theorem rowEval7470 (x : Key → ℝ) : Integer.Sparse.eval row7470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7470, Integer.Sparse.eval_collectBalanced, rawRowCheck7470]

theorem rawRowCheck7471 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow7471 := by decide +kernel

theorem rowCheck7471 : row7471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7471 := by decide +kernel

theorem rowEval7471 (x : Key → ℝ) : Integer.Sparse.eval row7471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7471, Integer.Sparse.eval_collectBalanced, rawRowCheck7471]

theorem rawRowCheck7472 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form2 = rawRow7472 := by decide +kernel

theorem rowCheck7472 : row7472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7472 := by decide +kernel

theorem rowEval7472 (x : Key → ℝ) : Integer.Sparse.eval row7472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7472, Integer.Sparse.eval_collectBalanced, rawRowCheck7472]

theorem rawRowCheck7473 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form2 = rawRow7473 := by decide +kernel

theorem rowCheck7473 : row7473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7473 := by decide +kernel

theorem rowEval7473 (x : Key → ℝ) : Integer.Sparse.eval row7473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7473, Integer.Sparse.eval_collectBalanced, rawRowCheck7473]

theorem rawRowCheck7474 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form2 = rawRow7474 := by decide +kernel

theorem rowCheck7474 : row7474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7474 := by decide +kernel

theorem rowEval7474 (x : Key → ℝ) : Integer.Sparse.eval row7474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7474, Integer.Sparse.eval_collectBalanced, rawRowCheck7474]

theorem rawRowCheck7475 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form2 = rawRow7475 := by decide +kernel

theorem rowCheck7475 : row7475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7475 := by decide +kernel

theorem rowEval7475 (x : Key → ℝ) : Integer.Sparse.eval row7475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7475, Integer.Sparse.eval_collectBalanced, rawRowCheck7475]

theorem rawRowCheck7476 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form2 = rawRow7476 := by decide +kernel

theorem rowCheck7476 : row7476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7476 := by decide +kernel

theorem rowEval7476 (x : Key → ℝ) : Integer.Sparse.eval row7476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7476, Integer.Sparse.eval_collectBalanced, rawRowCheck7476]

theorem rawRowCheck7477 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form2 = rawRow7477 := by decide +kernel

theorem rowCheck7477 : row7477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7477 := by decide +kernel

theorem rowEval7477 (x : Key → ℝ) : Integer.Sparse.eval row7477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7477, Integer.Sparse.eval_collectBalanced, rawRowCheck7477]

theorem rawRowCheck7478 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7478 := by decide +kernel

theorem rowCheck7478 : row7478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7478 := by decide +kernel

theorem rowEval7478 (x : Key → ℝ) : Integer.Sparse.eval row7478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7478, Integer.Sparse.eval_collectBalanced, rawRowCheck7478]

theorem rawRowCheck7479 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3 = rawRow7479 := by decide +kernel

theorem rowCheck7479 : row7479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7479 := by decide +kernel

theorem rowEval7479 (x : Key → ℝ) : Integer.Sparse.eval row7479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7479, Integer.Sparse.eval_collectBalanced, rawRowCheck7479]

theorem rawRowCheck7480 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3 = rawRow7480 := by decide +kernel

theorem rowCheck7480 : row7480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7480 := by decide +kernel

theorem rowEval7480 (x : Key → ℝ) : Integer.Sparse.eval row7480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7480, Integer.Sparse.eval_collectBalanced, rawRowCheck7480]

theorem rawRowCheck7481 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3 = rawRow7481 := by decide +kernel

theorem rowCheck7481 : row7481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7481 := by decide +kernel

theorem rowEval7481 (x : Key → ℝ) : Integer.Sparse.eval row7481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7481, Integer.Sparse.eval_collectBalanced, rawRowCheck7481]

theorem rawRowCheck7482 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow7482 := by decide +kernel

theorem rowCheck7482 : row7482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7482 := by decide +kernel

theorem rowEval7482 (x : Key → ℝ) : Integer.Sparse.eval row7482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7482, Integer.Sparse.eval_collectBalanced, rawRowCheck7482]

theorem rawRowCheck7483 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow7483 := by decide +kernel

theorem rowCheck7483 : row7483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7483 := by decide +kernel

theorem rowEval7483 (x : Key → ℝ) : Integer.Sparse.eval row7483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7483, Integer.Sparse.eval_collectBalanced, rawRowCheck7483]

theorem rawRowCheck7484 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow7484 := by decide +kernel

theorem rowCheck7484 : row7484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7484 := by decide +kernel

theorem rowEval7484 (x : Key → ℝ) : Integer.Sparse.eval row7484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7484, Integer.Sparse.eval_collectBalanced, rawRowCheck7484]

theorem rawRowCheck7485 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow7485 := by decide +kernel

theorem rowCheck7485 : row7485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7485 := by decide +kernel

theorem rowEval7485 (x : Key → ℝ) : Integer.Sparse.eval row7485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7485, Integer.Sparse.eval_collectBalanced, rawRowCheck7485]

theorem rawRowCheck7486 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow7486 := by decide +kernel

theorem rowCheck7486 : row7486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7486 := by decide +kernel

theorem rowEval7486 (x : Key → ℝ) : Integer.Sparse.eval row7486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7486, Integer.Sparse.eval_collectBalanced, rawRowCheck7486]

theorem rawRowCheck7487 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow7487 := by decide +kernel

theorem rowCheck7487 : row7487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7487 := by decide +kernel

theorem rowEval7487 (x : Key → ℝ) : Integer.Sparse.eval row7487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7487, Integer.Sparse.eval_collectBalanced, rawRowCheck7487]

theorem rawRowCheck7488 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form3 = rawRow7488 := by decide +kernel

theorem rowCheck7488 : row7488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7488 := by decide +kernel

theorem rowEval7488 (x : Key → ℝ) : Integer.Sparse.eval row7488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7488, Integer.Sparse.eval_collectBalanced, rawRowCheck7488]

theorem rawRowCheck7489 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form3 = rawRow7489 := by decide +kernel

theorem rowCheck7489 : row7489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7489 := by decide +kernel

theorem rowEval7489 (x : Key → ℝ) : Integer.Sparse.eval row7489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7489, Integer.Sparse.eval_collectBalanced, rawRowCheck7489]

theorem rawRowCheck7490 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form3 = rawRow7490 := by decide +kernel

theorem rowCheck7490 : row7490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7490 := by decide +kernel

theorem rowEval7490 (x : Key → ℝ) : Integer.Sparse.eval row7490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7490, Integer.Sparse.eval_collectBalanced, rawRowCheck7490]

theorem rawRowCheck7491 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form3 = rawRow7491 := by decide +kernel

theorem rowCheck7491 : row7491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7491 := by decide +kernel

theorem rowEval7491 (x : Key → ℝ) : Integer.Sparse.eval row7491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7491, Integer.Sparse.eval_collectBalanced, rawRowCheck7491]

theorem rawRowCheck7492 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form3 = rawRow7492 := by decide +kernel

theorem rowCheck7492 : row7492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7492 := by decide +kernel

theorem rowEval7492 (x : Key → ℝ) : Integer.Sparse.eval row7492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7492, Integer.Sparse.eval_collectBalanced, rawRowCheck7492]

theorem rawRowCheck7493 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form3 = rawRow7493 := by decide +kernel

theorem rowCheck7493 : row7493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7493 := by decide +kernel

theorem rowEval7493 (x : Key → ℝ) : Integer.Sparse.eval row7493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7493, Integer.Sparse.eval_collectBalanced, rawRowCheck7493]

theorem rawRowCheck7542 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7542 := by decide +kernel

theorem rowCheck7542 : row7542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7542 := by decide +kernel

theorem rowEval7542 (x : Key → ℝ) : Integer.Sparse.eval row7542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7542, Integer.Sparse.eval_collectBalanced, rawRowCheck7542]

theorem rawRowCheck7543 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7543 := by decide +kernel

theorem rowCheck7543 : row7543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7543 := by decide +kernel

theorem rowEval7543 (x : Key → ℝ) : Integer.Sparse.eval row7543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7543, Integer.Sparse.eval_collectBalanced, rawRowCheck7543]

theorem rawRowCheck7544 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7544 := by decide +kernel

theorem rowCheck7544 : row7544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7544 := by decide +kernel

theorem rowEval7544 (x : Key → ℝ) : Integer.Sparse.eval row7544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7544, Integer.Sparse.eval_collectBalanced, rawRowCheck7544]

theorem rawRowCheck7545 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7545 := by decide +kernel

theorem rowCheck7545 : row7545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7545 := by decide +kernel

theorem rowEval7545 (x : Key → ℝ) : Integer.Sparse.eval row7545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7545, Integer.Sparse.eval_collectBalanced, rawRowCheck7545]

theorem rawRowCheck7546 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7546 := by decide +kernel

theorem rowCheck7546 : row7546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7546 := by decide +kernel

theorem rowEval7546 (x : Key → ℝ) : Integer.Sparse.eval row7546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7546, Integer.Sparse.eval_collectBalanced, rawRowCheck7546]

theorem rawRowCheck7547 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7547 := by decide +kernel

theorem rowCheck7547 : row7547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7547 := by decide +kernel

theorem rowEval7547 (x : Key → ℝ) : Integer.Sparse.eval row7547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7547, Integer.Sparse.eval_collectBalanced, rawRowCheck7547]

theorem rawRowCheck7548 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7548 := by decide +kernel

theorem rowCheck7548 : row7548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7548 := by decide +kernel

theorem rowEval7548 (x : Key → ℝ) : Integer.Sparse.eval row7548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7548, Integer.Sparse.eval_collectBalanced, rawRowCheck7548]

theorem rawRowCheck7549 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form3 = rawRow7549 := by decide +kernel

theorem rowCheck7549 : row7549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7549 := by decide +kernel

theorem rowEval7549 (x : Key → ℝ) : Integer.Sparse.eval row7549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7549, Integer.Sparse.eval_collectBalanced, rawRowCheck7549]

theorem rawRowCheck7550 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form3 = rawRow7550 := by decide +kernel

theorem rowCheck7550 : row7550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7550 := by decide +kernel

theorem rowEval7550 (x : Key → ℝ) : Integer.Sparse.eval row7550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7550, Integer.Sparse.eval_collectBalanced, rawRowCheck7550]

theorem rawRowCheck7551 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form3 = rawRow7551 := by decide +kernel

theorem rowCheck7551 : row7551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7551 := by decide +kernel

theorem rowEval7551 (x : Key → ℝ) : Integer.Sparse.eval row7551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7551, Integer.Sparse.eval_collectBalanced, rawRowCheck7551]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7552 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form3 = rawRow7552 := by decide +kernel

theorem rowCheck7552 : row7552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7552 := by decide +kernel

theorem rowEval7552 (x : Key → ℝ) : Integer.Sparse.eval row7552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7552, Integer.Sparse.eval_collectBalanced, rawRowCheck7552]

theorem rawRowCheck7553 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form3 = rawRow7553 := by decide +kernel

theorem rowCheck7553 : row7553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7553 := by decide +kernel

theorem rowEval7553 (x : Key → ℝ) : Integer.Sparse.eval row7553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7553, Integer.Sparse.eval_collectBalanced, rawRowCheck7553]

theorem rawRowCheck7554 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form3 = rawRow7554 := by decide +kernel

theorem rowCheck7554 : row7554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7554 := by decide +kernel

theorem rowEval7554 (x : Key → ℝ) : Integer.Sparse.eval row7554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7554, Integer.Sparse.eval_collectBalanced, rawRowCheck7554]

theorem rawRowCheck7555 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form3 = rawRow7555 := by decide +kernel

theorem rowCheck7555 : row7555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7555 := by decide +kernel

theorem rowEval7555 (x : Key → ℝ) : Integer.Sparse.eval row7555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7555, Integer.Sparse.eval_collectBalanced, rawRowCheck7555]

theorem rawRowCheck7556 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form3 = rawRow7556 := by decide +kernel

theorem rowCheck7556 : row7556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7556 := by decide +kernel

theorem rowEval7556 (x : Key → ℝ) : Integer.Sparse.eval row7556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7556, Integer.Sparse.eval_collectBalanced, rawRowCheck7556]

theorem rawRowCheck7557 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form3 = rawRow7557 := by decide +kernel

theorem rowCheck7557 : row7557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7557 := by decide +kernel

theorem rowEval7557 (x : Key → ℝ) : Integer.Sparse.eval row7557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7557, Integer.Sparse.eval_collectBalanced, rawRowCheck7557]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8889 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow8889 := by decide +kernel

theorem rowCheck8889 : row8889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8889 := by decide +kernel

theorem rowEval8889 (x : Key → ℝ) : Integer.Sparse.eval row8889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8889, Integer.Sparse.eval_collectBalanced, rawRowCheck8889]

theorem rawRowCheck8890 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow8890 := by decide +kernel

theorem rowCheck8890 : row8890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8890 := by decide +kernel

theorem rowEval8890 (x : Key → ℝ) : Integer.Sparse.eval row8890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8890, Integer.Sparse.eval_collectBalanced, rawRowCheck8890]

theorem rawRowCheck8891 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow8891 := by decide +kernel

theorem rowCheck8891 : row8891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8891 := by decide +kernel

theorem rowEval8891 (x : Key → ℝ) : Integer.Sparse.eval row8891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8891, Integer.Sparse.eval_collectBalanced, rawRowCheck8891]

theorem rawRowCheck8892 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8892 := by decide +kernel

theorem rowCheck8892 : row8892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8892 := by decide +kernel

theorem rowEval8892 (x : Key → ℝ) : Integer.Sparse.eval row8892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8892, Integer.Sparse.eval_collectBalanced, rawRowCheck8892]

theorem rawRowCheck8893 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form3 = rawRow8893 := by decide +kernel

theorem rowCheck8893 : row8893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8893 := by decide +kernel

theorem rowEval8893 (x : Key → ℝ) : Integer.Sparse.eval row8893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8893, Integer.Sparse.eval_collectBalanced, rawRowCheck8893]

theorem rawRowCheck8894 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form3 = rawRow8894 := by decide +kernel

theorem rowCheck8894 : row8894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8894 := by decide +kernel

theorem rowEval8894 (x : Key → ℝ) : Integer.Sparse.eval row8894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8894, Integer.Sparse.eval_collectBalanced, rawRowCheck8894]

theorem rawRowCheck8895 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form3 = rawRow8895 := by decide +kernel

theorem rowCheck8895 : row8895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8895 := by decide +kernel

theorem rowEval8895 (x : Key → ℝ) : Integer.Sparse.eval row8895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8895, Integer.Sparse.eval_collectBalanced, rawRowCheck8895]

theorem rawRowCheck8896 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form3 = rawRow8896 := by decide +kernel

theorem rowCheck8896 : row8896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8896 := by decide +kernel

theorem rowEval8896 (x : Key → ℝ) : Integer.Sparse.eval row8896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8896, Integer.Sparse.eval_collectBalanced, rawRowCheck8896]

theorem rawRowCheck8897 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form3 = rawRow8897 := by decide +kernel

theorem rowCheck8897 : row8897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8897 := by decide +kernel

theorem rowEval8897 (x : Key → ℝ) : Integer.Sparse.eval row8897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8897, Integer.Sparse.eval_collectBalanced, rawRowCheck8897]

theorem rawRowCheck8898 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form3 = rawRow8898 := by decide +kernel

theorem rowCheck8898 : row8898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8898 := by decide +kernel

theorem rowEval8898 (x : Key → ℝ) : Integer.Sparse.eval row8898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8898, Integer.Sparse.eval_collectBalanced, rawRowCheck8898]

theorem rawRowCheck8899 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form3 = rawRow8899 := by decide +kernel

theorem rowCheck8899 : row8899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8899 := by decide +kernel

theorem rowEval8899 (x : Key → ℝ) : Integer.Sparse.eval row8899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8899, Integer.Sparse.eval_collectBalanced, rawRowCheck8899]

theorem rawRowCheck8900 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form3 = rawRow8900 := by decide +kernel

theorem rowCheck8900 : row8900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8900 := by decide +kernel

theorem rowEval8900 (x : Key → ℝ) : Integer.Sparse.eval row8900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8900, Integer.Sparse.eval_collectBalanced, rawRowCheck8900]

theorem rawRowCheck8901 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form3 = rawRow8901 := by decide +kernel

theorem rowCheck8901 : row8901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8901 := by decide +kernel

theorem rowEval8901 (x : Key → ℝ) : Integer.Sparse.eval row8901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8901, Integer.Sparse.eval_collectBalanced, rawRowCheck8901]

theorem rawRowCheck8902 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow8902 := by decide +kernel

theorem rowCheck8902 : row8902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8902 := by decide +kernel

theorem rowEval8902 (x : Key → ℝ) : Integer.Sparse.eval row8902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8902, Integer.Sparse.eval_collectBalanced, rawRowCheck8902]

theorem rawRowCheck8903 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow8903 := by decide +kernel

theorem rowCheck8903 : row8903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8903 := by decide +kernel

theorem rowEval8903 (x : Key → ℝ) : Integer.Sparse.eval row8903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8903, Integer.Sparse.eval_collectBalanced, rawRowCheck8903]

theorem rawRowCheck8904 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow8904 := by decide +kernel

theorem rowCheck8904 : row8904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8904 := by decide +kernel

theorem rowEval8904 (x : Key → ℝ) : Integer.Sparse.eval row8904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8904, Integer.Sparse.eval_collectBalanced, rawRowCheck8904]

end MUB6.Certificate.GramRows

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

theorem entryCheck12_3 : entry12_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_3 k)) := by decide +kernel

theorem rowsSound12_3 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7542 x
  · exact rowEval7543 x
  · exact rowEval7544 x
  · exact rowEval7545 x
  · exact rowEval8769 x
  · exact rowEval8770 x
  · exact rowEval8771 x
  · exact rowEval8772 x

theorem entryEval12_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_3 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck12_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_3]

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

theorem rawRowCheck9077 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow9077 := by decide +kernel

theorem rowCheck9077 : row9077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9077 := by decide +kernel

theorem rowEval9077 (x : Key → ℝ) : Integer.Sparse.eval row9077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9077, Integer.Sparse.eval_collectBalanced, rawRowCheck9077]

theorem rawRowCheck9078 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow9078 := by decide +kernel

theorem rowCheck9078 : row9078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9078 := by decide +kernel

theorem rowEval9078 (x : Key → ℝ) : Integer.Sparse.eval row9078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9078, Integer.Sparse.eval_collectBalanced, rawRowCheck9078]

theorem rawRowCheck9079 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow9079 := by decide +kernel

theorem rowCheck9079 : row9079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9079 := by decide +kernel

theorem rowEval9079 (x : Key → ℝ) : Integer.Sparse.eval row9079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9079, Integer.Sparse.eval_collectBalanced, rawRowCheck9079]

theorem rawRowCheck9080 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9080 := by decide +kernel

theorem rowCheck9080 : row9080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9080 := by decide +kernel

theorem rowEval9080 (x : Key → ℝ) : Integer.Sparse.eval row9080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9080, Integer.Sparse.eval_collectBalanced, rawRowCheck9080]

theorem rawRowCheck9081 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9081 := by decide +kernel

theorem rowCheck9081 : row9081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9081 := by decide +kernel

theorem rowEval9081 (x : Key → ℝ) : Integer.Sparse.eval row9081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9081, Integer.Sparse.eval_collectBalanced, rawRowCheck9081]

theorem rawRowCheck9082 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow9082 := by decide +kernel

theorem rowCheck9082 : row9082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9082 := by decide +kernel

theorem rowEval9082 (x : Key → ℝ) : Integer.Sparse.eval row9082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9082, Integer.Sparse.eval_collectBalanced, rawRowCheck9082]

theorem rawRowCheck9083 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow9083 := by decide +kernel

theorem rowCheck9083 : row9083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9083 := by decide +kernel

theorem rowEval9083 (x : Key → ℝ) : Integer.Sparse.eval row9083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9083, Integer.Sparse.eval_collectBalanced, rawRowCheck9083]

theorem rawRowCheck9084 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow9084 := by decide +kernel

theorem rowCheck9084 : row9084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9084 := by decide +kernel

theorem rowEval9084 (x : Key → ℝ) : Integer.Sparse.eval row9084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9084, Integer.Sparse.eval_collectBalanced, rawRowCheck9084]

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

theorem entryCheck13_3 : entry13_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_3 k)) := by decide +kernel

theorem rowsSound13_3 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8889 x
  · exact rowEval8890 x
  · exact rowEval8891 x
  · exact rowEval8892 x
  · exact rowEval8893 x
  · exact rowEval8894 x
  · exact rowEval8895 x
  · exact rowEval8896 x
  · exact rowEval8897 x
  · exact rowEval8898 x
  · exact rowEval8899 x
  · exact rowEval8900 x
  · exact rowEval8901 x
  · exact rowEval8902 x
  · exact rowEval8903 x
  · exact rowEval8904 x

theorem entryEval13_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_3 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck13_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_3]

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

theorem rawRowCheck9209 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form3 = rawRow9209 := by decide +kernel

theorem rowCheck9209 : row9209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9209 := by decide +kernel

theorem rowEval9209 (x : Key → ℝ) : Integer.Sparse.eval row9209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9209, Integer.Sparse.eval_collectBalanced, rawRowCheck9209]

theorem rawRowCheck9210 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form3 = rawRow9210 := by decide +kernel

theorem rowCheck9210 : row9210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9210 := by decide +kernel

theorem rowEval9210 (x : Key → ℝ) : Integer.Sparse.eval row9210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9210, Integer.Sparse.eval_collectBalanced, rawRowCheck9210]

theorem rawRowCheck9211 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form3 = rawRow9211 := by decide +kernel

theorem rowCheck9211 : row9211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9211 := by decide +kernel

theorem rowEval9211 (x : Key → ℝ) : Integer.Sparse.eval row9211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9211, Integer.Sparse.eval_collectBalanced, rawRowCheck9211]

theorem rawRowCheck9212 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form3 = rawRow9212 := by decide +kernel

theorem rowCheck9212 : row9212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9212 := by decide +kernel

theorem rowEval9212 (x : Key → ℝ) : Integer.Sparse.eval row9212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9212, Integer.Sparse.eval_collectBalanced, rawRowCheck9212]

theorem rawRowCheck9213 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form3 = rawRow9213 := by decide +kernel

theorem rowCheck9213 : row9213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9213 := by decide +kernel

theorem rowEval9213 (x : Key → ℝ) : Integer.Sparse.eval row9213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9213, Integer.Sparse.eval_collectBalanced, rawRowCheck9213]

theorem rawRowCheck9214 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form3 = rawRow9214 := by decide +kernel

theorem rowCheck9214 : row9214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9214 := by decide +kernel

theorem rowEval9214 (x : Key → ℝ) : Integer.Sparse.eval row9214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9214, Integer.Sparse.eval_collectBalanced, rawRowCheck9214]

theorem rawRowCheck9215 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form3 = rawRow9215 := by decide +kernel

theorem rowCheck9215 : row9215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9215 := by decide +kernel

theorem rowEval9215 (x : Key → ℝ) : Integer.Sparse.eval row9215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9215, Integer.Sparse.eval_collectBalanced, rawRowCheck9215]

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

theorem entryCheck14_3 : entry14_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_3 k)) := by decide +kernel

theorem rowsSound14_3 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval9077 x
  · exact rowEval9078 x
  · exact rowEval9079 x
  · exact rowEval9080 x
  · exact rowEval9081 x
  · exact rowEval9082 x
  · exact rowEval9083 x
  · exact rowEval9084 x

theorem entryEval14_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_3 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck14_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_3]

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

theorem rawRowCheck9216 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form3 = rawRow9216 := by decide +kernel

theorem rowCheck9216 : row9216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9216 := by decide +kernel

theorem rowEval9216 (x : Key → ℝ) : Integer.Sparse.eval row9216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9216, Integer.Sparse.eval_collectBalanced, rawRowCheck9216]

theorem rawRowCheck9217 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form3 = rawRow9217 := by decide +kernel

theorem rowCheck9217 : row9217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9217 := by decide +kernel

theorem rowEval9217 (x : Key → ℝ) : Integer.Sparse.eval row9217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9217, Integer.Sparse.eval_collectBalanced, rawRowCheck9217]

theorem rawRowCheck9218 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form3 = rawRow9218 := by decide +kernel

theorem rowCheck9218 : row9218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9218 := by decide +kernel

theorem rowEval9218 (x : Key → ℝ) : Integer.Sparse.eval row9218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9218, Integer.Sparse.eval_collectBalanced, rawRowCheck9218]

theorem rawRowCheck9219 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form3 = rawRow9219 := by decide +kernel

theorem rowCheck9219 : row9219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9219 := by decide +kernel

theorem rowEval9219 (x : Key → ℝ) : Integer.Sparse.eval row9219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9219, Integer.Sparse.eval_collectBalanced, rawRowCheck9219]

theorem rawRowCheck9220 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form3 = rawRow9220 := by decide +kernel

theorem rowCheck9220 : row9220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9220 := by decide +kernel

theorem rowEval9220 (x : Key → ℝ) : Integer.Sparse.eval row9220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9220, Integer.Sparse.eval_collectBalanced, rawRowCheck9220]

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

theorem rawRowCheck9393 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9393 := by decide +kernel

theorem rowCheck9393 : row9393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9393 := by decide +kernel

theorem rowEval9393 (x : Key → ℝ) : Integer.Sparse.eval row9393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9393, Integer.Sparse.eval_collectBalanced, rawRowCheck9393]

theorem rawRowCheck9394 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form3 = rawRow9394 := by decide +kernel

theorem rowCheck9394 : row9394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9394 := by decide +kernel

theorem rowEval9394 (x : Key → ℝ) : Integer.Sparse.eval row9394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9394, Integer.Sparse.eval_collectBalanced, rawRowCheck9394]

theorem rawRowCheck9395 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form3 = rawRow9395 := by decide +kernel

theorem rowCheck9395 : row9395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9395 := by decide +kernel

theorem rowEval9395 (x : Key → ℝ) : Integer.Sparse.eval row9395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9395, Integer.Sparse.eval_collectBalanced, rawRowCheck9395]

theorem rawRowCheck9396 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form3 = rawRow9396 := by decide +kernel

theorem rowCheck9396 : row9396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9396 := by decide +kernel

theorem rowEval9396 (x : Key → ℝ) : Integer.Sparse.eval row9396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9396, Integer.Sparse.eval_collectBalanced, rawRowCheck9396]

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

theorem entryCheck15_3 : entry15_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_3 k)) := by decide +kernel

theorem rowsSound15_3 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8685 x
  · exact rowEval8686 x
  · exact rowEval8687 x
  · exact rowEval8688 x
  · exact rowEval9209 x
  · exact rowEval9210 x
  · exact rowEval9211 x
  · exact rowEval9212 x
  · exact rowEval9213 x
  · exact rowEval9214 x
  · exact rowEval9215 x
  · exact rowEval9216 x
  · exact rowEval9217 x
  · exact rowEval9218 x
  · exact rowEval9219 x
  · exact rowEval9220 x

theorem entryEval15_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_3 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck15_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9573 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form3 = rawRow9573 := by decide +kernel

theorem rowCheck9573 : row9573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9573 := by decide +kernel

theorem rowEval9573 (x : Key → ℝ) : Integer.Sparse.eval row9573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9573, Integer.Sparse.eval_collectBalanced, rawRowCheck9573]

theorem rawRowCheck9574 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form3 = rawRow9574 := by decide +kernel

theorem rowCheck9574 : row9574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9574 := by decide +kernel

theorem rowEval9574 (x : Key → ℝ) : Integer.Sparse.eval row9574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9574, Integer.Sparse.eval_collectBalanced, rawRowCheck9574]

theorem rawRowCheck9575 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form3 = rawRow9575 := by decide +kernel

theorem rowCheck9575 : row9575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9575 := by decide +kernel

theorem rowEval9575 (x : Key → ℝ) : Integer.Sparse.eval row9575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9575, Integer.Sparse.eval_collectBalanced, rawRowCheck9575]

theorem rawRowCheck9576 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form3 = rawRow9576 := by decide +kernel

theorem rowCheck9576 : row9576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9576 := by decide +kernel

theorem rowEval9576 (x : Key → ℝ) : Integer.Sparse.eval row9576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9576, Integer.Sparse.eval_collectBalanced, rawRowCheck9576]

theorem rawRowCheck9577 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form3 = rawRow9577 := by decide +kernel

theorem rowCheck9577 : row9577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9577 := by decide +kernel

theorem rowEval9577 (x : Key → ℝ) : Integer.Sparse.eval row9577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9577, Integer.Sparse.eval_collectBalanced, rawRowCheck9577]

theorem rawRowCheck9578 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form3 = rawRow9578 := by decide +kernel

theorem rowCheck9578 : row9578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9578 := by decide +kernel

theorem rowEval9578 (x : Key → ℝ) : Integer.Sparse.eval row9578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9578, Integer.Sparse.eval_collectBalanced, rawRowCheck9578]

theorem rawRowCheck9579 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form3 = rawRow9579 := by decide +kernel

theorem rowCheck9579 : row9579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9579 := by decide +kernel

theorem rowEval9579 (x : Key → ℝ) : Integer.Sparse.eval row9579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9579, Integer.Sparse.eval_collectBalanced, rawRowCheck9579]

theorem rawRowCheck9580 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form3 = rawRow9580 := by decide +kernel

theorem rowCheck9580 : row9580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9580 := by decide +kernel

theorem rowEval9580 (x : Key → ℝ) : Integer.Sparse.eval row9580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9580, Integer.Sparse.eval_collectBalanced, rawRowCheck9580]

theorem rawRowCheck9581 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form3 = rawRow9581 := by decide +kernel

theorem rowCheck9581 : row9581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9581 := by decide +kernel

theorem rowEval9581 (x : Key → ℝ) : Integer.Sparse.eval row9581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9581, Integer.Sparse.eval_collectBalanced, rawRowCheck9581]

theorem rawRowCheck9582 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form3 = rawRow9582 := by decide +kernel

theorem rowCheck9582 : row9582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9582 := by decide +kernel

theorem rowEval9582 (x : Key → ℝ) : Integer.Sparse.eval row9582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9582, Integer.Sparse.eval_collectBalanced, rawRowCheck9582]

theorem rawRowCheck9583 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form3 = rawRow9583 := by decide +kernel

theorem rowCheck9583 : row9583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9583 := by decide +kernel

theorem rowEval9583 (x : Key → ℝ) : Integer.Sparse.eval row9583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9583, Integer.Sparse.eval_collectBalanced, rawRowCheck9583]

theorem rawRowCheck9584 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form3 = rawRow9584 := by decide +kernel

theorem rowCheck9584 : row9584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9584 := by decide +kernel

theorem rowEval9584 (x : Key → ℝ) : Integer.Sparse.eval row9584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9584, Integer.Sparse.eval_collectBalanced, rawRowCheck9584]

theorem rawRowCheck9585 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form3 = rawRow9585 := by decide +kernel

theorem rowCheck9585 : row9585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9585 := by decide +kernel

theorem rowEval9585 (x : Key → ℝ) : Integer.Sparse.eval row9585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9585, Integer.Sparse.eval_collectBalanced, rawRowCheck9585]

theorem rawRowCheck9586 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form3 = rawRow9586 := by decide +kernel

theorem rowCheck9586 : row9586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9586 := by decide +kernel

theorem rowEval9586 (x : Key → ℝ) : Integer.Sparse.eval row9586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9586, Integer.Sparse.eval_collectBalanced, rawRowCheck9586]

theorem rawRowCheck9587 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form3 = rawRow9587 := by decide +kernel

theorem rowCheck9587 : row9587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9587 := by decide +kernel

theorem rowEval9587 (x : Key → ℝ) : Integer.Sparse.eval row9587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9587, Integer.Sparse.eval_collectBalanced, rawRowCheck9587]

theorem rawRowCheck9588 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form3 = rawRow9588 := by decide +kernel

theorem rowCheck9588 : row9588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9588 := by decide +kernel

theorem rowEval9588 (x : Key → ℝ) : Integer.Sparse.eval row9588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9588, Integer.Sparse.eval_collectBalanced, rawRowCheck9588]

theorem rawRowCheck9589 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form3 = rawRow9589 := by decide +kernel

theorem rowCheck9589 : row9589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9589 := by decide +kernel

theorem rowEval9589 (x : Key → ℝ) : Integer.Sparse.eval row9589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9589, Integer.Sparse.eval_collectBalanced, rawRowCheck9589]

theorem rawRowCheck9590 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form3 = rawRow9590 := by decide +kernel

theorem rowCheck9590 : row9590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9590 := by decide +kernel

theorem rowEval9590 (x : Key → ℝ) : Integer.Sparse.eval row9590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9590, Integer.Sparse.eval_collectBalanced, rawRowCheck9590]

theorem rawRowCheck9591 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form3 = rawRow9591 := by decide +kernel

theorem rowCheck9591 : row9591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9591 := by decide +kernel

theorem rowEval9591 (x : Key → ℝ) : Integer.Sparse.eval row9591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9591, Integer.Sparse.eval_collectBalanced, rawRowCheck9591]

theorem rawRowCheck9592 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form3 = rawRow9592 := by decide +kernel

theorem rowCheck9592 : row9592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9592 := by decide +kernel

theorem rowEval9592 (x : Key → ℝ) : Integer.Sparse.eval row9592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9592, Integer.Sparse.eval_collectBalanced, rawRowCheck9592]

theorem rawRowCheck9593 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form3 = rawRow9593 := by decide +kernel

theorem rowCheck9593 : row9593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9593 := by decide +kernel

theorem rowEval9593 (x : Key → ℝ) : Integer.Sparse.eval row9593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9593, Integer.Sparse.eval_collectBalanced, rawRowCheck9593]

theorem rawRowCheck9594 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form3 = rawRow9594 := by decide +kernel

theorem rowCheck9594 : row9594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9594 := by decide +kernel

theorem rowEval9594 (x : Key → ℝ) : Integer.Sparse.eval row9594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9594, Integer.Sparse.eval_collectBalanced, rawRowCheck9594]

theorem rawRowCheck9595 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form3 = rawRow9595 := by decide +kernel

theorem rowCheck9595 : row9595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9595 := by decide +kernel

theorem rowEval9595 (x : Key → ℝ) : Integer.Sparse.eval row9595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9595, Integer.Sparse.eval_collectBalanced, rawRowCheck9595]

theorem rawRowCheck9596 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form3 = rawRow9596 := by decide +kernel

theorem rowCheck9596 : row9596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9596 := by decide +kernel

theorem rowEval9596 (x : Key → ℝ) : Integer.Sparse.eval row9596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9596, Integer.Sparse.eval_collectBalanced, rawRowCheck9596]

end MUB6.Certificate.GramRows

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

theorem entryCheck16_3 : entry16_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_3 k)) := by decide +kernel

theorem rowsSound16_3 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval9393 x
  · exact rowEval9394 x
  · exact rowEval9395 x
  · exact rowEval9396 x
  · exact rowEval7478 x
  · exact rowEval7479 x
  · exact rowEval7480 x
  · exact rowEval7481 x

theorem entryEval16_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_3 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck16_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck17_3 : entry17_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_3 k)) := by decide +kernel

theorem rowsSound17_3 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval9573 x
  · exact rowEval9574 x
  · exact rowEval9575 x
  · exact rowEval9576 x
  · exact rowEval9577 x
  · exact rowEval9578 x
  · exact rowEval9579 x
  · exact rowEval9580 x
  · exact rowEval9581 x
  · exact rowEval9582 x
  · exact rowEval9583 x
  · exact rowEval9584 x
  · exact rowEval9585 x
  · exact rowEval9586 x
  · exact rowEval9587 x
  · exact rowEval9588 x
  · exact rowEval9589 x
  · exact rowEval9590 x
  · exact rowEval9591 x
  · exact rowEval9592 x
  · exact rowEval9593 x
  · exact rowEval9594 x
  · exact rowEval9595 x
  · exact rowEval9596 x

theorem entryEval17_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_3 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck17_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_3]

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

theorem rawRowCheck10419 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form3 = rawRow10419 := by decide +kernel

theorem rowCheck10419 : row10419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10419 := by decide +kernel

theorem rowEval10419 (x : Key → ℝ) : Integer.Sparse.eval row10419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10419, Integer.Sparse.eval_collectBalanced, rawRowCheck10419]

theorem rawRowCheck10420 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form3 = rawRow10420 := by decide +kernel

theorem rowCheck10420 : row10420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10420 := by decide +kernel

theorem rowEval10420 (x : Key → ℝ) : Integer.Sparse.eval row10420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10420, Integer.Sparse.eval_collectBalanced, rawRowCheck10420]

theorem rawRowCheck10421 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form3 = rawRow10421 := by decide +kernel

theorem rowCheck10421 : row10421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10421 := by decide +kernel

theorem rowEval10421 (x : Key → ℝ) : Integer.Sparse.eval row10421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10421, Integer.Sparse.eval_collectBalanced, rawRowCheck10421]

theorem rawRowCheck10422 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form3 = rawRow10422 := by decide +kernel

theorem rowCheck10422 : row10422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10422 := by decide +kernel

theorem rowEval10422 (x : Key → ℝ) : Integer.Sparse.eval row10422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10422, Integer.Sparse.eval_collectBalanced, rawRowCheck10422]

theorem rawRowCheck10423 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form3 = rawRow10423 := by decide +kernel

theorem rowCheck10423 : row10423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10423 := by decide +kernel

theorem rowEval10423 (x : Key → ℝ) : Integer.Sparse.eval row10423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10423, Integer.Sparse.eval_collectBalanced, rawRowCheck10423]

theorem rawRowCheck10424 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form3 = rawRow10424 := by decide +kernel

theorem rowCheck10424 : row10424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10424 := by decide +kernel

theorem rowEval10424 (x : Key → ℝ) : Integer.Sparse.eval row10424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10424, Integer.Sparse.eval_collectBalanced, rawRowCheck10424]

theorem rawRowCheck10425 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form3 = rawRow10425 := by decide +kernel

theorem rowCheck10425 : row10425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10425 := by decide +kernel

theorem rowEval10425 (x : Key → ℝ) : Integer.Sparse.eval row10425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10425, Integer.Sparse.eval_collectBalanced, rawRowCheck10425]

theorem rawRowCheck10426 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form3 = rawRow10426 := by decide +kernel

theorem rowCheck10426 : row10426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10426 := by decide +kernel

theorem rowEval10426 (x : Key → ℝ) : Integer.Sparse.eval row10426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10426, Integer.Sparse.eval_collectBalanced, rawRowCheck10426]

theorem rawRowCheck10427 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form3 = rawRow10427 := by decide +kernel

theorem rowCheck10427 : row10427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10427 := by decide +kernel

theorem rowEval10427 (x : Key → ℝ) : Integer.Sparse.eval row10427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10427, Integer.Sparse.eval_collectBalanced, rawRowCheck10427]

theorem rawRowCheck10428 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form3 = rawRow10428 := by decide +kernel

theorem rowCheck10428 : row10428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10428 := by decide +kernel

theorem rowEval10428 (x : Key → ℝ) : Integer.Sparse.eval row10428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10428, Integer.Sparse.eval_collectBalanced, rawRowCheck10428]

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

theorem rawRowCheck10604 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow10604 := by decide +kernel

theorem rowCheck10604 : row10604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10604 := by decide +kernel

theorem rowEval10604 (x : Key → ℝ) : Integer.Sparse.eval row10604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10604, Integer.Sparse.eval_collectBalanced, rawRowCheck10604]

theorem rawRowCheck10605 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow10605 := by decide +kernel

theorem rowCheck10605 : row10605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10605 := by decide +kernel

theorem rowEval10605 (x : Key → ℝ) : Integer.Sparse.eval row10605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10605, Integer.Sparse.eval_collectBalanced, rawRowCheck10605]

theorem rawRowCheck10606 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow10606 := by decide +kernel

theorem rowCheck10606 : row10606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10606 := by decide +kernel

theorem rowEval10606 (x : Key → ℝ) : Integer.Sparse.eval row10606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10606, Integer.Sparse.eval_collectBalanced, rawRowCheck10606]

theorem rawRowCheck10607 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow10607 := by decide +kernel

theorem rowCheck10607 : row10607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10607 := by decide +kernel

theorem rowEval10607 (x : Key → ℝ) : Integer.Sparse.eval row10607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10607, Integer.Sparse.eval_collectBalanced, rawRowCheck10607]

theorem rawRowCheck10608 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow10608 := by decide +kernel

theorem rowCheck10608 : row10608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10608 := by decide +kernel

theorem rowEval10608 (x : Key → ℝ) : Integer.Sparse.eval row10608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10608, Integer.Sparse.eval_collectBalanced, rawRowCheck10608]

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

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval10419 x
  · exact rowEval10420 x
  · exact rowEval10421 x
  · exact rowEval10422 x
  · exact rowEval10423 x
  · exact rowEval10424 x
  · exact rowEval10425 x
  · exact rowEval10426 x
  · exact rowEval10427 x
  · exact rowEval10428 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

end MUB6.Certificate.GramEntries.Block3

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

theorem entryCheck20_3 : entry20_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_3 k)) := by decide +kernel

theorem rowsSound20_3 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval10604 x
  · exact rowEval10605 x
  · exact rowEval10606 x
  · exact rowEval10607 x
  · exact rowEval10608 x

theorem entryEval20_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_3 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck20_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10802 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form3 = rawRow10802 := by decide +kernel

theorem rowCheck10802 : row10802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10802 := by decide +kernel

theorem rowEval10802 (x : Key → ℝ) : Integer.Sparse.eval row10802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10802, Integer.Sparse.eval_collectBalanced, rawRowCheck10802]

theorem rawRowCheck10803 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form3 = rawRow10803 := by decide +kernel

theorem rowCheck10803 : row10803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10803 := by decide +kernel

theorem rowEval10803 (x : Key → ℝ) : Integer.Sparse.eval row10803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10803, Integer.Sparse.eval_collectBalanced, rawRowCheck10803]

theorem rawRowCheck10804 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form3 = rawRow10804 := by decide +kernel

theorem rowCheck10804 : row10804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10804 := by decide +kernel

theorem rowEval10804 (x : Key → ℝ) : Integer.Sparse.eval row10804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10804, Integer.Sparse.eval_collectBalanced, rawRowCheck10804]

theorem rawRowCheck10805 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form3 = rawRow10805 := by decide +kernel

theorem rowCheck10805 : row10805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10805 := by decide +kernel

theorem rowEval10805 (x : Key → ℝ) : Integer.Sparse.eval row10805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10805, Integer.Sparse.eval_collectBalanced, rawRowCheck10805]

theorem rawRowCheck10806 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form3 = rawRow10806 := by decide +kernel

theorem rowCheck10806 : row10806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10806 := by decide +kernel

theorem rowEval10806 (x : Key → ℝ) : Integer.Sparse.eval row10806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10806, Integer.Sparse.eval_collectBalanced, rawRowCheck10806]

theorem rawRowCheck10807 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form3 = rawRow10807 := by decide +kernel

theorem rowCheck10807 : row10807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10807 := by decide +kernel

theorem rowEval10807 (x : Key → ℝ) : Integer.Sparse.eval row10807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10807, Integer.Sparse.eval_collectBalanced, rawRowCheck10807]

theorem rawRowCheck10808 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form3 = rawRow10808 := by decide +kernel

theorem rowCheck10808 : row10808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10808 := by decide +kernel

theorem rowEval10808 (x : Key → ℝ) : Integer.Sparse.eval row10808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10808, Integer.Sparse.eval_collectBalanced, rawRowCheck10808]

theorem rawRowCheck10809 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form3 = rawRow10809 := by decide +kernel

theorem rowCheck10809 : row10809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10809 := by decide +kernel

theorem rowEval10809 (x : Key → ℝ) : Integer.Sparse.eval row10809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10809, Integer.Sparse.eval_collectBalanced, rawRowCheck10809]

theorem rawRowCheck10810 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form3 = rawRow10810 := by decide +kernel

theorem rowCheck10810 : row10810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10810 := by decide +kernel

theorem rowEval10810 (x : Key → ℝ) : Integer.Sparse.eval row10810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10810, Integer.Sparse.eval_collectBalanced, rawRowCheck10810]

theorem rawRowCheck10811 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form3 = rawRow10811 := by decide +kernel

theorem rowCheck10811 : row10811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10811 := by decide +kernel

theorem rowEval10811 (x : Key → ℝ) : Integer.Sparse.eval row10811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10811, Integer.Sparse.eval_collectBalanced, rawRowCheck10811]

theorem rawRowCheck10812 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form3 = rawRow10812 := by decide +kernel

theorem rowCheck10812 : row10812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10812 := by decide +kernel

theorem rowEval10812 (x : Key → ℝ) : Integer.Sparse.eval row10812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10812, Integer.Sparse.eval_collectBalanced, rawRowCheck10812]

theorem rawRowCheck10813 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form3 = rawRow10813 := by decide +kernel

theorem rowCheck10813 : row10813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10813 := by decide +kernel

theorem rowEval10813 (x : Key → ℝ) : Integer.Sparse.eval row10813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10813, Integer.Sparse.eval_collectBalanced, rawRowCheck10813]

theorem rawRowCheck10814 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form3 = rawRow10814 := by decide +kernel

theorem rowCheck10814 : row10814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10814 := by decide +kernel

theorem rowEval10814 (x : Key → ℝ) : Integer.Sparse.eval row10814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10814, Integer.Sparse.eval_collectBalanced, rawRowCheck10814]

theorem rawRowCheck10815 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form3 = rawRow10815 := by decide +kernel

theorem rowCheck10815 : row10815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10815 := by decide +kernel

theorem rowEval10815 (x : Key → ℝ) : Integer.Sparse.eval row10815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10815, Integer.Sparse.eval_collectBalanced, rawRowCheck10815]

theorem rawRowCheck10816 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form3 = rawRow10816 := by decide +kernel

theorem rowCheck10816 : row10816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10816 := by decide +kernel

theorem rowEval10816 (x : Key → ℝ) : Integer.Sparse.eval row10816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10816, Integer.Sparse.eval_collectBalanced, rawRowCheck10816]

theorem rawRowCheck10817 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form3 = rawRow10817 := by decide +kernel

theorem rowCheck10817 : row10817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10817 := by decide +kernel

theorem rowEval10817 (x : Key → ℝ) : Integer.Sparse.eval row10817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10817, Integer.Sparse.eval_collectBalanced, rawRowCheck10817]

theorem rawRowCheck10818 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form3 = rawRow10818 := by decide +kernel

theorem rowCheck10818 : row10818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10818 := by decide +kernel

theorem rowEval10818 (x : Key → ℝ) : Integer.Sparse.eval row10818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10818, Integer.Sparse.eval_collectBalanced, rawRowCheck10818]

theorem rawRowCheck10819 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form3 = rawRow10819 := by decide +kernel

theorem rowCheck10819 : row10819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10819 := by decide +kernel

theorem rowEval10819 (x : Key → ℝ) : Integer.Sparse.eval row10819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10819, Integer.Sparse.eval_collectBalanced, rawRowCheck10819]

theorem rawRowCheck10820 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form3 = rawRow10820 := by decide +kernel

theorem rowCheck10820 : row10820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10820 := by decide +kernel

theorem rowEval10820 (x : Key → ℝ) : Integer.Sparse.eval row10820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10820, Integer.Sparse.eval_collectBalanced, rawRowCheck10820]

theorem rawRowCheck10821 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form3 = rawRow10821 := by decide +kernel

theorem rowCheck10821 : row10821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10821 := by decide +kernel

theorem rowEval10821 (x : Key → ℝ) : Integer.Sparse.eval row10821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10821, Integer.Sparse.eval_collectBalanced, rawRowCheck10821]

theorem rawRowCheck10822 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form3 = rawRow10822 := by decide +kernel

theorem rowCheck10822 : row10822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10822 := by decide +kernel

theorem rowEval10822 (x : Key → ℝ) : Integer.Sparse.eval row10822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10822, Integer.Sparse.eval_collectBalanced, rawRowCheck10822]

theorem rawRowCheck10823 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form3 = rawRow10823 := by decide +kernel

theorem rowCheck10823 : row10823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10823 := by decide +kernel

theorem rowEval10823 (x : Key → ℝ) : Integer.Sparse.eval row10823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10823, Integer.Sparse.eval_collectBalanced, rawRowCheck10823]

theorem rawRowCheck10824 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form3 = rawRow10824 := by decide +kernel

theorem rowCheck10824 : row10824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10824 := by decide +kernel

theorem rowEval10824 (x : Key → ℝ) : Integer.Sparse.eval row10824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10824, Integer.Sparse.eval_collectBalanced, rawRowCheck10824]

theorem rawRowCheck10825 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form3 = rawRow10825 := by decide +kernel

theorem rowCheck10825 : row10825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10825 := by decide +kernel

theorem rowEval10825 (x : Key → ℝ) : Integer.Sparse.eval row10825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10825, Integer.Sparse.eval_collectBalanced, rawRowCheck10825]

theorem rawRowCheck10826 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow10826 := by decide +kernel

theorem rowCheck10826 : row10826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10826 := by decide +kernel

theorem rowEval10826 (x : Key → ℝ) : Integer.Sparse.eval row10826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10826, Integer.Sparse.eval_collectBalanced, rawRowCheck10826]

theorem rawRowCheck10827 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow10827 := by decide +kernel

theorem rowCheck10827 : row10827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10827 := by decide +kernel

theorem rowEval10827 (x : Key → ℝ) : Integer.Sparse.eval row10827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10827, Integer.Sparse.eval_collectBalanced, rawRowCheck10827]

theorem rawRowCheck10828 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow10828 := by decide +kernel

theorem rowCheck10828 : row10828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10828 := by decide +kernel

theorem rowEval10828 (x : Key → ℝ) : Integer.Sparse.eval row10828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10828, Integer.Sparse.eval_collectBalanced, rawRowCheck10828]

theorem rawRowCheck10829 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow10829 := by decide +kernel

theorem rowCheck10829 : row10829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10829 := by decide +kernel

theorem rowEval10829 (x : Key → ℝ) : Integer.Sparse.eval row10829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10829, Integer.Sparse.eval_collectBalanced, rawRowCheck10829]

theorem rawRowCheck10830 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow10830 := by decide +kernel

theorem rowCheck10830 : row10830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10830 := by decide +kernel

theorem rowEval10830 (x : Key → ℝ) : Integer.Sparse.eval row10830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10830, Integer.Sparse.eval_collectBalanced, rawRowCheck10830]

theorem rawRowCheck10831 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow10831 := by decide +kernel

theorem rowCheck10831 : row10831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10831 := by decide +kernel

theorem rowEval10831 (x : Key → ℝ) : Integer.Sparse.eval row10831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10831, Integer.Sparse.eval_collectBalanced, rawRowCheck10831]

theorem rawRowCheck10832 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form3 = rawRow10832 := by decide +kernel

theorem rowCheck10832 : row10832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10832 := by decide +kernel

theorem rowEval10832 (x : Key → ℝ) : Integer.Sparse.eval row10832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10832, Integer.Sparse.eval_collectBalanced, rawRowCheck10832]

theorem rawRowCheck10833 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form3 = rawRow10833 := by decide +kernel

theorem rowCheck10833 : row10833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10833 := by decide +kernel

theorem rowEval10833 (x : Key → ℝ) : Integer.Sparse.eval row10833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10833, Integer.Sparse.eval_collectBalanced, rawRowCheck10833]

theorem rawRowCheck10834 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form3 = rawRow10834 := by decide +kernel

theorem rowCheck10834 : row10834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10834 := by decide +kernel

theorem rowEval10834 (x : Key → ℝ) : Integer.Sparse.eval row10834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10834, Integer.Sparse.eval_collectBalanced, rawRowCheck10834]

theorem rawRowCheck10835 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form3 = rawRow10835 := by decide +kernel

theorem rowCheck10835 : row10835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10835 := by decide +kernel

theorem rowEval10835 (x : Key → ℝ) : Integer.Sparse.eval row10835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10835, Integer.Sparse.eval_collectBalanced, rawRowCheck10835]

theorem rawRowCheck10836 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form3 = rawRow10836 := by decide +kernel

theorem rowCheck10836 : row10836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10836 := by decide +kernel

theorem rowEval10836 (x : Key → ℝ) : Integer.Sparse.eval row10836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10836, Integer.Sparse.eval_collectBalanced, rawRowCheck10836]

theorem rawRowCheck10837 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form3 = rawRow10837 := by decide +kernel

theorem rowCheck10837 : row10837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10837 := by decide +kernel

theorem rowEval10837 (x : Key → ℝ) : Integer.Sparse.eval row10837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10837, Integer.Sparse.eval_collectBalanced, rawRowCheck10837]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck21_3 : entry21_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_3 k)) := by decide +kernel

theorem rowsSound21_3 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval10802 x
  · exact rowEval10803 x
  · exact rowEval10804 x
  · exact rowEval10805 x
  · exact rowEval10806 x
  · exact rowEval10807 x
  · exact rowEval10808 x
  · exact rowEval10809 x
  · exact rowEval10810 x
  · exact rowEval10811 x
  · exact rowEval10812 x
  · exact rowEval10813 x
  · exact rowEval10814 x
  · exact rowEval10815 x
  · exact rowEval10816 x
  · exact rowEval10817 x
  · exact rowEval10818 x
  · exact rowEval10819 x
  · exact rowEval10820 x
  · exact rowEval10821 x
  · exact rowEval10822 x
  · exact rowEval10823 x
  · exact rowEval10824 x
  · exact rowEval10825 x
  · exact rowEval10826 x
  · exact rowEval10827 x
  · exact rowEval10828 x
  · exact rowEval10829 x
  · exact rowEval10830 x
  · exact rowEval10831 x
  · exact rowEval10832 x
  · exact rowEval10833 x
  · exact rowEval10834 x
  · exact rowEval10835 x
  · exact rowEval10836 x
  · exact rowEval10837 x

theorem entryEval21_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_3 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck21_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_3]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck12221 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow12221 := by decide +kernel

theorem rowCheck12221 : row12221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12221 := by decide +kernel

theorem rowEval12221 (x : Key → ℝ) : Integer.Sparse.eval row12221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12221, Integer.Sparse.eval_collectBalanced, rawRowCheck12221]

theorem rawRowCheck12222 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow12222 := by decide +kernel

theorem rowCheck12222 : row12222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12222 := by decide +kernel

theorem rowEval12222 (x : Key → ℝ) : Integer.Sparse.eval row12222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12222, Integer.Sparse.eval_collectBalanced, rawRowCheck12222]

theorem rawRowCheck12223 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form3 = rawRow12223 := by decide +kernel

theorem rowCheck12223 : row12223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12223 := by decide +kernel

theorem rowEval12223 (x : Key → ℝ) : Integer.Sparse.eval row12223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12223, Integer.Sparse.eval_collectBalanced, rawRowCheck12223]

theorem rawRowCheck12224 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form3 = rawRow12224 := by decide +kernel

theorem rowCheck12224 : row12224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12224 := by decide +kernel

theorem rowEval12224 (x : Key → ℝ) : Integer.Sparse.eval row12224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12224, Integer.Sparse.eval_collectBalanced, rawRowCheck12224]

theorem rawRowCheck12225 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form3 = rawRow12225 := by decide +kernel

theorem rowCheck12225 : row12225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12225 := by decide +kernel

theorem rowEval12225 (x : Key → ℝ) : Integer.Sparse.eval row12225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12225, Integer.Sparse.eval_collectBalanced, rawRowCheck12225]

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

theorem rawRowCheck12355 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form3 = rawRow12355 := by decide +kernel

theorem rowCheck12355 : row12355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12355 := by decide +kernel

theorem rowEval12355 (x : Key → ℝ) : Integer.Sparse.eval row12355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12355, Integer.Sparse.eval_collectBalanced, rawRowCheck12355]

theorem rawRowCheck12356 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form3 = rawRow12356 := by decide +kernel

theorem rowCheck12356 : row12356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12356 := by decide +kernel

theorem rowEval12356 (x : Key → ℝ) : Integer.Sparse.eval row12356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12356, Integer.Sparse.eval_collectBalanced, rawRowCheck12356]

theorem rawRowCheck12357 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form3 = rawRow12357 := by decide +kernel

theorem rowCheck12357 : row12357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12357 := by decide +kernel

theorem rowEval12357 (x : Key → ℝ) : Integer.Sparse.eval row12357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12357, Integer.Sparse.eval_collectBalanced, rawRowCheck12357]

theorem rawRowCheck12358 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form3 = rawRow12358 := by decide +kernel

theorem rowCheck12358 : row12358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12358 := by decide +kernel

theorem rowEval12358 (x : Key → ℝ) : Integer.Sparse.eval row12358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12358, Integer.Sparse.eval_collectBalanced, rawRowCheck12358]

theorem rawRowCheck12359 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form3 = rawRow12359 := by decide +kernel

theorem rowCheck12359 : row12359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12359 := by decide +kernel

theorem rowEval12359 (x : Key → ℝ) : Integer.Sparse.eval row12359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12359, Integer.Sparse.eval_collectBalanced, rawRowCheck12359]

theorem rawRowCheck12360 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form3 = rawRow12360 := by decide +kernel

theorem rowCheck12360 : row12360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12360 := by decide +kernel

theorem rowEval12360 (x : Key → ℝ) : Integer.Sparse.eval row12360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12360, Integer.Sparse.eval_collectBalanced, rawRowCheck12360]

theorem rawRowCheck12361 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form3 = rawRow12361 := by decide +kernel

theorem rowCheck12361 : row12361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12361 := by decide +kernel

theorem rowEval12361 (x : Key → ℝ) : Integer.Sparse.eval row12361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12361, Integer.Sparse.eval_collectBalanced, rawRowCheck12361]

theorem rawRowCheck12362 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form3 = rawRow12362 := by decide +kernel

theorem rowCheck12362 : row12362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12362 := by decide +kernel

theorem rowEval12362 (x : Key → ℝ) : Integer.Sparse.eval row12362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12362, Integer.Sparse.eval_collectBalanced, rawRowCheck12362]

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

theorem entryCheck24_3 : entry24_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_3 k)) := by decide +kernel

theorem rowsSound24_3 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12221 x
  · exact rowEval12222 x
  · exact rowEval12223 x
  · exact rowEval12224 x
  · exact rowEval12225 x

theorem entryEval24_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_3 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck24_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_3]

end MUB6.Certificate.GramEntries.Block3

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

theorem entryCheck25_3 : entry25_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_3 k)) := by decide +kernel

theorem rowsSound25_3 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12355 x
  · exact rowEval12356 x
  · exact rowEval12357 x
  · exact rowEval12358 x
  · exact rowEval12359 x
  · exact rowEval12360 x
  · exact rowEval12361 x
  · exact rowEval12362 x

theorem entryEval25_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_3 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck25_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12611 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form3 = rawRow12611 := by decide +kernel

theorem rowCheck12611 : row12611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12611 := by decide +kernel

theorem rowEval12611 (x : Key → ℝ) : Integer.Sparse.eval row12611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12611, Integer.Sparse.eval_collectBalanced, rawRowCheck12611]

theorem rawRowCheck12612 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form3 = rawRow12612 := by decide +kernel

theorem rowCheck12612 : row12612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12612 := by decide +kernel

theorem rowEval12612 (x : Key → ℝ) : Integer.Sparse.eval row12612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12612, Integer.Sparse.eval_collectBalanced, rawRowCheck12612]

theorem rawRowCheck12613 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form3 = rawRow12613 := by decide +kernel

theorem rowCheck12613 : row12613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12613 := by decide +kernel

theorem rowEval12613 (x : Key → ℝ) : Integer.Sparse.eval row12613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12613, Integer.Sparse.eval_collectBalanced, rawRowCheck12613]

theorem rawRowCheck12614 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form3 = rawRow12614 := by decide +kernel

theorem rowCheck12614 : row12614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12614 := by decide +kernel

theorem rowEval12614 (x : Key → ℝ) : Integer.Sparse.eval row12614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12614, Integer.Sparse.eval_collectBalanced, rawRowCheck12614]

theorem rawRowCheck12615 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form3 = rawRow12615 := by decide +kernel

theorem rowCheck12615 : row12615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12615 := by decide +kernel

theorem rowEval12615 (x : Key → ℝ) : Integer.Sparse.eval row12615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12615, Integer.Sparse.eval_collectBalanced, rawRowCheck12615]

theorem rawRowCheck12616 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form3 = rawRow12616 := by decide +kernel

theorem rowCheck12616 : row12616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12616 := by decide +kernel

theorem rowEval12616 (x : Key → ℝ) : Integer.Sparse.eval row12616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12616, Integer.Sparse.eval_collectBalanced, rawRowCheck12616]

theorem rawRowCheck12617 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form3 = rawRow12617 := by decide +kernel

theorem rowCheck12617 : row12617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12617 := by decide +kernel

theorem rowEval12617 (x : Key → ℝ) : Integer.Sparse.eval row12617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12617, Integer.Sparse.eval_collectBalanced, rawRowCheck12617]

theorem rawRowCheck12618 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form3 = rawRow12618 := by decide +kernel

theorem rowCheck12618 : row12618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12618 := by decide +kernel

theorem rowEval12618 (x : Key → ℝ) : Integer.Sparse.eval row12618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12618, Integer.Sparse.eval_collectBalanced, rawRowCheck12618]

theorem rawRowCheck12619 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form3 = rawRow12619 := by decide +kernel

theorem rowCheck12619 : row12619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12619 := by decide +kernel

theorem rowEval12619 (x : Key → ℝ) : Integer.Sparse.eval row12619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12619, Integer.Sparse.eval_collectBalanced, rawRowCheck12619]

theorem rawRowCheck12620 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form3 = rawRow12620 := by decide +kernel

theorem rowCheck12620 : row12620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12620 := by decide +kernel

theorem rowEval12620 (x : Key → ℝ) : Integer.Sparse.eval row12620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12620, Integer.Sparse.eval_collectBalanced, rawRowCheck12620]

theorem rawRowCheck12621 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form3 = rawRow12621 := by decide +kernel

theorem rowCheck12621 : row12621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12621 := by decide +kernel

theorem rowEval12621 (x : Key → ℝ) : Integer.Sparse.eval row12621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12621, Integer.Sparse.eval_collectBalanced, rawRowCheck12621]

theorem rawRowCheck12622 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form3 = rawRow12622 := by decide +kernel

theorem rowCheck12622 : row12622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12622 := by decide +kernel

theorem rowEval12622 (x : Key → ℝ) : Integer.Sparse.eval row12622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12622, Integer.Sparse.eval_collectBalanced, rawRowCheck12622]

theorem rawRowCheck12623 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form3 = rawRow12623 := by decide +kernel

theorem rowCheck12623 : row12623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12623 := by decide +kernel

theorem rowEval12623 (x : Key → ℝ) : Integer.Sparse.eval row12623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12623, Integer.Sparse.eval_collectBalanced, rawRowCheck12623]

theorem rawRowCheck12624 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form3 = rawRow12624 := by decide +kernel

theorem rowCheck12624 : row12624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12624 := by decide +kernel

theorem rowEval12624 (x : Key → ℝ) : Integer.Sparse.eval row12624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12624, Integer.Sparse.eval_collectBalanced, rawRowCheck12624]

theorem rawRowCheck12625 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form3 = rawRow12625 := by decide +kernel

theorem rowCheck12625 : row12625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12625 := by decide +kernel

theorem rowEval12625 (x : Key → ℝ) : Integer.Sparse.eval row12625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12625, Integer.Sparse.eval_collectBalanced, rawRowCheck12625]

theorem rawRowCheck12626 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form3 = rawRow12626 := by decide +kernel

theorem rowCheck12626 : row12626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12626 := by decide +kernel

theorem rowEval12626 (x : Key → ℝ) : Integer.Sparse.eval row12626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12626, Integer.Sparse.eval_collectBalanced, rawRowCheck12626]

theorem rawRowCheck12627 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form3 = rawRow12627 := by decide +kernel

theorem rowCheck12627 : row12627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12627 := by decide +kernel

theorem rowEval12627 (x : Key → ℝ) : Integer.Sparse.eval row12627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12627, Integer.Sparse.eval_collectBalanced, rawRowCheck12627]

theorem rawRowCheck12628 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form3 = rawRow12628 := by decide +kernel

theorem rowCheck12628 : row12628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12628 := by decide +kernel

theorem rowEval12628 (x : Key → ℝ) : Integer.Sparse.eval row12628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12628, Integer.Sparse.eval_collectBalanced, rawRowCheck12628]

theorem rawRowCheck12629 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form3 = rawRow12629 := by decide +kernel

theorem rowCheck12629 : row12629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12629 := by decide +kernel

theorem rowEval12629 (x : Key → ℝ) : Integer.Sparse.eval row12629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12629, Integer.Sparse.eval_collectBalanced, rawRowCheck12629]

theorem rawRowCheck12630 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form3 = rawRow12630 := by decide +kernel

theorem rowCheck12630 : row12630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12630 := by decide +kernel

theorem rowEval12630 (x : Key → ℝ) : Integer.Sparse.eval row12630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12630, Integer.Sparse.eval_collectBalanced, rawRowCheck12630]

theorem rawRowCheck12631 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form3 = rawRow12631 := by decide +kernel

theorem rowCheck12631 : row12631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12631 := by decide +kernel

theorem rowEval12631 (x : Key → ℝ) : Integer.Sparse.eval row12631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12631, Integer.Sparse.eval_collectBalanced, rawRowCheck12631]

theorem rawRowCheck12632 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow12632 := by decide +kernel

theorem rowCheck12632 : row12632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12632 := by decide +kernel

theorem rowEval12632 (x : Key → ℝ) : Integer.Sparse.eval row12632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12632, Integer.Sparse.eval_collectBalanced, rawRowCheck12632]

theorem rawRowCheck12633 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow12633 := by decide +kernel

theorem rowCheck12633 : row12633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12633 := by decide +kernel

theorem rowEval12633 (x : Key → ℝ) : Integer.Sparse.eval row12633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12633, Integer.Sparse.eval_collectBalanced, rawRowCheck12633]

theorem rawRowCheck12634 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow12634 := by decide +kernel

theorem rowCheck12634 : row12634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12634 := by decide +kernel

theorem rowEval12634 (x : Key → ℝ) : Integer.Sparse.eval row12634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12634, Integer.Sparse.eval_collectBalanced, rawRowCheck12634]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck26_3 : entry26_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_3 k)) := by decide +kernel

theorem rowsSound26_3 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12611 x
  · exact rowEval12612 x
  · exact rowEval12613 x
  · exact rowEval12614 x
  · exact rowEval12615 x
  · exact rowEval12616 x
  · exact rowEval12617 x
  · exact rowEval12618 x
  · exact rowEval12619 x
  · exact rowEval12620 x
  · exact rowEval12621 x
  · exact rowEval12622 x
  · exact rowEval12623 x
  · exact rowEval12624 x
  · exact rowEval12625 x
  · exact rowEval12626 x
  · exact rowEval12627 x
  · exact rowEval12628 x
  · exact rowEval12629 x
  · exact rowEval12630 x
  · exact rowEval12631 x
  · exact rowEval12632 x
  · exact rowEval12633 x
  · exact rowEval12634 x

theorem entryEval26_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_3 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck26_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7430 x
  · exact rowEval7431 x
  · exact rowEval7432 x
  · exact rowEval7433 x
  · exact rowEval7434 x
  · exact rowEval7435 x
  · exact rowEval7436 x
  · exact rowEval7437 x
  · exact rowEval7438 x
  · exact rowEval7439 x
  · exact rowEval7440 x
  · exact rowEval7441 x
  · exact rowEval7442 x
  · exact rowEval7443 x
  · exact rowEval7444 x
  · exact rowEval7445 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7446 x
  · exact rowEval7447 x
  · exact rowEval7448 x
  · exact rowEval7449 x
  · exact rowEval7450 x
  · exact rowEval7451 x
  · exact rowEval7452 x
  · exact rowEval7453 x
  · exact rowEval7454 x
  · exact rowEval7455 x
  · exact rowEval7456 x
  · exact rowEval7457 x
  · exact rowEval7458 x
  · exact rowEval7459 x
  · exact rowEval7460 x
  · exact rowEval7461 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7462 x
  · exact rowEval7463 x
  · exact rowEval7464 x
  · exact rowEval7465 x
  · exact rowEval7466 x
  · exact rowEval7467 x
  · exact rowEval7468 x
  · exact rowEval7469 x
  · exact rowEval7470 x
  · exact rowEval7471 x
  · exact rowEval7472 x
  · exact rowEval7473 x
  · exact rowEval7474 x
  · exact rowEval7475 x
  · exact rowEval7476 x
  · exact rowEval7477 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7478 x
  · exact rowEval7479 x
  · exact rowEval7480 x
  · exact rowEval7481 x
  · exact rowEval7482 x
  · exact rowEval7483 x
  · exact rowEval7484 x
  · exact rowEval7485 x
  · exact rowEval7486 x
  · exact rowEval7487 x
  · exact rowEval7488 x
  · exact rowEval7489 x
  · exact rowEval7490 x
  · exact rowEval7491 x
  · exact rowEval7492 x
  · exact rowEval7493 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7542 x
  · exact rowEval7543 x
  · exact rowEval7544 x
  · exact rowEval7545 x
  · exact rowEval7546 x
  · exact rowEval7547 x
  · exact rowEval7548 x
  · exact rowEval7549 x
  · exact rowEval7550 x
  · exact rowEval7551 x
  · exact rowEval7552 x
  · exact rowEval7553 x
  · exact rowEval7554 x
  · exact rowEval7555 x
  · exact rowEval7556 x
  · exact rowEval7557 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7682 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7682 := by decide +kernel

theorem rowCheck7682 : row7682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7682 := by decide +kernel

theorem rowEval7682 (x : Key → ℝ) : Integer.Sparse.eval row7682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7682, Integer.Sparse.eval_collectBalanced, rawRowCheck7682]

theorem rawRowCheck7683 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7683 := by decide +kernel

theorem rowCheck7683 : row7683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7683 := by decide +kernel

theorem rowEval7683 (x : Key → ℝ) : Integer.Sparse.eval row7683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7683, Integer.Sparse.eval_collectBalanced, rawRowCheck7683]

theorem rawRowCheck7684 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7684 := by decide +kernel

theorem rowCheck7684 : row7684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7684 := by decide +kernel

theorem rowEval7684 (x : Key → ℝ) : Integer.Sparse.eval row7684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7684, Integer.Sparse.eval_collectBalanced, rawRowCheck7684]

theorem rawRowCheck7685 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form3 = rawRow7685 := by decide +kernel

theorem rowCheck7685 : row7685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7685 := by decide +kernel

theorem rowEval7685 (x : Key → ℝ) : Integer.Sparse.eval row7685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7685, Integer.Sparse.eval_collectBalanced, rawRowCheck7685]

theorem rawRowCheck7686 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form3 = rawRow7686 := by decide +kernel

theorem rowCheck7686 : row7686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7686 := by decide +kernel

theorem rowEval7686 (x : Key → ℝ) : Integer.Sparse.eval row7686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7686, Integer.Sparse.eval_collectBalanced, rawRowCheck7686]

theorem rawRowCheck7687 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form3 = rawRow7687 := by decide +kernel

theorem rowCheck7687 : row7687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7687 := by decide +kernel

theorem rowEval7687 (x : Key → ℝ) : Integer.Sparse.eval row7687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7687, Integer.Sparse.eval_collectBalanced, rawRowCheck7687]

theorem rawRowCheck7688 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form3 = rawRow7688 := by decide +kernel

theorem rowCheck7688 : row7688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7688 := by decide +kernel

theorem rowEval7688 (x : Key → ℝ) : Integer.Sparse.eval row7688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7688, Integer.Sparse.eval_collectBalanced, rawRowCheck7688]

theorem rawRowCheck7689 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form3 = rawRow7689 := by decide +kernel

theorem rowCheck7689 : row7689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7689 := by decide +kernel

theorem rowEval7689 (x : Key → ℝ) : Integer.Sparse.eval row7689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7689, Integer.Sparse.eval_collectBalanced, rawRowCheck7689]

theorem rawRowCheck7690 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form3 = rawRow7690 := by decide +kernel

theorem rowCheck7690 : row7690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7690 := by decide +kernel

theorem rowEval7690 (x : Key → ℝ) : Integer.Sparse.eval row7690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7690, Integer.Sparse.eval_collectBalanced, rawRowCheck7690]

theorem rawRowCheck7691 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form3 = rawRow7691 := by decide +kernel

theorem rowCheck7691 : row7691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7691 := by decide +kernel

theorem rowEval7691 (x : Key → ℝ) : Integer.Sparse.eval row7691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7691, Integer.Sparse.eval_collectBalanced, rawRowCheck7691]

theorem rawRowCheck7692 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form3 = rawRow7692 := by decide +kernel

theorem rowCheck7692 : row7692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7692 := by decide +kernel

theorem rowEval7692 (x : Key → ℝ) : Integer.Sparse.eval row7692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7692, Integer.Sparse.eval_collectBalanced, rawRowCheck7692]

theorem rawRowCheck7693 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form3 = rawRow7693 := by decide +kernel

theorem rowCheck7693 : row7693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7693 := by decide +kernel

theorem rowEval7693 (x : Key → ℝ) : Integer.Sparse.eval row7693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7693, Integer.Sparse.eval_collectBalanced, rawRowCheck7693]

theorem rawRowCheck7805 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7805 := by decide +kernel

theorem rowCheck7805 : row7805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7805 := by decide +kernel

theorem rowEval7805 (x : Key → ℝ) : Integer.Sparse.eval row7805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7805, Integer.Sparse.eval_collectBalanced, rawRowCheck7805]

theorem rawRowCheck7806 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7806 := by decide +kernel

theorem rowCheck7806 : row7806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7806 := by decide +kernel

theorem rowEval7806 (x : Key → ℝ) : Integer.Sparse.eval row7806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7806, Integer.Sparse.eval_collectBalanced, rawRowCheck7806]

theorem rawRowCheck7807 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow7807 := by decide +kernel

theorem rowCheck7807 : row7807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7807 := by decide +kernel

theorem rowEval7807 (x : Key → ℝ) : Integer.Sparse.eval row7807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7807, Integer.Sparse.eval_collectBalanced, rawRowCheck7807]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7808 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow7808 := by decide +kernel

theorem rowCheck7808 : row7808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7808 := by decide +kernel

theorem rowEval7808 (x : Key → ℝ) : Integer.Sparse.eval row7808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7808, Integer.Sparse.eval_collectBalanced, rawRowCheck7808]

theorem rawRowCheck7809 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow7809 := by decide +kernel

theorem rowCheck7809 : row7809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7809 := by decide +kernel

theorem rowEval7809 (x : Key → ℝ) : Integer.Sparse.eval row7809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7809, Integer.Sparse.eval_collectBalanced, rawRowCheck7809]

theorem rawRowCheck7861 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7861 := by decide +kernel

theorem rowCheck7861 : row7861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7861 := by decide +kernel

theorem rowEval7861 (x : Key → ℝ) : Integer.Sparse.eval row7861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7861, Integer.Sparse.eval_collectBalanced, rawRowCheck7861]

theorem rawRowCheck7862 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7862 := by decide +kernel

theorem rowCheck7862 : row7862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7862 := by decide +kernel

theorem rowEval7862 (x : Key → ℝ) : Integer.Sparse.eval row7862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7862, Integer.Sparse.eval_collectBalanced, rawRowCheck7862]

theorem rawRowCheck7863 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7863 := by decide +kernel

theorem rowCheck7863 : row7863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7863 := by decide +kernel

theorem rowEval7863 (x : Key → ℝ) : Integer.Sparse.eval row7863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7863, Integer.Sparse.eval_collectBalanced, rawRowCheck7863]

theorem rawRowCheck7864 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form3 = rawRow7864 := by decide +kernel

theorem rowCheck7864 : row7864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7864 := by decide +kernel

theorem rowEval7864 (x : Key → ℝ) : Integer.Sparse.eval row7864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7864, Integer.Sparse.eval_collectBalanced, rawRowCheck7864]

theorem rawRowCheck7865 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form3 = rawRow7865 := by decide +kernel

theorem rowCheck7865 : row7865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7865 := by decide +kernel

theorem rowEval7865 (x : Key → ℝ) : Integer.Sparse.eval row7865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7865, Integer.Sparse.eval_collectBalanced, rawRowCheck7865]

theorem rawRowCheck7866 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form3 = rawRow7866 := by decide +kernel

theorem rowCheck7866 : row7866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7866 := by decide +kernel

theorem rowEval7866 (x : Key → ℝ) : Integer.Sparse.eval row7866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7866, Integer.Sparse.eval_collectBalanced, rawRowCheck7866]

theorem rawRowCheck7867 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form3 = rawRow7867 := by decide +kernel

theorem rowCheck7867 : row7867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7867 := by decide +kernel

theorem rowEval7867 (x : Key → ℝ) : Integer.Sparse.eval row7867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7867, Integer.Sparse.eval_collectBalanced, rawRowCheck7867]

theorem rawRowCheck7868 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form3 = rawRow7868 := by decide +kernel

theorem rowCheck7868 : row7868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7868 := by decide +kernel

theorem rowEval7868 (x : Key → ℝ) : Integer.Sparse.eval row7868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7868, Integer.Sparse.eval_collectBalanced, rawRowCheck7868]

theorem rawRowCheck7869 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form3 = rawRow7869 := by decide +kernel

theorem rowCheck7869 : row7869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7869 := by decide +kernel

theorem rowEval7869 (x : Key → ℝ) : Integer.Sparse.eval row7869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7869, Integer.Sparse.eval_collectBalanced, rawRowCheck7869]

theorem rawRowCheck7870 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow7870 := by decide +kernel

theorem rowCheck7870 : row7870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7870 := by decide +kernel

theorem rowEval7870 (x : Key → ℝ) : Integer.Sparse.eval row7870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7870, Integer.Sparse.eval_collectBalanced, rawRowCheck7870]

theorem rawRowCheck7871 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow7871 := by decide +kernel

theorem rowCheck7871 : row7871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7871 := by decide +kernel

theorem rowEval7871 (x : Key → ℝ) : Integer.Sparse.eval row7871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7871, Integer.Sparse.eval_collectBalanced, rawRowCheck7871]

theorem rawRowCheck7872 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow7872 := by decide +kernel

theorem rowCheck7872 : row7872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7872 := by decide +kernel

theorem rowEval7872 (x : Key → ℝ) : Integer.Sparse.eval row7872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7872, Integer.Sparse.eval_collectBalanced, rawRowCheck7872]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck6_3 : entry6_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_3 k)) := by decide +kernel

theorem rowsSound6_3 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7805 x
  · exact rowEval7806 x
  · exact rowEval7807 x
  · exact rowEval7808 x
  · exact rowEval7809 x

theorem entryEval6_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_3 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck6_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_3]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7861 x
  · exact rowEval7862 x
  · exact rowEval7863 x
  · exact rowEval7864 x
  · exact rowEval7865 x
  · exact rowEval7866 x
  · exact rowEval7867 x
  · exact rowEval7868 x
  · exact rowEval7869 x
  · exact rowEval7870 x
  · exact rowEval7871 x
  · exact rowEval7872 x
  · exact rowEval7682 x
  · exact rowEval7683 x
  · exact rowEval7684 x
  · exact rowEval7685 x
  · exact rowEval7686 x
  · exact rowEval7687 x
  · exact rowEval7688 x
  · exact rowEval7689 x
  · exact rowEval7690 x
  · exact rowEval7691 x
  · exact rowEval7692 x
  · exact rowEval7693 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

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

theorem entryEvalRow3_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 3).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval3_0 B hB
  · exact entryEval3_1 B hB
  · exact entryEval3_2 B hB
  · exact entryEval3_3 B hB
  · exact (entryEval4_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e_oai
