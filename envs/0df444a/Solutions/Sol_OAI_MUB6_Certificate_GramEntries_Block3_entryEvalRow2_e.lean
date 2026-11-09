-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:14:18.15475+00:00
-- url     : https://prove2.me/submissions/1aca1fd5-d272-492c-977a-d1b8215b5fa6

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval5_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval8_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval9_2_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7382 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7382 := by decide +kernel

theorem rowCheck7382 : row7382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7382 := by decide +kernel

theorem rowEval7382 (x : Key → ℝ) : Integer.Sparse.eval row7382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7382, Integer.Sparse.eval_collectBalanced, rawRowCheck7382]

theorem rawRowCheck7383 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7383 := by decide +kernel

theorem rowCheck7383 : row7383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7383 := by decide +kernel

theorem rowEval7383 (x : Key → ℝ) : Integer.Sparse.eval row7383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7383, Integer.Sparse.eval_collectBalanced, rawRowCheck7383]

theorem rawRowCheck7384 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7384 := by decide +kernel

theorem rowCheck7384 : row7384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7384 := by decide +kernel

theorem rowEval7384 (x : Key → ℝ) : Integer.Sparse.eval row7384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7384, Integer.Sparse.eval_collectBalanced, rawRowCheck7384]

theorem rawRowCheck7385 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7385 := by decide +kernel

theorem rowCheck7385 : row7385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7385 := by decide +kernel

theorem rowEval7385 (x : Key → ℝ) : Integer.Sparse.eval row7385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7385, Integer.Sparse.eval_collectBalanced, rawRowCheck7385]

theorem rawRowCheck7386 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7386 := by decide +kernel

theorem rowCheck7386 : row7386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7386 := by decide +kernel

theorem rowEval7386 (x : Key → ℝ) : Integer.Sparse.eval row7386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7386, Integer.Sparse.eval_collectBalanced, rawRowCheck7386]

theorem rawRowCheck7387 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7387 := by decide +kernel

theorem rowCheck7387 : row7387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7387 := by decide +kernel

theorem rowEval7387 (x : Key → ℝ) : Integer.Sparse.eval row7387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7387, Integer.Sparse.eval_collectBalanced, rawRowCheck7387]

theorem rawRowCheck7388 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7388 := by decide +kernel

theorem rowCheck7388 : row7388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7388 := by decide +kernel

theorem rowEval7388 (x : Key → ℝ) : Integer.Sparse.eval row7388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7388, Integer.Sparse.eval_collectBalanced, rawRowCheck7388]

theorem rawRowCheck7389 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0 = rawRow7389 := by decide +kernel

theorem rowCheck7389 : row7389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7389 := by decide +kernel

theorem rowEval7389 (x : Key → ℝ) : Integer.Sparse.eval row7389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7389, Integer.Sparse.eval_collectBalanced, rawRowCheck7389]

theorem rawRowCheck7390 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0 = rawRow7390 := by decide +kernel

theorem rowCheck7390 : row7390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7390 := by decide +kernel

theorem rowEval7390 (x : Key → ℝ) : Integer.Sparse.eval row7390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7390, Integer.Sparse.eval_collectBalanced, rawRowCheck7390]

theorem rawRowCheck7391 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0 = rawRow7391 := by decide +kernel

theorem rowCheck7391 : row7391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7391 := by decide +kernel

theorem rowEval7391 (x : Key → ℝ) : Integer.Sparse.eval row7391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7391, Integer.Sparse.eval_collectBalanced, rawRowCheck7391]

theorem rawRowCheck7392 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0 = rawRow7392 := by decide +kernel

theorem rowCheck7392 : row7392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7392 := by decide +kernel

theorem rowEval7392 (x : Key → ℝ) : Integer.Sparse.eval row7392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7392, Integer.Sparse.eval_collectBalanced, rawRowCheck7392]

theorem rawRowCheck7393 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0 = rawRow7393 := by decide +kernel

theorem rowCheck7393 : row7393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7393 := by decide +kernel

theorem rowEval7393 (x : Key → ℝ) : Integer.Sparse.eval row7393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7393, Integer.Sparse.eval_collectBalanced, rawRowCheck7393]

theorem rawRowCheck7394 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0 = rawRow7394 := by decide +kernel

theorem rowCheck7394 : row7394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7394 := by decide +kernel

theorem rowEval7394 (x : Key → ℝ) : Integer.Sparse.eval row7394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7394, Integer.Sparse.eval_collectBalanced, rawRowCheck7394]

theorem rawRowCheck7395 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7395 := by decide +kernel

theorem rowCheck7395 : row7395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7395 := by decide +kernel

theorem rowEval7395 (x : Key → ℝ) : Integer.Sparse.eval row7395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7395, Integer.Sparse.eval_collectBalanced, rawRowCheck7395]

theorem rawRowCheck7396 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7396 := by decide +kernel

theorem rowCheck7396 : row7396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7396 := by decide +kernel

theorem rowEval7396 (x : Key → ℝ) : Integer.Sparse.eval row7396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7396, Integer.Sparse.eval_collectBalanced, rawRowCheck7396]

theorem rawRowCheck7397 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7397 := by decide +kernel

theorem rowCheck7397 : row7397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7397 := by decide +kernel

theorem rowEval7397 (x : Key → ℝ) : Integer.Sparse.eval row7397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7397, Integer.Sparse.eval_collectBalanced, rawRowCheck7397]

theorem rawRowCheck7398 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7398 := by decide +kernel

theorem rowCheck7398 : row7398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7398 := by decide +kernel

theorem rowEval7398 (x : Key → ℝ) : Integer.Sparse.eval row7398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7398, Integer.Sparse.eval_collectBalanced, rawRowCheck7398]

theorem rawRowCheck7399 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7399 := by decide +kernel

theorem rowCheck7399 : row7399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7399 := by decide +kernel

theorem rowEval7399 (x : Key → ℝ) : Integer.Sparse.eval row7399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7399, Integer.Sparse.eval_collectBalanced, rawRowCheck7399]

theorem rawRowCheck7400 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7400 := by decide +kernel

theorem rowCheck7400 : row7400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7400 := by decide +kernel

theorem rowEval7400 (x : Key → ℝ) : Integer.Sparse.eval row7400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7400, Integer.Sparse.eval_collectBalanced, rawRowCheck7400]

theorem rawRowCheck7401 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7401 := by decide +kernel

theorem rowCheck7401 : row7401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7401 := by decide +kernel

theorem rowEval7401 (x : Key → ℝ) : Integer.Sparse.eval row7401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7401, Integer.Sparse.eval_collectBalanced, rawRowCheck7401]

theorem rawRowCheck7402 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7402 := by decide +kernel

theorem rowCheck7402 : row7402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7402 := by decide +kernel

theorem rowEval7402 (x : Key → ℝ) : Integer.Sparse.eval row7402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7402, Integer.Sparse.eval_collectBalanced, rawRowCheck7402]

theorem rawRowCheck7403 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7403 := by decide +kernel

theorem rowCheck7403 : row7403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7403 := by decide +kernel

theorem rowEval7403 (x : Key → ℝ) : Integer.Sparse.eval row7403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7403, Integer.Sparse.eval_collectBalanced, rawRowCheck7403]

theorem rawRowCheck7404 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7404 := by decide +kernel

theorem rowCheck7404 : row7404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7404 := by decide +kernel

theorem rowEval7404 (x : Key → ℝ) : Integer.Sparse.eval row7404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7404, Integer.Sparse.eval_collectBalanced, rawRowCheck7404]

theorem rawRowCheck7405 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form1 = rawRow7405 := by decide +kernel

theorem rowCheck7405 : row7405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7405 := by decide +kernel

theorem rowEval7405 (x : Key → ℝ) : Integer.Sparse.eval row7405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7405, Integer.Sparse.eval_collectBalanced, rawRowCheck7405]

theorem rawRowCheck7406 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form1 = rawRow7406 := by decide +kernel

theorem rowCheck7406 : row7406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7406 := by decide +kernel

theorem rowEval7406 (x : Key → ℝ) : Integer.Sparse.eval row7406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7406, Integer.Sparse.eval_collectBalanced, rawRowCheck7406]

theorem rawRowCheck7407 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form1 = rawRow7407 := by decide +kernel

theorem rowCheck7407 : row7407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7407 := by decide +kernel

theorem rowEval7407 (x : Key → ℝ) : Integer.Sparse.eval row7407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7407, Integer.Sparse.eval_collectBalanced, rawRowCheck7407]

theorem rawRowCheck7408 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form1 = rawRow7408 := by decide +kernel

theorem rowCheck7408 : row7408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7408 := by decide +kernel

theorem rowEval7408 (x : Key → ℝ) : Integer.Sparse.eval row7408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7408, Integer.Sparse.eval_collectBalanced, rawRowCheck7408]

theorem rawRowCheck7409 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form1 = rawRow7409 := by decide +kernel

theorem rowCheck7409 : row7409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7409 := by decide +kernel

theorem rowEval7409 (x : Key → ℝ) : Integer.Sparse.eval row7409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7409, Integer.Sparse.eval_collectBalanced, rawRowCheck7409]

theorem rawRowCheck7410 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form1 = rawRow7410 := by decide +kernel

theorem rowCheck7410 : row7410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7410 := by decide +kernel

theorem rowEval7410 (x : Key → ℝ) : Integer.Sparse.eval row7410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7410, Integer.Sparse.eval_collectBalanced, rawRowCheck7410]

theorem rawRowCheck7411 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7411 := by decide +kernel

theorem rowCheck7411 : row7411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7411 := by decide +kernel

theorem rowEval7411 (x : Key → ℝ) : Integer.Sparse.eval row7411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7411, Integer.Sparse.eval_collectBalanced, rawRowCheck7411]

theorem rawRowCheck7412 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7412 := by decide +kernel

theorem rowCheck7412 : row7412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7412 := by decide +kernel

theorem rowEval7412 (x : Key → ℝ) : Integer.Sparse.eval row7412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7412, Integer.Sparse.eval_collectBalanced, rawRowCheck7412]

theorem rawRowCheck7413 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7413 := by decide +kernel

theorem rowCheck7413 : row7413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7413 := by decide +kernel

theorem rowEval7413 (x : Key → ℝ) : Integer.Sparse.eval row7413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7413, Integer.Sparse.eval_collectBalanced, rawRowCheck7413]

theorem rawRowCheck7414 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7414 := by decide +kernel

theorem rowCheck7414 : row7414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7414 := by decide +kernel

theorem rowEval7414 (x : Key → ℝ) : Integer.Sparse.eval row7414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7414, Integer.Sparse.eval_collectBalanced, rawRowCheck7414]

theorem rawRowCheck7415 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7415 := by decide +kernel

theorem rowCheck7415 : row7415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7415 := by decide +kernel

theorem rowEval7415 (x : Key → ℝ) : Integer.Sparse.eval row7415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7415, Integer.Sparse.eval_collectBalanced, rawRowCheck7415]

theorem rawRowCheck7416 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7416 := by decide +kernel

theorem rowCheck7416 : row7416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7416 := by decide +kernel

theorem rowEval7416 (x : Key → ℝ) : Integer.Sparse.eval row7416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7416, Integer.Sparse.eval_collectBalanced, rawRowCheck7416]

theorem rawRowCheck7417 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7417 := by decide +kernel

theorem rowCheck7417 : row7417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7417 := by decide +kernel

theorem rowEval7417 (x : Key → ℝ) : Integer.Sparse.eval row7417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7417, Integer.Sparse.eval_collectBalanced, rawRowCheck7417]

theorem rawRowCheck7418 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7418 := by decide +kernel

theorem rowCheck7418 : row7418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7418 := by decide +kernel

theorem rowEval7418 (x : Key → ℝ) : Integer.Sparse.eval row7418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7418, Integer.Sparse.eval_collectBalanced, rawRowCheck7418]

theorem rawRowCheck7419 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7419 := by decide +kernel

theorem rowCheck7419 : row7419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7419 := by decide +kernel

theorem rowEval7419 (x : Key → ℝ) : Integer.Sparse.eval row7419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7419, Integer.Sparse.eval_collectBalanced, rawRowCheck7419]

theorem rawRowCheck7420 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7420 := by decide +kernel

theorem rowCheck7420 : row7420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7420 := by decide +kernel

theorem rowEval7420 (x : Key → ℝ) : Integer.Sparse.eval row7420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7420, Integer.Sparse.eval_collectBalanced, rawRowCheck7420]

theorem rawRowCheck7421 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form2 = rawRow7421 := by decide +kernel

theorem rowCheck7421 : row7421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7421 := by decide +kernel

theorem rowEval7421 (x : Key → ℝ) : Integer.Sparse.eval row7421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7421, Integer.Sparse.eval_collectBalanced, rawRowCheck7421]

theorem rawRowCheck7422 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form2 = rawRow7422 := by decide +kernel

theorem rowCheck7422 : row7422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7422 := by decide +kernel

theorem rowEval7422 (x : Key → ℝ) : Integer.Sparse.eval row7422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7422, Integer.Sparse.eval_collectBalanced, rawRowCheck7422]

theorem rawRowCheck7423 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form2 = rawRow7423 := by decide +kernel

theorem rowCheck7423 : row7423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7423 := by decide +kernel

theorem rowEval7423 (x : Key → ℝ) : Integer.Sparse.eval row7423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7423, Integer.Sparse.eval_collectBalanced, rawRowCheck7423]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck8677 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form2 = rawRow8677 := by decide +kernel

theorem rowCheck8677 : row8677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8677 := by decide +kernel

theorem rowEval8677 (x : Key → ℝ) : Integer.Sparse.eval row8677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8677, Integer.Sparse.eval_collectBalanced, rawRowCheck8677]

theorem rawRowCheck8678 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form2 = rawRow8678 := by decide +kernel

theorem rowCheck8678 : row8678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8678 := by decide +kernel

theorem rowEval8678 (x : Key → ℝ) : Integer.Sparse.eval row8678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8678, Integer.Sparse.eval_collectBalanced, rawRowCheck8678]

theorem rawRowCheck8679 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form2 = rawRow8679 := by decide +kernel

theorem rowCheck8679 : row8679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8679 := by decide +kernel

theorem rowEval8679 (x : Key → ℝ) : Integer.Sparse.eval row8679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8679, Integer.Sparse.eval_collectBalanced, rawRowCheck8679]

theorem rawRowCheck8680 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8680 := by decide +kernel

theorem rowCheck8680 : row8680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8680 := by decide +kernel

theorem rowEval8680 (x : Key → ℝ) : Integer.Sparse.eval row8680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8680, Integer.Sparse.eval_collectBalanced, rawRowCheck8680]

theorem rawRowCheck8681 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8681 := by decide +kernel

theorem rowCheck8681 : row8681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8681 := by decide +kernel

theorem rowEval8681 (x : Key → ℝ) : Integer.Sparse.eval row8681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8681, Integer.Sparse.eval_collectBalanced, rawRowCheck8681]

theorem rawRowCheck8682 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow8682 := by decide +kernel

theorem rowCheck8682 : row8682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8682 := by decide +kernel

theorem rowEval8682 (x : Key → ℝ) : Integer.Sparse.eval row8682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8682, Integer.Sparse.eval_collectBalanced, rawRowCheck8682]

theorem rawRowCheck8683 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow8683 := by decide +kernel

theorem rowCheck8683 : row8683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8683 := by decide +kernel

theorem rowEval8683 (x : Key → ℝ) : Integer.Sparse.eval row8683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8683, Integer.Sparse.eval_collectBalanced, rawRowCheck8683]

theorem rawRowCheck8684 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow8684 := by decide +kernel

theorem rowCheck8684 : row8684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8684 := by decide +kernel

theorem rowEval8684 (x : Key → ℝ) : Integer.Sparse.eval row8684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck8684, Integer.Sparse.eval_collectBalanced, rawRowCheck8684]

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

theorem rawRowCheck8765 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8765 := by decide +kernel

theorem rowCheck8765 : row8765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8765 := by decide +kernel

theorem rowEval8765 (x : Key → ℝ) : Integer.Sparse.eval row8765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8765, Integer.Sparse.eval_collectBalanced, rawRowCheck8765]

theorem rawRowCheck8766 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow8766 := by decide +kernel

theorem rowCheck8766 : row8766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8766 := by decide +kernel

theorem rowEval8766 (x : Key → ℝ) : Integer.Sparse.eval row8766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8766, Integer.Sparse.eval_collectBalanced, rawRowCheck8766]

theorem rawRowCheck8767 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow8767 := by decide +kernel

theorem rowCheck8767 : row8767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8767 := by decide +kernel

theorem rowEval8767 (x : Key → ℝ) : Integer.Sparse.eval row8767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8767, Integer.Sparse.eval_collectBalanced, rawRowCheck8767]

theorem rawRowCheck8768 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow8768 := by decide +kernel

theorem rowCheck8768 : row8768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8768 := by decide +kernel

theorem rowEval8768 (x : Key → ℝ) : Integer.Sparse.eval row8768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck8768, Integer.Sparse.eval_collectBalanced, rawRowCheck8768]

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

theorem entryCheck11_2 : entry11_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_2 k)) := by decide +kernel

theorem rowsSound11_2 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8677 x
  · exact rowEval8678 x
  · exact rowEval8679 x
  · exact rowEval8680 x
  · exact rowEval8681 x
  · exact rowEval8682 x
  · exact rowEval8683 x
  · exact rowEval8684 x

theorem entryEval11_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_2 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck11_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_2]

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

theorem rawRowCheck7424 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form2 = rawRow7424 := by decide +kernel

theorem rowCheck7424 : row7424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7424 := by decide +kernel

theorem rowEval7424 (x : Key → ℝ) : Integer.Sparse.eval row7424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7424, Integer.Sparse.eval_collectBalanced, rawRowCheck7424]

theorem rawRowCheck7425 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form2 = rawRow7425 := by decide +kernel

theorem rowCheck7425 : row7425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7425 := by decide +kernel

theorem rowEval7425 (x : Key → ℝ) : Integer.Sparse.eval row7425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7425, Integer.Sparse.eval_collectBalanced, rawRowCheck7425]

theorem rawRowCheck7426 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form2 = rawRow7426 := by decide +kernel

theorem rowCheck7426 : row7426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7426 := by decide +kernel

theorem rowEval7426 (x : Key → ℝ) : Integer.Sparse.eval row7426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7426, Integer.Sparse.eval_collectBalanced, rawRowCheck7426]

theorem rawRowCheck7427 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form2 = rawRow7427 := by decide +kernel

theorem rowCheck7427 : row7427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7427 := by decide +kernel

theorem rowEval7427 (x : Key → ℝ) : Integer.Sparse.eval row7427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7427, Integer.Sparse.eval_collectBalanced, rawRowCheck7427]

theorem rawRowCheck7428 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form2 = rawRow7428 := by decide +kernel

theorem rowCheck7428 : row7428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7428 := by decide +kernel

theorem rowEval7428 (x : Key → ℝ) : Integer.Sparse.eval row7428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7428, Integer.Sparse.eval_collectBalanced, rawRowCheck7428]

theorem rawRowCheck7429 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form2 = rawRow7429 := by decide +kernel

theorem rowCheck7429 : row7429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7429 := by decide +kernel

theorem rowEval7429 (x : Key → ℝ) : Integer.Sparse.eval row7429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7429, Integer.Sparse.eval_collectBalanced, rawRowCheck7429]

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

theorem rawRowCheck7526 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7526 := by decide +kernel

theorem rowCheck7526 : row7526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7526 := by decide +kernel

theorem rowEval7526 (x : Key → ℝ) : Integer.Sparse.eval row7526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7526, Integer.Sparse.eval_collectBalanced, rawRowCheck7526]

theorem rawRowCheck7527 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7527 := by decide +kernel

theorem rowCheck7527 : row7527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7527 := by decide +kernel

theorem rowEval7527 (x : Key → ℝ) : Integer.Sparse.eval row7527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7527, Integer.Sparse.eval_collectBalanced, rawRowCheck7527]

theorem rawRowCheck7528 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7528 := by decide +kernel

theorem rowCheck7528 : row7528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7528 := by decide +kernel

theorem rowEval7528 (x : Key → ℝ) : Integer.Sparse.eval row7528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7528, Integer.Sparse.eval_collectBalanced, rawRowCheck7528]

theorem rawRowCheck7529 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7529 := by decide +kernel

theorem rowCheck7529 : row7529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7529 := by decide +kernel

theorem rowEval7529 (x : Key → ℝ) : Integer.Sparse.eval row7529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7529, Integer.Sparse.eval_collectBalanced, rawRowCheck7529]

theorem rawRowCheck7530 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7530 := by decide +kernel

theorem rowCheck7530 : row7530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7530 := by decide +kernel

theorem rowEval7530 (x : Key → ℝ) : Integer.Sparse.eval row7530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7530, Integer.Sparse.eval_collectBalanced, rawRowCheck7530]

theorem rawRowCheck7531 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7531 := by decide +kernel

theorem rowCheck7531 : row7531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7531 := by decide +kernel

theorem rowEval7531 (x : Key → ℝ) : Integer.Sparse.eval row7531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7531, Integer.Sparse.eval_collectBalanced, rawRowCheck7531]

theorem rawRowCheck7532 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7532 := by decide +kernel

theorem rowCheck7532 : row7532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7532 := by decide +kernel

theorem rowEval7532 (x : Key → ℝ) : Integer.Sparse.eval row7532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7532, Integer.Sparse.eval_collectBalanced, rawRowCheck7532]

theorem rawRowCheck7533 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form2 = rawRow7533 := by decide +kernel

theorem rowCheck7533 : row7533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7533 := by decide +kernel

theorem rowEval7533 (x : Key → ℝ) : Integer.Sparse.eval row7533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7533, Integer.Sparse.eval_collectBalanced, rawRowCheck7533]

theorem rawRowCheck7534 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form2 = rawRow7534 := by decide +kernel

theorem rowCheck7534 : row7534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7534 := by decide +kernel

theorem rowEval7534 (x : Key → ℝ) : Integer.Sparse.eval row7534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7534, Integer.Sparse.eval_collectBalanced, rawRowCheck7534]

theorem rawRowCheck7535 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form2 = rawRow7535 := by decide +kernel

theorem rowCheck7535 : row7535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7535 := by decide +kernel

theorem rowEval7535 (x : Key → ℝ) : Integer.Sparse.eval row7535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7535, Integer.Sparse.eval_collectBalanced, rawRowCheck7535]

theorem rawRowCheck7536 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form2 = rawRow7536 := by decide +kernel

theorem rowCheck7536 : row7536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7536 := by decide +kernel

theorem rowEval7536 (x : Key → ℝ) : Integer.Sparse.eval row7536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7536, Integer.Sparse.eval_collectBalanced, rawRowCheck7536]

theorem rawRowCheck7537 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form2 = rawRow7537 := by decide +kernel

theorem rowCheck7537 : row7537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7537 := by decide +kernel

theorem rowEval7537 (x : Key → ℝ) : Integer.Sparse.eval row7537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7537, Integer.Sparse.eval_collectBalanced, rawRowCheck7537]

theorem rawRowCheck7538 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form2 = rawRow7538 := by decide +kernel

theorem rowCheck7538 : row7538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7538 := by decide +kernel

theorem rowEval7538 (x : Key → ℝ) : Integer.Sparse.eval row7538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7538, Integer.Sparse.eval_collectBalanced, rawRowCheck7538]

theorem rawRowCheck7539 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form2 = rawRow7539 := by decide +kernel

theorem rowCheck7539 : row7539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7539 := by decide +kernel

theorem rowEval7539 (x : Key → ℝ) : Integer.Sparse.eval row7539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7539, Integer.Sparse.eval_collectBalanced, rawRowCheck7539]

theorem rawRowCheck7540 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form2 = rawRow7540 := by decide +kernel

theorem rowCheck7540 : row7540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7540 := by decide +kernel

theorem rowEval7540 (x : Key → ℝ) : Integer.Sparse.eval row7540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7540, Integer.Sparse.eval_collectBalanced, rawRowCheck7540]

theorem rawRowCheck7541 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form2 = rawRow7541 := by decide +kernel

theorem rowCheck7541 : row7541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7541 := by decide +kernel

theorem rowEval7541 (x : Key → ℝ) : Integer.Sparse.eval row7541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7541, Integer.Sparse.eval_collectBalanced, rawRowCheck7541]

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

theorem rawRowCheck7646 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7646 := by decide +kernel

theorem rowCheck7646 : row7646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7646 := by decide +kernel

theorem rowEval7646 (x : Key → ℝ) : Integer.Sparse.eval row7646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7646, Integer.Sparse.eval_collectBalanced, rawRowCheck7646]

theorem rawRowCheck7647 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7647 := by decide +kernel

theorem rowCheck7647 : row7647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7647 := by decide +kernel

theorem rowEval7647 (x : Key → ℝ) : Integer.Sparse.eval row7647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7647, Integer.Sparse.eval_collectBalanced, rawRowCheck7647]

theorem rawRowCheck7648 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7648 := by decide +kernel

theorem rowCheck7648 : row7648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7648 := by decide +kernel

theorem rowEval7648 (x : Key → ℝ) : Integer.Sparse.eval row7648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7648, Integer.Sparse.eval_collectBalanced, rawRowCheck7648]

theorem rawRowCheck7649 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form2 = rawRow7649 := by decide +kernel

theorem rowCheck7649 : row7649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7649 := by decide +kernel

theorem rowEval7649 (x : Key → ℝ) : Integer.Sparse.eval row7649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7649, Integer.Sparse.eval_collectBalanced, rawRowCheck7649]

theorem rawRowCheck7650 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form2 = rawRow7650 := by decide +kernel

theorem rowCheck7650 : row7650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7650 := by decide +kernel

theorem rowEval7650 (x : Key → ℝ) : Integer.Sparse.eval row7650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7650, Integer.Sparse.eval_collectBalanced, rawRowCheck7650]

theorem rawRowCheck7651 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form2 = rawRow7651 := by decide +kernel

theorem rowCheck7651 : row7651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7651 := by decide +kernel

theorem rowEval7651 (x : Key → ℝ) : Integer.Sparse.eval row7651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7651, Integer.Sparse.eval_collectBalanced, rawRowCheck7651]

theorem rawRowCheck7652 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form2 = rawRow7652 := by decide +kernel

theorem rowCheck7652 : row7652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7652 := by decide +kernel

theorem rowEval7652 (x : Key → ℝ) : Integer.Sparse.eval row7652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7652, Integer.Sparse.eval_collectBalanced, rawRowCheck7652]

theorem rawRowCheck7653 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form2 = rawRow7653 := by decide +kernel

theorem rowCheck7653 : row7653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7653 := by decide +kernel

theorem rowEval7653 (x : Key → ℝ) : Integer.Sparse.eval row7653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7653, Integer.Sparse.eval_collectBalanced, rawRowCheck7653]

theorem rawRowCheck7654 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form2 = rawRow7654 := by decide +kernel

theorem rowCheck7654 : row7654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7654 := by decide +kernel

theorem rowEval7654 (x : Key → ℝ) : Integer.Sparse.eval row7654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7654, Integer.Sparse.eval_collectBalanced, rawRowCheck7654]

theorem rawRowCheck7655 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form2 = rawRow7655 := by decide +kernel

theorem rowCheck7655 : row7655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7655 := by decide +kernel

theorem rowEval7655 (x : Key → ℝ) : Integer.Sparse.eval row7655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7655, Integer.Sparse.eval_collectBalanced, rawRowCheck7655]

theorem rawRowCheck7656 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form2 = rawRow7656 := by decide +kernel

theorem rowCheck7656 : row7656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7656 := by decide +kernel

theorem rowEval7656 (x : Key → ℝ) : Integer.Sparse.eval row7656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7656, Integer.Sparse.eval_collectBalanced, rawRowCheck7656]

theorem rawRowCheck7657 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form2 = rawRow7657 := by decide +kernel

theorem rowCheck7657 : row7657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7657 := by decide +kernel

theorem rowEval7657 (x : Key → ℝ) : Integer.Sparse.eval row7657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7657, Integer.Sparse.eval_collectBalanced, rawRowCheck7657]

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

theorem rawRowCheck8873 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow8873 := by decide +kernel

theorem rowCheck8873 : row8873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8873 := by decide +kernel

theorem rowEval8873 (x : Key → ℝ) : Integer.Sparse.eval row8873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8873, Integer.Sparse.eval_collectBalanced, rawRowCheck8873]

theorem rawRowCheck8874 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow8874 := by decide +kernel

theorem rowCheck8874 : row8874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8874 := by decide +kernel

theorem rowEval8874 (x : Key → ℝ) : Integer.Sparse.eval row8874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8874, Integer.Sparse.eval_collectBalanced, rawRowCheck8874]

theorem rawRowCheck8875 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow8875 := by decide +kernel

theorem rowCheck8875 : row8875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8875 := by decide +kernel

theorem rowEval8875 (x : Key → ℝ) : Integer.Sparse.eval row8875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8875, Integer.Sparse.eval_collectBalanced, rawRowCheck8875]

theorem rawRowCheck8876 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8876 := by decide +kernel

theorem rowCheck8876 : row8876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8876 := by decide +kernel

theorem rowEval8876 (x : Key → ℝ) : Integer.Sparse.eval row8876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8876, Integer.Sparse.eval_collectBalanced, rawRowCheck8876]

theorem rawRowCheck8877 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form2 = rawRow8877 := by decide +kernel

theorem rowCheck8877 : row8877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8877 := by decide +kernel

theorem rowEval8877 (x : Key → ℝ) : Integer.Sparse.eval row8877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8877, Integer.Sparse.eval_collectBalanced, rawRowCheck8877]

theorem rawRowCheck8878 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form2 = rawRow8878 := by decide +kernel

theorem rowCheck8878 : row8878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8878 := by decide +kernel

theorem rowEval8878 (x : Key → ℝ) : Integer.Sparse.eval row8878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8878, Integer.Sparse.eval_collectBalanced, rawRowCheck8878]

theorem rawRowCheck8879 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form2 = rawRow8879 := by decide +kernel

theorem rowCheck8879 : row8879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8879 := by decide +kernel

theorem rowEval8879 (x : Key → ℝ) : Integer.Sparse.eval row8879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8879, Integer.Sparse.eval_collectBalanced, rawRowCheck8879]

theorem rawRowCheck8880 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form2 = rawRow8880 := by decide +kernel

theorem rowCheck8880 : row8880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8880 := by decide +kernel

theorem rowEval8880 (x : Key → ℝ) : Integer.Sparse.eval row8880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8880, Integer.Sparse.eval_collectBalanced, rawRowCheck8880]

theorem rawRowCheck8881 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form2 = rawRow8881 := by decide +kernel

theorem rowCheck8881 : row8881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8881 := by decide +kernel

theorem rowEval8881 (x : Key → ℝ) : Integer.Sparse.eval row8881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8881, Integer.Sparse.eval_collectBalanced, rawRowCheck8881]

theorem rawRowCheck8882 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form2 = rawRow8882 := by decide +kernel

theorem rowCheck8882 : row8882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8882 := by decide +kernel

theorem rowEval8882 (x : Key → ℝ) : Integer.Sparse.eval row8882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8882, Integer.Sparse.eval_collectBalanced, rawRowCheck8882]

theorem rawRowCheck8883 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form2 = rawRow8883 := by decide +kernel

theorem rowCheck8883 : row8883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8883 := by decide +kernel

theorem rowEval8883 (x : Key → ℝ) : Integer.Sparse.eval row8883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8883, Integer.Sparse.eval_collectBalanced, rawRowCheck8883]

theorem rawRowCheck8884 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form2 = rawRow8884 := by decide +kernel

theorem rowCheck8884 : row8884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8884 := by decide +kernel

theorem rowEval8884 (x : Key → ℝ) : Integer.Sparse.eval row8884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8884, Integer.Sparse.eval_collectBalanced, rawRowCheck8884]

theorem rawRowCheck8885 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form2 = rawRow8885 := by decide +kernel

theorem rowCheck8885 : row8885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8885 := by decide +kernel

theorem rowEval8885 (x : Key → ℝ) : Integer.Sparse.eval row8885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8885, Integer.Sparse.eval_collectBalanced, rawRowCheck8885]

theorem rawRowCheck8886 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow8886 := by decide +kernel

theorem rowCheck8886 : row8886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8886 := by decide +kernel

theorem rowEval8886 (x : Key → ℝ) : Integer.Sparse.eval row8886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8886, Integer.Sparse.eval_collectBalanced, rawRowCheck8886]

theorem rawRowCheck8887 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow8887 := by decide +kernel

theorem rowCheck8887 : row8887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8887 := by decide +kernel

theorem rowEval8887 (x : Key → ℝ) : Integer.Sparse.eval row8887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8887, Integer.Sparse.eval_collectBalanced, rawRowCheck8887]

theorem rawRowCheck8888 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow8888 := by decide +kernel

theorem rowCheck8888 : row8888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8888 := by decide +kernel

theorem rowEval8888 (x : Key → ℝ) : Integer.Sparse.eval row8888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8888, Integer.Sparse.eval_collectBalanced, rawRowCheck8888]

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

theorem entryCheck12_2 : entry12_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_2 k)) := by decide +kernel

theorem rowsSound12_2 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7526 x
  · exact rowEval7527 x
  · exact rowEval7528 x
  · exact rowEval7529 x
  · exact rowEval8765 x
  · exact rowEval8766 x
  · exact rowEval8767 x
  · exact rowEval8768 x

theorem entryEval12_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_2 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck12_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_2]

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

theorem rawRowCheck9073 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow9073 := by decide +kernel

theorem rowCheck9073 : row9073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9073 := by decide +kernel

theorem rowEval9073 (x : Key → ℝ) : Integer.Sparse.eval row9073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9073, Integer.Sparse.eval_collectBalanced, rawRowCheck9073]

theorem rawRowCheck9074 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow9074 := by decide +kernel

theorem rowCheck9074 : row9074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9074 := by decide +kernel

theorem rowEval9074 (x : Key → ℝ) : Integer.Sparse.eval row9074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9074, Integer.Sparse.eval_collectBalanced, rawRowCheck9074]

theorem rawRowCheck9075 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow9075 := by decide +kernel

theorem rowCheck9075 : row9075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9075 := by decide +kernel

theorem rowEval9075 (x : Key → ℝ) : Integer.Sparse.eval row9075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9075, Integer.Sparse.eval_collectBalanced, rawRowCheck9075]

theorem rawRowCheck9076 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow9076 := by decide +kernel

theorem rowCheck9076 : row9076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9076 := by decide +kernel

theorem rowEval9076 (x : Key → ℝ) : Integer.Sparse.eval row9076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9076, Integer.Sparse.eval_collectBalanced, rawRowCheck9076]

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

theorem entryCheck13_2 : entry13_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_2 k)) := by decide +kernel

theorem rowsSound13_2 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8873 x
  · exact rowEval8874 x
  · exact rowEval8875 x
  · exact rowEval8876 x
  · exact rowEval8877 x
  · exact rowEval8878 x
  · exact rowEval8879 x
  · exact rowEval8880 x
  · exact rowEval8881 x
  · exact rowEval8882 x
  · exact rowEval8883 x
  · exact rowEval8884 x
  · exact rowEval8885 x
  · exact rowEval8886 x
  · exact rowEval8887 x
  · exact rowEval8888 x

theorem entryEval13_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_2 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck13_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_2]

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

theorem rawRowCheck9197 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form2 = rawRow9197 := by decide +kernel

theorem rowCheck9197 : row9197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9197 := by decide +kernel

theorem rowEval9197 (x : Key → ℝ) : Integer.Sparse.eval row9197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9197, Integer.Sparse.eval_collectBalanced, rawRowCheck9197]

theorem rawRowCheck9198 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form2 = rawRow9198 := by decide +kernel

theorem rowCheck9198 : row9198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9198 := by decide +kernel

theorem rowEval9198 (x : Key → ℝ) : Integer.Sparse.eval row9198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9198, Integer.Sparse.eval_collectBalanced, rawRowCheck9198]

theorem rawRowCheck9199 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form2 = rawRow9199 := by decide +kernel

theorem rowCheck9199 : row9199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9199 := by decide +kernel

theorem rowEval9199 (x : Key → ℝ) : Integer.Sparse.eval row9199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9199, Integer.Sparse.eval_collectBalanced, rawRowCheck9199]

theorem rawRowCheck9200 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9200 := by decide +kernel

theorem rowCheck9200 : row9200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9200 := by decide +kernel

theorem rowEval9200 (x : Key → ℝ) : Integer.Sparse.eval row9200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9200, Integer.Sparse.eval_collectBalanced, rawRowCheck9200]

theorem rawRowCheck9201 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9201 := by decide +kernel

theorem rowCheck9201 : row9201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9201 := by decide +kernel

theorem rowEval9201 (x : Key → ℝ) : Integer.Sparse.eval row9201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9201, Integer.Sparse.eval_collectBalanced, rawRowCheck9201]

theorem rawRowCheck9202 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9202 := by decide +kernel

theorem rowCheck9202 : row9202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9202 := by decide +kernel

theorem rowEval9202 (x : Key → ℝ) : Integer.Sparse.eval row9202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9202, Integer.Sparse.eval_collectBalanced, rawRowCheck9202]

theorem rawRowCheck9203 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9203 := by decide +kernel

theorem rowCheck9203 : row9203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9203 := by decide +kernel

theorem rowEval9203 (x : Key → ℝ) : Integer.Sparse.eval row9203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9203, Integer.Sparse.eval_collectBalanced, rawRowCheck9203]

theorem rawRowCheck9204 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form2 = rawRow9204 := by decide +kernel

theorem rowCheck9204 : row9204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9204 := by decide +kernel

theorem rowEval9204 (x : Key → ℝ) : Integer.Sparse.eval row9204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9204, Integer.Sparse.eval_collectBalanced, rawRowCheck9204]

theorem rawRowCheck9205 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form2 = rawRow9205 := by decide +kernel

theorem rowCheck9205 : row9205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9205 := by decide +kernel

theorem rowEval9205 (x : Key → ℝ) : Integer.Sparse.eval row9205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9205, Integer.Sparse.eval_collectBalanced, rawRowCheck9205]

theorem rawRowCheck9206 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form2 = rawRow9206 := by decide +kernel

theorem rowCheck9206 : row9206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9206 := by decide +kernel

theorem rowEval9206 (x : Key → ℝ) : Integer.Sparse.eval row9206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9206, Integer.Sparse.eval_collectBalanced, rawRowCheck9206]

theorem rawRowCheck9207 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form2 = rawRow9207 := by decide +kernel

theorem rowCheck9207 : row9207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9207 := by decide +kernel

theorem rowEval9207 (x : Key → ℝ) : Integer.Sparse.eval row9207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9207, Integer.Sparse.eval_collectBalanced, rawRowCheck9207]

theorem rawRowCheck9208 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form2 = rawRow9208 := by decide +kernel

theorem rowCheck9208 : row9208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9208 := by decide +kernel

theorem rowEval9208 (x : Key → ℝ) : Integer.Sparse.eval row9208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9208, Integer.Sparse.eval_collectBalanced, rawRowCheck9208]

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

theorem entryCheck14_2 : entry14_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_2 k)) := by decide +kernel

theorem rowsSound14_2 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7414 x
  · exact rowEval7415 x
  · exact rowEval7416 x
  · exact rowEval7417 x
  · exact rowEval9073 x
  · exact rowEval9074 x
  · exact rowEval9075 x
  · exact rowEval9076 x

theorem entryEval14_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_2 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck14_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_2]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck9389 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form2 = rawRow9389 := by decide +kernel

theorem rowCheck9389 : row9389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9389 := by decide +kernel

theorem rowEval9389 (x : Key → ℝ) : Integer.Sparse.eval row9389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9389, Integer.Sparse.eval_collectBalanced, rawRowCheck9389]

theorem rawRowCheck9390 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form2 = rawRow9390 := by decide +kernel

theorem rowCheck9390 : row9390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9390 := by decide +kernel

theorem rowEval9390 (x : Key → ℝ) : Integer.Sparse.eval row9390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9390, Integer.Sparse.eval_collectBalanced, rawRowCheck9390]

theorem rawRowCheck9391 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form2 = rawRow9391 := by decide +kernel

theorem rowCheck9391 : row9391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9391 := by decide +kernel

theorem rowEval9391 (x : Key → ℝ) : Integer.Sparse.eval row9391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9391, Integer.Sparse.eval_collectBalanced, rawRowCheck9391]

theorem rawRowCheck9392 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form2 = rawRow9392 := by decide +kernel

theorem rowCheck9392 : row9392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9392 := by decide +kernel

theorem rowEval9392 (x : Key → ℝ) : Integer.Sparse.eval row9392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9392, Integer.Sparse.eval_collectBalanced, rawRowCheck9392]

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

theorem entryCheck15_2 : entry15_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_2 k)) := by decide +kernel

theorem rowsSound15_2 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8677 x
  · exact rowEval8678 x
  · exact rowEval8679 x
  · exact rowEval8680 x
  · exact rowEval9197 x
  · exact rowEval9198 x
  · exact rowEval9199 x
  · exact rowEval9200 x
  · exact rowEval9201 x
  · exact rowEval9202 x
  · exact rowEval9203 x
  · exact rowEval9204 x
  · exact rowEval9205 x
  · exact rowEval9206 x
  · exact rowEval9207 x
  · exact rowEval9208 x

theorem entryEval15_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_2 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck15_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_2]

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

theorem rawRowCheck9549 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form2 = rawRow9549 := by decide +kernel

theorem rowCheck9549 : row9549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9549 := by decide +kernel

theorem rowEval9549 (x : Key → ℝ) : Integer.Sparse.eval row9549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9549, Integer.Sparse.eval_collectBalanced, rawRowCheck9549]

theorem rawRowCheck9550 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form2 = rawRow9550 := by decide +kernel

theorem rowCheck9550 : row9550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9550 := by decide +kernel

theorem rowEval9550 (x : Key → ℝ) : Integer.Sparse.eval row9550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9550, Integer.Sparse.eval_collectBalanced, rawRowCheck9550]

theorem rawRowCheck9551 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form2 = rawRow9551 := by decide +kernel

theorem rowCheck9551 : row9551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9551 := by decide +kernel

theorem rowEval9551 (x : Key → ℝ) : Integer.Sparse.eval row9551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9551, Integer.Sparse.eval_collectBalanced, rawRowCheck9551]

theorem rawRowCheck9552 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form2 = rawRow9552 := by decide +kernel

theorem rowCheck9552 : row9552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9552 := by decide +kernel

theorem rowEval9552 (x : Key → ℝ) : Integer.Sparse.eval row9552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9552, Integer.Sparse.eval_collectBalanced, rawRowCheck9552]

theorem rawRowCheck9553 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form2 = rawRow9553 := by decide +kernel

theorem rowCheck9553 : row9553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9553 := by decide +kernel

theorem rowEval9553 (x : Key → ℝ) : Integer.Sparse.eval row9553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9553, Integer.Sparse.eval_collectBalanced, rawRowCheck9553]

theorem rawRowCheck9554 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form2 = rawRow9554 := by decide +kernel

theorem rowCheck9554 : row9554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9554 := by decide +kernel

theorem rowEval9554 (x : Key → ℝ) : Integer.Sparse.eval row9554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9554, Integer.Sparse.eval_collectBalanced, rawRowCheck9554]

theorem rawRowCheck9555 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form2 = rawRow9555 := by decide +kernel

theorem rowCheck9555 : row9555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9555 := by decide +kernel

theorem rowEval9555 (x : Key → ℝ) : Integer.Sparse.eval row9555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9555, Integer.Sparse.eval_collectBalanced, rawRowCheck9555]

theorem rawRowCheck9556 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form2 = rawRow9556 := by decide +kernel

theorem rowCheck9556 : row9556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9556 := by decide +kernel

theorem rowEval9556 (x : Key → ℝ) : Integer.Sparse.eval row9556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9556, Integer.Sparse.eval_collectBalanced, rawRowCheck9556]

theorem rawRowCheck9557 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form2 = rawRow9557 := by decide +kernel

theorem rowCheck9557 : row9557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9557 := by decide +kernel

theorem rowEval9557 (x : Key → ℝ) : Integer.Sparse.eval row9557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9557, Integer.Sparse.eval_collectBalanced, rawRowCheck9557]

theorem rawRowCheck9558 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form2 = rawRow9558 := by decide +kernel

theorem rowCheck9558 : row9558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9558 := by decide +kernel

theorem rowEval9558 (x : Key → ℝ) : Integer.Sparse.eval row9558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9558, Integer.Sparse.eval_collectBalanced, rawRowCheck9558]

theorem rawRowCheck9559 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form2 = rawRow9559 := by decide +kernel

theorem rowCheck9559 : row9559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9559 := by decide +kernel

theorem rowEval9559 (x : Key → ℝ) : Integer.Sparse.eval row9559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9559, Integer.Sparse.eval_collectBalanced, rawRowCheck9559]

theorem rawRowCheck9560 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form2 = rawRow9560 := by decide +kernel

theorem rowCheck9560 : row9560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9560 := by decide +kernel

theorem rowEval9560 (x : Key → ℝ) : Integer.Sparse.eval row9560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9560, Integer.Sparse.eval_collectBalanced, rawRowCheck9560]

theorem rawRowCheck9561 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form2 = rawRow9561 := by decide +kernel

theorem rowCheck9561 : row9561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9561 := by decide +kernel

theorem rowEval9561 (x : Key → ℝ) : Integer.Sparse.eval row9561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9561, Integer.Sparse.eval_collectBalanced, rawRowCheck9561]

theorem rawRowCheck9562 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form2 = rawRow9562 := by decide +kernel

theorem rowCheck9562 : row9562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9562 := by decide +kernel

theorem rowEval9562 (x : Key → ℝ) : Integer.Sparse.eval row9562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9562, Integer.Sparse.eval_collectBalanced, rawRowCheck9562]

theorem rawRowCheck9563 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form2 = rawRow9563 := by decide +kernel

theorem rowCheck9563 : row9563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9563 := by decide +kernel

theorem rowEval9563 (x : Key → ℝ) : Integer.Sparse.eval row9563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9563, Integer.Sparse.eval_collectBalanced, rawRowCheck9563]

theorem rawRowCheck9564 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form2 = rawRow9564 := by decide +kernel

theorem rowCheck9564 : row9564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9564 := by decide +kernel

theorem rowEval9564 (x : Key → ℝ) : Integer.Sparse.eval row9564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9564, Integer.Sparse.eval_collectBalanced, rawRowCheck9564]

theorem rawRowCheck9565 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form2 = rawRow9565 := by decide +kernel

theorem rowCheck9565 : row9565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9565 := by decide +kernel

theorem rowEval9565 (x : Key → ℝ) : Integer.Sparse.eval row9565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9565, Integer.Sparse.eval_collectBalanced, rawRowCheck9565]

theorem rawRowCheck9566 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form2 = rawRow9566 := by decide +kernel

theorem rowCheck9566 : row9566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9566 := by decide +kernel

theorem rowEval9566 (x : Key → ℝ) : Integer.Sparse.eval row9566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9566, Integer.Sparse.eval_collectBalanced, rawRowCheck9566]

theorem rawRowCheck9567 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form2 = rawRow9567 := by decide +kernel

theorem rowCheck9567 : row9567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9567 := by decide +kernel

theorem rowEval9567 (x : Key → ℝ) : Integer.Sparse.eval row9567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9567, Integer.Sparse.eval_collectBalanced, rawRowCheck9567]

theorem rawRowCheck9568 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form2 = rawRow9568 := by decide +kernel

theorem rowCheck9568 : row9568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9568 := by decide +kernel

theorem rowEval9568 (x : Key → ℝ) : Integer.Sparse.eval row9568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9568, Integer.Sparse.eval_collectBalanced, rawRowCheck9568]

theorem rawRowCheck9569 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form2 = rawRow9569 := by decide +kernel

theorem rowCheck9569 : row9569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9569 := by decide +kernel

theorem rowEval9569 (x : Key → ℝ) : Integer.Sparse.eval row9569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9569, Integer.Sparse.eval_collectBalanced, rawRowCheck9569]

theorem rawRowCheck9570 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form2 = rawRow9570 := by decide +kernel

theorem rowCheck9570 : row9570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9570 := by decide +kernel

theorem rowEval9570 (x : Key → ℝ) : Integer.Sparse.eval row9570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9570, Integer.Sparse.eval_collectBalanced, rawRowCheck9570]

theorem rawRowCheck9571 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form2 = rawRow9571 := by decide +kernel

theorem rowCheck9571 : row9571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9571 := by decide +kernel

theorem rowEval9571 (x : Key → ℝ) : Integer.Sparse.eval row9571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9571, Integer.Sparse.eval_collectBalanced, rawRowCheck9571]

theorem rawRowCheck9572 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form2 = rawRow9572 := by decide +kernel

theorem rowCheck9572 : row9572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9572 := by decide +kernel

theorem rowEval9572 (x : Key → ℝ) : Integer.Sparse.eval row9572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9572, Integer.Sparse.eval_collectBalanced, rawRowCheck9572]

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

theorem entryCheck16_2 : entry16_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_2 k)) := by decide +kernel

theorem rowsSound16_2 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval9389 x
  · exact rowEval9390 x
  · exact rowEval9391 x
  · exact rowEval9392 x
  · exact rowEval7462 x
  · exact rowEval7463 x
  · exact rowEval7464 x
  · exact rowEval7465 x

theorem entryEval16_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_2 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck16_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_2]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9981 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2 = rawRow9981 := by decide +kernel

theorem rowCheck9981 : row9981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9981 := by decide +kernel

theorem rowEval9981 (x : Key → ℝ) : Integer.Sparse.eval row9981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9981, Integer.Sparse.eval_collectBalanced, rawRowCheck9981]

theorem rawRowCheck9982 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2 = rawRow9982 := by decide +kernel

theorem rowCheck9982 : row9982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9982 := by decide +kernel

theorem rowEval9982 (x : Key → ℝ) : Integer.Sparse.eval row9982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9982, Integer.Sparse.eval_collectBalanced, rawRowCheck9982]

theorem rawRowCheck9983 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2 = rawRow9983 := by decide +kernel

theorem rowCheck9983 : row9983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9983 := by decide +kernel

theorem rowEval9983 (x : Key → ℝ) : Integer.Sparse.eval row9983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9983, Integer.Sparse.eval_collectBalanced, rawRowCheck9983]

end MUB6.Certificate.GramRows

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

theorem entryCheck17_2 : entry17_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_2 k)) := by decide +kernel

theorem rowsSound17_2 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval9549 x
  · exact rowEval9550 x
  · exact rowEval9551 x
  · exact rowEval9552 x
  · exact rowEval9553 x
  · exact rowEval9554 x
  · exact rowEval9555 x
  · exact rowEval9556 x
  · exact rowEval9557 x
  · exact rowEval9558 x
  · exact rowEval9559 x
  · exact rowEval9560 x
  · exact rowEval9561 x
  · exact rowEval9562 x
  · exact rowEval9563 x
  · exact rowEval9564 x
  · exact rowEval9565 x
  · exact rowEval9566 x
  · exact rowEval9567 x
  · exact rowEval9568 x
  · exact rowEval9569 x
  · exact rowEval9570 x
  · exact rowEval9571 x
  · exact rowEval9572 x

theorem entryEval17_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_2 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck17_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_2]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9984 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2 = rawRow9984 := by decide +kernel

theorem rowCheck9984 : row9984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9984 := by decide +kernel

theorem rowEval9984 (x : Key → ℝ) : Integer.Sparse.eval row9984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9984, Integer.Sparse.eval_collectBalanced, rawRowCheck9984]

theorem rawRowCheck9985 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2 = rawRow9985 := by decide +kernel

theorem rowCheck9985 : row9985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9985 := by decide +kernel

theorem rowEval9985 (x : Key → ℝ) : Integer.Sparse.eval row9985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9985, Integer.Sparse.eval_collectBalanced, rawRowCheck9985]

theorem rawRowCheck9986 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2 = rawRow9986 := by decide +kernel

theorem rowCheck9986 : row9986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9986 := by decide +kernel

theorem rowEval9986 (x : Key → ℝ) : Integer.Sparse.eval row9986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9986, Integer.Sparse.eval_collectBalanced, rawRowCheck9986]

theorem rawRowCheck9987 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9987 := by decide +kernel

theorem rowCheck9987 : row9987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9987 := by decide +kernel

theorem rowEval9987 (x : Key → ℝ) : Integer.Sparse.eval row9987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9987, Integer.Sparse.eval_collectBalanced, rawRowCheck9987]

theorem rawRowCheck9988 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9988 := by decide +kernel

theorem rowCheck9988 : row9988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9988 := by decide +kernel

theorem rowEval9988 (x : Key → ℝ) : Integer.Sparse.eval row9988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9988, Integer.Sparse.eval_collectBalanced, rawRowCheck9988]

theorem rawRowCheck9989 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9989 := by decide +kernel

theorem rowCheck9989 : row9989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9989 := by decide +kernel

theorem rowEval9989 (x : Key → ℝ) : Integer.Sparse.eval row9989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9989, Integer.Sparse.eval_collectBalanced, rawRowCheck9989]

theorem rawRowCheck9990 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9990 := by decide +kernel

theorem rowCheck9990 : row9990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9990 := by decide +kernel

theorem rowEval9990 (x : Key → ℝ) : Integer.Sparse.eval row9990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9990, Integer.Sparse.eval_collectBalanced, rawRowCheck9990]

theorem rawRowCheck9991 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2 = rawRow9991 := by decide +kernel

theorem rowCheck9991 : row9991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9991 := by decide +kernel

theorem rowEval9991 (x : Key → ℝ) : Integer.Sparse.eval row9991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9991, Integer.Sparse.eval_collectBalanced, rawRowCheck9991]

theorem rawRowCheck9992 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2 = rawRow9992 := by decide +kernel

theorem rowCheck9992 : row9992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9992 := by decide +kernel

theorem rowEval9992 (x : Key → ℝ) : Integer.Sparse.eval row9992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9992, Integer.Sparse.eval_collectBalanced, rawRowCheck9992]

theorem rawRowCheck9993 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form2 = rawRow9993 := by decide +kernel

theorem rowCheck9993 : row9993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9993 := by decide +kernel

theorem rowEval9993 (x : Key → ℝ) : Integer.Sparse.eval row9993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9993, Integer.Sparse.eval_collectBalanced, rawRowCheck9993]

theorem rawRowCheck9994 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form2 = rawRow9994 := by decide +kernel

theorem rowCheck9994 : row9994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9994 := by decide +kernel

theorem rowEval9994 (x : Key → ℝ) : Integer.Sparse.eval row9994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9994, Integer.Sparse.eval_collectBalanced, rawRowCheck9994]

theorem rawRowCheck9995 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form2 = rawRow9995 := by decide +kernel

theorem rowCheck9995 : row9995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9995 := by decide +kernel

theorem rowEval9995 (x : Key → ℝ) : Integer.Sparse.eval row9995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9995, Integer.Sparse.eval_collectBalanced, rawRowCheck9995]

theorem rawRowCheck9996 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9996 := by decide +kernel

theorem rowCheck9996 : row9996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9996 := by decide +kernel

theorem rowEval9996 (x : Key → ℝ) : Integer.Sparse.eval row9996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9996, Integer.Sparse.eval_collectBalanced, rawRowCheck9996]

theorem rawRowCheck9997 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9997 := by decide +kernel

theorem rowCheck9997 : row9997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9997 := by decide +kernel

theorem rowEval9997 (x : Key → ℝ) : Integer.Sparse.eval row9997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9997, Integer.Sparse.eval_collectBalanced, rawRowCheck9997]

theorem rawRowCheck9998 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9998 := by decide +kernel

theorem rowCheck9998 : row9998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9998 := by decide +kernel

theorem rowEval9998 (x : Key → ℝ) : Integer.Sparse.eval row9998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9998, Integer.Sparse.eval_collectBalanced, rawRowCheck9998]

theorem rawRowCheck9999 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9999 := by decide +kernel

theorem rowCheck9999 : row9999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9999 := by decide +kernel

theorem rowEval9999 (x : Key → ℝ) : Integer.Sparse.eval row9999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9999, Integer.Sparse.eval_collectBalanced, rawRowCheck9999]

theorem rawRowCheck10000 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form2 = rawRow10000 := by decide +kernel

theorem rowCheck10000 : row10000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10000 := by decide +kernel

theorem rowEval10000 (x : Key → ℝ) : Integer.Sparse.eval row10000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10000, Integer.Sparse.eval_collectBalanced, rawRowCheck10000]

theorem rawRowCheck10001 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form2 = rawRow10001 := by decide +kernel

theorem rowCheck10001 : row10001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10001 := by decide +kernel

theorem rowEval10001 (x : Key → ℝ) : Integer.Sparse.eval row10001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck10001, Integer.Sparse.eval_collectBalanced, rawRowCheck10001]

theorem rawRowCheck10002 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form2 = rawRow10002 := by decide +kernel

theorem rowCheck10002 : row10002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10002 := by decide +kernel

theorem rowEval10002 (x : Key → ℝ) : Integer.Sparse.eval row10002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10002, Integer.Sparse.eval_collectBalanced, rawRowCheck10002]

theorem rawRowCheck10003 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form2 = rawRow10003 := by decide +kernel

theorem rowCheck10003 : row10003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10003 := by decide +kernel

theorem rowEval10003 (x : Key → ℝ) : Integer.Sparse.eval row10003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10003, Integer.Sparse.eval_collectBalanced, rawRowCheck10003]

theorem rawRowCheck10004 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form2 = rawRow10004 := by decide +kernel

theorem rowCheck10004 : row10004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10004 := by decide +kernel

theorem rowEval10004 (x : Key → ℝ) : Integer.Sparse.eval row10004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck10004, Integer.Sparse.eval_collectBalanced, rawRowCheck10004]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck10409 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form2 = rawRow10409 := by decide +kernel

theorem rowCheck10409 : row10409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10409 := by decide +kernel

theorem rowEval10409 (x : Key → ℝ) : Integer.Sparse.eval row10409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10409, Integer.Sparse.eval_collectBalanced, rawRowCheck10409]

theorem rawRowCheck10410 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form2 = rawRow10410 := by decide +kernel

theorem rowCheck10410 : row10410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10410 := by decide +kernel

theorem rowEval10410 (x : Key → ℝ) : Integer.Sparse.eval row10410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10410, Integer.Sparse.eval_collectBalanced, rawRowCheck10410]

theorem rawRowCheck10411 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form2 = rawRow10411 := by decide +kernel

theorem rowCheck10411 : row10411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10411 := by decide +kernel

theorem rowEval10411 (x : Key → ℝ) : Integer.Sparse.eval row10411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10411, Integer.Sparse.eval_collectBalanced, rawRowCheck10411]

theorem rawRowCheck10412 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form2 = rawRow10412 := by decide +kernel

theorem rowCheck10412 : row10412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10412 := by decide +kernel

theorem rowEval10412 (x : Key → ℝ) : Integer.Sparse.eval row10412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10412, Integer.Sparse.eval_collectBalanced, rawRowCheck10412]

theorem rawRowCheck10413 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form2 = rawRow10413 := by decide +kernel

theorem rowCheck10413 : row10413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10413 := by decide +kernel

theorem rowEval10413 (x : Key → ℝ) : Integer.Sparse.eval row10413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10413, Integer.Sparse.eval_collectBalanced, rawRowCheck10413]

theorem rawRowCheck10414 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form2 = rawRow10414 := by decide +kernel

theorem rowCheck10414 : row10414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10414 := by decide +kernel

theorem rowEval10414 (x : Key → ℝ) : Integer.Sparse.eval row10414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10414, Integer.Sparse.eval_collectBalanced, rawRowCheck10414]

theorem rawRowCheck10415 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form2 = rawRow10415 := by decide +kernel

theorem rowCheck10415 : row10415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10415 := by decide +kernel

theorem rowEval10415 (x : Key → ℝ) : Integer.Sparse.eval row10415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10415, Integer.Sparse.eval_collectBalanced, rawRowCheck10415]

theorem rawRowCheck10416 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form2 = rawRow10416 := by decide +kernel

theorem rowCheck10416 : row10416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10416 := by decide +kernel

theorem rowEval10416 (x : Key → ℝ) : Integer.Sparse.eval row10416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10416, Integer.Sparse.eval_collectBalanced, rawRowCheck10416]

theorem rawRowCheck10417 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form2 = rawRow10417 := by decide +kernel

theorem rowCheck10417 : row10417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10417 := by decide +kernel

theorem rowEval10417 (x : Key → ℝ) : Integer.Sparse.eval row10417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10417, Integer.Sparse.eval_collectBalanced, rawRowCheck10417]

theorem rawRowCheck10418 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form2 = rawRow10418 := by decide +kernel

theorem rowCheck10418 : row10418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10418 := by decide +kernel

theorem rowEval10418 (x : Key → ℝ) : Integer.Sparse.eval row10418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10418, Integer.Sparse.eval_collectBalanced, rawRowCheck10418]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck18_2 : entry18_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_2 k)) := by decide +kernel

theorem rowsSound18_2 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval9981 x
  · exact rowEval9982 x
  · exact rowEval9983 x
  · exact rowEval9984 x
  · exact rowEval9985 x
  · exact rowEval9986 x
  · exact rowEval9987 x
  · exact rowEval9988 x
  · exact rowEval9989 x
  · exact rowEval9990 x
  · exact rowEval9991 x
  · exact rowEval9992 x
  · exact rowEval9993 x
  · exact rowEval9994 x
  · exact rowEval9995 x
  · exact rowEval9996 x
  · exact rowEval9997 x
  · exact rowEval9998 x
  · exact rowEval9999 x
  · exact rowEval10000 x
  · exact rowEval10001 x
  · exact rowEval10002 x
  · exact rowEval10003 x
  · exact rowEval10004 x

theorem entryEval18_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_2 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck18_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_2]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck10599 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow10599 := by decide +kernel

theorem rowCheck10599 : row10599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10599 := by decide +kernel

theorem rowEval10599 (x : Key → ℝ) : Integer.Sparse.eval row10599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10599, Integer.Sparse.eval_collectBalanced, rawRowCheck10599]

theorem rawRowCheck10600 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow10600 := by decide +kernel

theorem rowCheck10600 : row10600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10600 := by decide +kernel

theorem rowEval10600 (x : Key → ℝ) : Integer.Sparse.eval row10600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10600, Integer.Sparse.eval_collectBalanced, rawRowCheck10600]

theorem rawRowCheck10601 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow10601 := by decide +kernel

theorem rowCheck10601 : row10601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10601 := by decide +kernel

theorem rowEval10601 (x : Key → ℝ) : Integer.Sparse.eval row10601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10601, Integer.Sparse.eval_collectBalanced, rawRowCheck10601]

theorem rawRowCheck10602 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow10602 := by decide +kernel

theorem rowCheck10602 : row10602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10602 := by decide +kernel

theorem rowEval10602 (x : Key → ℝ) : Integer.Sparse.eval row10602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10602, Integer.Sparse.eval_collectBalanced, rawRowCheck10602]

theorem rawRowCheck10603 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow10603 := by decide +kernel

theorem rowCheck10603 : row10603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10603 := by decide +kernel

theorem rowEval10603 (x : Key → ℝ) : Integer.Sparse.eval row10603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10603, Integer.Sparse.eval_collectBalanced, rawRowCheck10603]

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

theorem entryCheck19_2 : entry19_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_2 k)) := by decide +kernel

theorem rowsSound19_2 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval10409 x
  · exact rowEval10410 x
  · exact rowEval10411 x
  · exact rowEval10412 x
  · exact rowEval10413 x
  · exact rowEval10414 x
  · exact rowEval10415 x
  · exact rowEval10416 x
  · exact rowEval10417 x
  · exact rowEval10418 x

theorem entryEval19_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_2 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck19_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_2]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block3.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form2.terms k).tag (GramFunctions.Block3.form2.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7382 x
  · exact rowEval7383 x
  · exact rowEval7384 x
  · exact rowEval7385 x
  · exact rowEval7386 x
  · exact rowEval7387 x
  · exact rowEval7388 x
  · exact rowEval7389 x
  · exact rowEval7390 x
  · exact rowEval7391 x
  · exact rowEval7392 x
  · exact rowEval7393 x
  · exact rowEval7394 x
  · exact rowEval7395 x
  · exact rowEval7396 x
  · exact rowEval7397 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block3.form2.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form2 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block3.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form2.terms k).tag (GramFunctions.Block3.form2.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7398 x
  · exact rowEval7399 x
  · exact rowEval7400 x
  · exact rowEval7401 x
  · exact rowEval7402 x
  · exact rowEval7403 x
  · exact rowEval7404 x
  · exact rowEval7405 x
  · exact rowEval7406 x
  · exact rowEval7407 x
  · exact rowEval7408 x
  · exact rowEval7409 x
  · exact rowEval7410 x
  · exact rowEval7411 x
  · exact rowEval7412 x
  · exact rowEval7413 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block3.form2.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form2 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block3.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form2.terms k).tag (GramFunctions.Block3.form2.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7414 x
  · exact rowEval7415 x
  · exact rowEval7416 x
  · exact rowEval7417 x
  · exact rowEval7418 x
  · exact rowEval7419 x
  · exact rowEval7420 x
  · exact rowEval7421 x
  · exact rowEval7422 x
  · exact rowEval7423 x
  · exact rowEval7424 x
  · exact rowEval7425 x
  · exact rowEval7426 x
  · exact rowEval7427 x
  · exact rowEval7428 x
  · exact rowEval7429 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block3.form2.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form2 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

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

theorem entryCheck20_2 : entry20_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_2 k)) := by decide +kernel

theorem rowsSound20_2 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval10599 x
  · exact rowEval10600 x
  · exact rowEval10601 x
  · exact rowEval10602 x
  · exact rowEval10603 x

theorem entryEval20_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_2 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck20_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_2]

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

theorem rawRowCheck11810 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form2 = rawRow11810 := by decide +kernel

theorem rowCheck11810 : row11810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11810 := by decide +kernel

theorem rowEval11810 (x : Key → ℝ) : Integer.Sparse.eval row11810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11810, Integer.Sparse.eval_collectBalanced, rawRowCheck11810]

theorem rawRowCheck11811 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form2 = rawRow11811 := by decide +kernel

theorem rowCheck11811 : row11811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11811 := by decide +kernel

theorem rowEval11811 (x : Key → ℝ) : Integer.Sparse.eval row11811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11811, Integer.Sparse.eval_collectBalanced, rawRowCheck11811]

theorem rawRowCheck11812 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form2 = rawRow11812 := by decide +kernel

theorem rowCheck11812 : row11812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11812 := by decide +kernel

theorem rowEval11812 (x : Key → ℝ) : Integer.Sparse.eval row11812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11812, Integer.Sparse.eval_collectBalanced, rawRowCheck11812]

theorem rawRowCheck11813 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form2 = rawRow11813 := by decide +kernel

theorem rowCheck11813 : row11813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11813 := by decide +kernel

theorem rowEval11813 (x : Key → ℝ) : Integer.Sparse.eval row11813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11813, Integer.Sparse.eval_collectBalanced, rawRowCheck11813]

theorem rawRowCheck11814 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form2 = rawRow11814 := by decide +kernel

theorem rowCheck11814 : row11814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11814 := by decide +kernel

theorem rowEval11814 (x : Key → ℝ) : Integer.Sparse.eval row11814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11814, Integer.Sparse.eval_collectBalanced, rawRowCheck11814]

theorem rawRowCheck11815 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form2 = rawRow11815 := by decide +kernel

theorem rowCheck11815 : row11815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11815 := by decide +kernel

theorem rowEval11815 (x : Key → ℝ) : Integer.Sparse.eval row11815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11815, Integer.Sparse.eval_collectBalanced, rawRowCheck11815]

theorem rawRowCheck11816 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2 = rawRow11816 := by decide +kernel

theorem rowCheck11816 : row11816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11816 := by decide +kernel

theorem rowEval11816 (x : Key → ℝ) : Integer.Sparse.eval row11816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11816, Integer.Sparse.eval_collectBalanced, rawRowCheck11816]

theorem rawRowCheck11817 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2 = rawRow11817 := by decide +kernel

theorem rowCheck11817 : row11817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11817 := by decide +kernel

theorem rowEval11817 (x : Key → ℝ) : Integer.Sparse.eval row11817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11817, Integer.Sparse.eval_collectBalanced, rawRowCheck11817]

theorem rawRowCheck11818 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2 = rawRow11818 := by decide +kernel

theorem rowCheck11818 : row11818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11818 := by decide +kernel

theorem rowEval11818 (x : Key → ℝ) : Integer.Sparse.eval row11818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11818, Integer.Sparse.eval_collectBalanced, rawRowCheck11818]

theorem rawRowCheck11819 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2 = rawRow11819 := by decide +kernel

theorem rowCheck11819 : row11819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11819 := by decide +kernel

theorem rowEval11819 (x : Key → ℝ) : Integer.Sparse.eval row11819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11819, Integer.Sparse.eval_collectBalanced, rawRowCheck11819]

theorem rawRowCheck11820 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2 = rawRow11820 := by decide +kernel

theorem rowCheck11820 : row11820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11820 := by decide +kernel

theorem rowEval11820 (x : Key → ℝ) : Integer.Sparse.eval row11820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11820, Integer.Sparse.eval_collectBalanced, rawRowCheck11820]

theorem rawRowCheck11821 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2 = rawRow11821 := by decide +kernel

theorem rowCheck11821 : row11821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11821 := by decide +kernel

theorem rowEval11821 (x : Key → ℝ) : Integer.Sparse.eval row11821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11821, Integer.Sparse.eval_collectBalanced, rawRowCheck11821]

theorem rawRowCheck11822 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2 = rawRow11822 := by decide +kernel

theorem rowCheck11822 : row11822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11822 := by decide +kernel

theorem rowEval11822 (x : Key → ℝ) : Integer.Sparse.eval row11822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11822, Integer.Sparse.eval_collectBalanced, rawRowCheck11822]

theorem rawRowCheck11823 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2 = rawRow11823 := by decide +kernel

theorem rowCheck11823 : row11823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11823 := by decide +kernel

theorem rowEval11823 (x : Key → ℝ) : Integer.Sparse.eval row11823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11823, Integer.Sparse.eval_collectBalanced, rawRowCheck11823]

theorem rawRowCheck11824 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2 = rawRow11824 := by decide +kernel

theorem rowCheck11824 : row11824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11824 := by decide +kernel

theorem rowEval11824 (x : Key → ℝ) : Integer.Sparse.eval row11824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck11824, Integer.Sparse.eval_collectBalanced, rawRowCheck11824]

theorem rawRowCheck11825 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2 = rawRow11825 := by decide +kernel

theorem rowCheck11825 : row11825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11825 := by decide +kernel

theorem rowEval11825 (x : Key → ℝ) : Integer.Sparse.eval row11825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11825, Integer.Sparse.eval_collectBalanced, rawRowCheck11825]

theorem rawRowCheck11826 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2 = rawRow11826 := by decide +kernel

theorem rowCheck11826 : row11826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11826 := by decide +kernel

theorem rowEval11826 (x : Key → ℝ) : Integer.Sparse.eval row11826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11826, Integer.Sparse.eval_collectBalanced, rawRowCheck11826]

theorem rawRowCheck11827 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2 = rawRow11827 := by decide +kernel

theorem rowCheck11827 : row11827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11827 := by decide +kernel

theorem rowEval11827 (x : Key → ℝ) : Integer.Sparse.eval row11827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck11827, Integer.Sparse.eval_collectBalanced, rawRowCheck11827]

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

theorem rawRowCheck12216 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow12216 := by decide +kernel

theorem rowCheck12216 : row12216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12216 := by decide +kernel

theorem rowEval12216 (x : Key → ℝ) : Integer.Sparse.eval row12216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12216, Integer.Sparse.eval_collectBalanced, rawRowCheck12216]

theorem rawRowCheck12217 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow12217 := by decide +kernel

theorem rowCheck12217 : row12217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12217 := by decide +kernel

theorem rowEval12217 (x : Key → ℝ) : Integer.Sparse.eval row12217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12217, Integer.Sparse.eval_collectBalanced, rawRowCheck12217]

theorem rawRowCheck12218 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form2 = rawRow12218 := by decide +kernel

theorem rowCheck12218 : row12218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12218 := by decide +kernel

theorem rowEval12218 (x : Key → ℝ) : Integer.Sparse.eval row12218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12218, Integer.Sparse.eval_collectBalanced, rawRowCheck12218]

theorem rawRowCheck12219 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form2 = rawRow12219 := by decide +kernel

theorem rowCheck12219 : row12219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12219 := by decide +kernel

theorem rowEval12219 (x : Key → ℝ) : Integer.Sparse.eval row12219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12219, Integer.Sparse.eval_collectBalanced, rawRowCheck12219]

theorem rawRowCheck12220 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form2 = rawRow12220 := by decide +kernel

theorem rowCheck12220 : row12220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12220 := by decide +kernel

theorem rowEval12220 (x : Key → ℝ) : Integer.Sparse.eval row12220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12220, Integer.Sparse.eval_collectBalanced, rawRowCheck12220]

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

theorem entryCheck23_2 : entry23_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_2 k)) := by decide +kernel

theorem rowsSound23_2 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval11810 x
  · exact rowEval11811 x
  · exact rowEval11812 x
  · exact rowEval11813 x
  · exact rowEval11814 x
  · exact rowEval11815 x
  · exact rowEval11816 x
  · exact rowEval11817 x
  · exact rowEval11818 x
  · exact rowEval11819 x
  · exact rowEval11820 x
  · exact rowEval11821 x
  · exact rowEval11822 x
  · exact rowEval11823 x
  · exact rowEval11824 x
  · exact rowEval11825 x
  · exact rowEval11826 x
  · exact rowEval11827 x

theorem entryEval23_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_2 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck23_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_2]

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

theorem rawRowCheck12347 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form2 = rawRow12347 := by decide +kernel

theorem rowCheck12347 : row12347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12347 := by decide +kernel

theorem rowEval12347 (x : Key → ℝ) : Integer.Sparse.eval row12347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12347, Integer.Sparse.eval_collectBalanced, rawRowCheck12347]

theorem rawRowCheck12348 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form2 = rawRow12348 := by decide +kernel

theorem rowCheck12348 : row12348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12348 := by decide +kernel

theorem rowEval12348 (x : Key → ℝ) : Integer.Sparse.eval row12348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12348, Integer.Sparse.eval_collectBalanced, rawRowCheck12348]

theorem rawRowCheck12349 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form2 = rawRow12349 := by decide +kernel

theorem rowCheck12349 : row12349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12349 := by decide +kernel

theorem rowEval12349 (x : Key → ℝ) : Integer.Sparse.eval row12349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12349, Integer.Sparse.eval_collectBalanced, rawRowCheck12349]

theorem rawRowCheck12350 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form2 = rawRow12350 := by decide +kernel

theorem rowCheck12350 : row12350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12350 := by decide +kernel

theorem rowEval12350 (x : Key → ℝ) : Integer.Sparse.eval row12350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12350, Integer.Sparse.eval_collectBalanced, rawRowCheck12350]

theorem rawRowCheck12351 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form2 = rawRow12351 := by decide +kernel

theorem rowCheck12351 : row12351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12351 := by decide +kernel

theorem rowEval12351 (x : Key → ℝ) : Integer.Sparse.eval row12351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12351, Integer.Sparse.eval_collectBalanced, rawRowCheck12351]

theorem rawRowCheck12352 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form2 = rawRow12352 := by decide +kernel

theorem rowCheck12352 : row12352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12352 := by decide +kernel

theorem rowEval12352 (x : Key → ℝ) : Integer.Sparse.eval row12352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12352, Integer.Sparse.eval_collectBalanced, rawRowCheck12352]

theorem rawRowCheck12353 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form2 = rawRow12353 := by decide +kernel

theorem rowCheck12353 : row12353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12353 := by decide +kernel

theorem rowEval12353 (x : Key → ℝ) : Integer.Sparse.eval row12353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12353, Integer.Sparse.eval_collectBalanced, rawRowCheck12353]

theorem rawRowCheck12354 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form2 = rawRow12354 := by decide +kernel

theorem rowCheck12354 : row12354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12354 := by decide +kernel

theorem rowEval12354 (x : Key → ℝ) : Integer.Sparse.eval row12354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12354, Integer.Sparse.eval_collectBalanced, rawRowCheck12354]

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

theorem entryCheck24_2 : entry24_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_2 k)) := by decide +kernel

theorem rowsSound24_2 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12216 x
  · exact rowEval12217 x
  · exact rowEval12218 x
  · exact rowEval12219 x
  · exact rowEval12220 x

theorem entryEval24_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_2 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck24_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_2]

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

theorem entryCheck25_2 : entry25_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_2 k)) := by decide +kernel

theorem rowsSound25_2 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12347 x
  · exact rowEval12348 x
  · exact rowEval12349 x
  · exact rowEval12350 x
  · exact rowEval12351 x
  · exact rowEval12352 x
  · exact rowEval12353 x
  · exact rowEval12354 x

theorem entryEval25_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_2 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck25_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_2]

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

theorem rawRowCheck12587 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form2 = rawRow12587 := by decide +kernel

theorem rowCheck12587 : row12587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12587 := by decide +kernel

theorem rowEval12587 (x : Key → ℝ) : Integer.Sparse.eval row12587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12587, Integer.Sparse.eval_collectBalanced, rawRowCheck12587]

theorem rawRowCheck12588 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form2 = rawRow12588 := by decide +kernel

theorem rowCheck12588 : row12588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12588 := by decide +kernel

theorem rowEval12588 (x : Key → ℝ) : Integer.Sparse.eval row12588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12588, Integer.Sparse.eval_collectBalanced, rawRowCheck12588]

theorem rawRowCheck12589 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form2 = rawRow12589 := by decide +kernel

theorem rowCheck12589 : row12589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12589 := by decide +kernel

theorem rowEval12589 (x : Key → ℝ) : Integer.Sparse.eval row12589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12589, Integer.Sparse.eval_collectBalanced, rawRowCheck12589]

theorem rawRowCheck12590 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form2 = rawRow12590 := by decide +kernel

theorem rowCheck12590 : row12590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12590 := by decide +kernel

theorem rowEval12590 (x : Key → ℝ) : Integer.Sparse.eval row12590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12590, Integer.Sparse.eval_collectBalanced, rawRowCheck12590]

theorem rawRowCheck12591 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form2 = rawRow12591 := by decide +kernel

theorem rowCheck12591 : row12591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12591 := by decide +kernel

theorem rowEval12591 (x : Key → ℝ) : Integer.Sparse.eval row12591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12591, Integer.Sparse.eval_collectBalanced, rawRowCheck12591]

theorem rawRowCheck12592 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form2 = rawRow12592 := by decide +kernel

theorem rowCheck12592 : row12592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12592 := by decide +kernel

theorem rowEval12592 (x : Key → ℝ) : Integer.Sparse.eval row12592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12592, Integer.Sparse.eval_collectBalanced, rawRowCheck12592]

theorem rawRowCheck12593 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form2 = rawRow12593 := by decide +kernel

theorem rowCheck12593 : row12593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12593 := by decide +kernel

theorem rowEval12593 (x : Key → ℝ) : Integer.Sparse.eval row12593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12593, Integer.Sparse.eval_collectBalanced, rawRowCheck12593]

theorem rawRowCheck12594 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form2 = rawRow12594 := by decide +kernel

theorem rowCheck12594 : row12594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12594 := by decide +kernel

theorem rowEval12594 (x : Key → ℝ) : Integer.Sparse.eval row12594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12594, Integer.Sparse.eval_collectBalanced, rawRowCheck12594]

theorem rawRowCheck12595 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form2 = rawRow12595 := by decide +kernel

theorem rowCheck12595 : row12595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12595 := by decide +kernel

theorem rowEval12595 (x : Key → ℝ) : Integer.Sparse.eval row12595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12595, Integer.Sparse.eval_collectBalanced, rawRowCheck12595]

theorem rawRowCheck12596 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form2 = rawRow12596 := by decide +kernel

theorem rowCheck12596 : row12596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12596 := by decide +kernel

theorem rowEval12596 (x : Key → ℝ) : Integer.Sparse.eval row12596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12596, Integer.Sparse.eval_collectBalanced, rawRowCheck12596]

theorem rawRowCheck12597 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form2 = rawRow12597 := by decide +kernel

theorem rowCheck12597 : row12597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12597 := by decide +kernel

theorem rowEval12597 (x : Key → ℝ) : Integer.Sparse.eval row12597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12597, Integer.Sparse.eval_collectBalanced, rawRowCheck12597]

theorem rawRowCheck12598 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form2 = rawRow12598 := by decide +kernel

theorem rowCheck12598 : row12598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12598 := by decide +kernel

theorem rowEval12598 (x : Key → ℝ) : Integer.Sparse.eval row12598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12598, Integer.Sparse.eval_collectBalanced, rawRowCheck12598]

theorem rawRowCheck12599 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form2 = rawRow12599 := by decide +kernel

theorem rowCheck12599 : row12599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12599 := by decide +kernel

theorem rowEval12599 (x : Key → ℝ) : Integer.Sparse.eval row12599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12599, Integer.Sparse.eval_collectBalanced, rawRowCheck12599]

theorem rawRowCheck12600 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form2 = rawRow12600 := by decide +kernel

theorem rowCheck12600 : row12600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12600 := by decide +kernel

theorem rowEval12600 (x : Key → ℝ) : Integer.Sparse.eval row12600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12600, Integer.Sparse.eval_collectBalanced, rawRowCheck12600]

theorem rawRowCheck12601 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form2 = rawRow12601 := by decide +kernel

theorem rowCheck12601 : row12601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12601 := by decide +kernel

theorem rowEval12601 (x : Key → ℝ) : Integer.Sparse.eval row12601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12601, Integer.Sparse.eval_collectBalanced, rawRowCheck12601]

theorem rawRowCheck12602 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form2 = rawRow12602 := by decide +kernel

theorem rowCheck12602 : row12602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12602 := by decide +kernel

theorem rowEval12602 (x : Key → ℝ) : Integer.Sparse.eval row12602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12602, Integer.Sparse.eval_collectBalanced, rawRowCheck12602]

theorem rawRowCheck12603 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form2 = rawRow12603 := by decide +kernel

theorem rowCheck12603 : row12603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12603 := by decide +kernel

theorem rowEval12603 (x : Key → ℝ) : Integer.Sparse.eval row12603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12603, Integer.Sparse.eval_collectBalanced, rawRowCheck12603]

theorem rawRowCheck12604 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form2 = rawRow12604 := by decide +kernel

theorem rowCheck12604 : row12604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12604 := by decide +kernel

theorem rowEval12604 (x : Key → ℝ) : Integer.Sparse.eval row12604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12604, Integer.Sparse.eval_collectBalanced, rawRowCheck12604]

theorem rawRowCheck12605 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form2 = rawRow12605 := by decide +kernel

theorem rowCheck12605 : row12605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12605 := by decide +kernel

theorem rowEval12605 (x : Key → ℝ) : Integer.Sparse.eval row12605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12605, Integer.Sparse.eval_collectBalanced, rawRowCheck12605]

theorem rawRowCheck12606 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form2 = rawRow12606 := by decide +kernel

theorem rowCheck12606 : row12606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12606 := by decide +kernel

theorem rowEval12606 (x : Key → ℝ) : Integer.Sparse.eval row12606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12606, Integer.Sparse.eval_collectBalanced, rawRowCheck12606]

theorem rawRowCheck12607 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form2 = rawRow12607 := by decide +kernel

theorem rowCheck12607 : row12607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12607 := by decide +kernel

theorem rowEval12607 (x : Key → ℝ) : Integer.Sparse.eval row12607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12607, Integer.Sparse.eval_collectBalanced, rawRowCheck12607]

theorem rawRowCheck12608 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow12608 := by decide +kernel

theorem rowCheck12608 : row12608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12608 := by decide +kernel

theorem rowEval12608 (x : Key → ℝ) : Integer.Sparse.eval row12608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12608, Integer.Sparse.eval_collectBalanced, rawRowCheck12608]

theorem rawRowCheck12609 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow12609 := by decide +kernel

theorem rowCheck12609 : row12609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12609 := by decide +kernel

theorem rowEval12609 (x : Key → ℝ) : Integer.Sparse.eval row12609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12609, Integer.Sparse.eval_collectBalanced, rawRowCheck12609]

theorem rawRowCheck12610 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow12610 := by decide +kernel

theorem rowCheck12610 : row12610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12610 := by decide +kernel

theorem rowEval12610 (x : Key → ℝ) : Integer.Sparse.eval row12610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12610, Integer.Sparse.eval_collectBalanced, rawRowCheck12610]

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

theorem entryCheck26_2 : entry26_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_2 k)) := by decide +kernel

theorem rowsSound26_2 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12587 x
  · exact rowEval12588 x
  · exact rowEval12589 x
  · exact rowEval12590 x
  · exact rowEval12591 x
  · exact rowEval12592 x
  · exact rowEval12593 x
  · exact rowEval12594 x
  · exact rowEval12595 x
  · exact rowEval12596 x
  · exact rowEval12597 x
  · exact rowEval12598 x
  · exact rowEval12599 x
  · exact rowEval12600 x
  · exact rowEval12601 x
  · exact rowEval12602 x
  · exact rowEval12603 x
  · exact rowEval12604 x
  · exact rowEval12605 x
  · exact rowEval12606 x
  · exact rowEval12607 x
  · exact rowEval12608 x
  · exact rowEval12609 x
  · exact rowEval12610 x

theorem entryEval26_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_2 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck26_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_2]

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

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7526 x
  · exact rowEval7527 x
  · exact rowEval7528 x
  · exact rowEval7529 x
  · exact rowEval7530 x
  · exact rowEval7531 x
  · exact rowEval7532 x
  · exact rowEval7533 x
  · exact rowEval7534 x
  · exact rowEval7535 x
  · exact rowEval7536 x
  · exact rowEval7537 x
  · exact rowEval7538 x
  · exact rowEval7539 x
  · exact rowEval7540 x
  · exact rowEval7541 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

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

theorem rawRowCheck7800 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7800 := by decide +kernel

theorem rowCheck7800 : row7800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7800 := by decide +kernel

theorem rowEval7800 (x : Key → ℝ) : Integer.Sparse.eval row7800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7800, Integer.Sparse.eval_collectBalanced, rawRowCheck7800]

theorem rawRowCheck7801 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7801 := by decide +kernel

theorem rowCheck7801 : row7801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7801 := by decide +kernel

theorem rowEval7801 (x : Key → ℝ) : Integer.Sparse.eval row7801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7801, Integer.Sparse.eval_collectBalanced, rawRowCheck7801]

theorem rawRowCheck7802 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow7802 := by decide +kernel

theorem rowCheck7802 : row7802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7802 := by decide +kernel

theorem rowEval7802 (x : Key → ℝ) : Integer.Sparse.eval row7802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7802, Integer.Sparse.eval_collectBalanced, rawRowCheck7802]

theorem rawRowCheck7803 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow7803 := by decide +kernel

theorem rowCheck7803 : row7803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7803 := by decide +kernel

theorem rowEval7803 (x : Key → ℝ) : Integer.Sparse.eval row7803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7803, Integer.Sparse.eval_collectBalanced, rawRowCheck7803]

theorem rawRowCheck7804 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow7804 := by decide +kernel

theorem rowCheck7804 : row7804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7804 := by decide +kernel

theorem rowEval7804 (x : Key → ℝ) : Integer.Sparse.eval row7804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7804, Integer.Sparse.eval_collectBalanced, rawRowCheck7804]

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

theorem rawRowCheck7849 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7849 := by decide +kernel

theorem rowCheck7849 : row7849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7849 := by decide +kernel

theorem rowEval7849 (x : Key → ℝ) : Integer.Sparse.eval row7849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7849, Integer.Sparse.eval_collectBalanced, rawRowCheck7849]

theorem rawRowCheck7850 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7850 := by decide +kernel

theorem rowCheck7850 : row7850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7850 := by decide +kernel

theorem rowEval7850 (x : Key → ℝ) : Integer.Sparse.eval row7850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7850, Integer.Sparse.eval_collectBalanced, rawRowCheck7850]

theorem rawRowCheck7851 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7851 := by decide +kernel

theorem rowCheck7851 : row7851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7851 := by decide +kernel

theorem rowEval7851 (x : Key → ℝ) : Integer.Sparse.eval row7851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7851, Integer.Sparse.eval_collectBalanced, rawRowCheck7851]

theorem rawRowCheck7852 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form2 = rawRow7852 := by decide +kernel

theorem rowCheck7852 : row7852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7852 := by decide +kernel

theorem rowEval7852 (x : Key → ℝ) : Integer.Sparse.eval row7852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7852, Integer.Sparse.eval_collectBalanced, rawRowCheck7852]

theorem rawRowCheck7853 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form2 = rawRow7853 := by decide +kernel

theorem rowCheck7853 : row7853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7853 := by decide +kernel

theorem rowEval7853 (x : Key → ℝ) : Integer.Sparse.eval row7853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7853, Integer.Sparse.eval_collectBalanced, rawRowCheck7853]

theorem rawRowCheck7854 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form2 = rawRow7854 := by decide +kernel

theorem rowCheck7854 : row7854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7854 := by decide +kernel

theorem rowEval7854 (x : Key → ℝ) : Integer.Sparse.eval row7854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7854, Integer.Sparse.eval_collectBalanced, rawRowCheck7854]

theorem rawRowCheck7855 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form2 = rawRow7855 := by decide +kernel

theorem rowCheck7855 : row7855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7855 := by decide +kernel

theorem rowEval7855 (x : Key → ℝ) : Integer.Sparse.eval row7855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7855, Integer.Sparse.eval_collectBalanced, rawRowCheck7855]

theorem rawRowCheck7856 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form2 = rawRow7856 := by decide +kernel

theorem rowCheck7856 : row7856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7856 := by decide +kernel

theorem rowEval7856 (x : Key → ℝ) : Integer.Sparse.eval row7856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7856, Integer.Sparse.eval_collectBalanced, rawRowCheck7856]

theorem rawRowCheck7857 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form2 = rawRow7857 := by decide +kernel

theorem rowCheck7857 : row7857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7857 := by decide +kernel

theorem rowEval7857 (x : Key → ℝ) : Integer.Sparse.eval row7857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7857, Integer.Sparse.eval_collectBalanced, rawRowCheck7857]

theorem rawRowCheck7858 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow7858 := by decide +kernel

theorem rowCheck7858 : row7858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7858 := by decide +kernel

theorem rowEval7858 (x : Key → ℝ) : Integer.Sparse.eval row7858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7858, Integer.Sparse.eval_collectBalanced, rawRowCheck7858]

theorem rawRowCheck7859 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow7859 := by decide +kernel

theorem rowCheck7859 : row7859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7859 := by decide +kernel

theorem rowEval7859 (x : Key → ℝ) : Integer.Sparse.eval row7859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7859, Integer.Sparse.eval_collectBalanced, rawRowCheck7859]

theorem rawRowCheck7860 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow7860 := by decide +kernel

theorem rowCheck7860 : row7860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7860 := by decide +kernel

theorem rowEval7860 (x : Key → ℝ) : Integer.Sparse.eval row7860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7860, Integer.Sparse.eval_collectBalanced, rawRowCheck7860]

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

theorem entryCheck6_2 : entry6_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_2 k)) := by decide +kernel

theorem rowsSound6_2 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7800 x
  · exact rowEval7801 x
  · exact rowEval7802 x
  · exact rowEval7803 x
  · exact rowEval7804 x

theorem entryEval6_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_2 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck6_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_2]

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

theorem entryCheck7_2 : entry7_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_2 k)) := by decide +kernel

theorem rowsSound7_2 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7849 x
  · exact rowEval7850 x
  · exact rowEval7851 x
  · exact rowEval7852 x
  · exact rowEval7853 x
  · exact rowEval7854 x
  · exact rowEval7855 x
  · exact rowEval7856 x
  · exact rowEval7857 x
  · exact rowEval7858 x
  · exact rowEval7859 x
  · exact rowEval7860 x
  · exact rowEval7646 x
  · exact rowEval7647 x
  · exact rowEval7648 x
  · exact rowEval7649 x
  · exact rowEval7650 x
  · exact rowEval7651 x
  · exact rowEval7652 x
  · exact rowEval7653 x
  · exact rowEval7654 x
  · exact rowEval7655 x
  · exact rowEval7656 x
  · exact rowEval7657 x

theorem entryEval7_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_2 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck7_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_2]

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

theorem entryEvalRow2_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 2 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 2).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval2_0 B hB
  · exact entryEval2_1 B hB
  · exact entryEval2_2 B hB
  · exact (entryEval3_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e_oai
