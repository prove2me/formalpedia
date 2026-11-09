-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:12:15.838404+00:00
-- url     : https://prove2.me/submissions/a4e8e32c-bfe9-445c-a29e-65d9637d35e9

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
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E053
import Definitions.Def_OAIQ106E054
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E057
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval9_1_e

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

theorem rawRowCheck7372 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7372 := by decide +kernel

theorem rowCheck7372 : row7372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7372 := by decide +kernel

theorem rowEval7372 (x : Key → ℝ) : Integer.Sparse.eval row7372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7372, Integer.Sparse.eval_collectBalanced, rawRowCheck7372]

theorem rawRowCheck7373 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7373 := by decide +kernel

theorem rowCheck7373 : row7373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7373 := by decide +kernel

theorem rowEval7373 (x : Key → ℝ) : Integer.Sparse.eval row7373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7373, Integer.Sparse.eval_collectBalanced, rawRowCheck7373]

theorem rawRowCheck7374 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7374 := by decide +kernel

theorem rowCheck7374 : row7374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7374 := by decide +kernel

theorem rowEval7374 (x : Key → ℝ) : Integer.Sparse.eval row7374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7374, Integer.Sparse.eval_collectBalanced, rawRowCheck7374]

theorem rawRowCheck7375 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7375 := by decide +kernel

theorem rowCheck7375 : row7375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7375 := by decide +kernel

theorem rowEval7375 (x : Key → ℝ) : Integer.Sparse.eval row7375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7375, Integer.Sparse.eval_collectBalanced, rawRowCheck7375]

theorem rawRowCheck7376 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7376 := by decide +kernel

theorem rowCheck7376 : row7376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7376 := by decide +kernel

theorem rowEval7376 (x : Key → ℝ) : Integer.Sparse.eval row7376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7376, Integer.Sparse.eval_collectBalanced, rawRowCheck7376]

theorem rawRowCheck7377 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7377 := by decide +kernel

theorem rowCheck7377 : row7377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7377 := by decide +kernel

theorem rowEval7377 (x : Key → ℝ) : Integer.Sparse.eval row7377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7377, Integer.Sparse.eval_collectBalanced, rawRowCheck7377]

theorem rawRowCheck7378 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7378 := by decide +kernel

theorem rowCheck7378 : row7378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7378 := by decide +kernel

theorem rowEval7378 (x : Key → ℝ) : Integer.Sparse.eval row7378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7378, Integer.Sparse.eval_collectBalanced, rawRowCheck7378]

theorem rawRowCheck7379 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7379 := by decide +kernel

theorem rowCheck7379 : row7379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7379 := by decide +kernel

theorem rowEval7379 (x : Key → ℝ) : Integer.Sparse.eval row7379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7379, Integer.Sparse.eval_collectBalanced, rawRowCheck7379]

theorem rawRowCheck7380 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7380 := by decide +kernel

theorem rowCheck7380 : row7380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7380 := by decide +kernel

theorem rowEval7380 (x : Key → ℝ) : Integer.Sparse.eval row7380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7380, Integer.Sparse.eval_collectBalanced, rawRowCheck7380]

theorem rawRowCheck7381 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7381 := by decide +kernel

theorem rowCheck7381 : row7381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7381 := by decide +kernel

theorem rowEval7381 (x : Key → ℝ) : Integer.Sparse.eval row7381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7381, Integer.Sparse.eval_collectBalanced, rawRowCheck7381]

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

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block3.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form1.terms k).tag (GramFunctions.Block3.form1.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7372 x
  · exact rowEval7373 x
  · exact rowEval7374 x
  · exact rowEval7375 x
  · exact rowEval7376 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block3.form1.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form1 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block3.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form1.terms k).tag (GramFunctions.Block3.form1.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7377 x
  · exact rowEval7378 x
  · exact rowEval7379 x
  · exact rowEval7380 x
  · exact rowEval7381 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block3.form1.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form1 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck8669 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form1 = rawRow8669 := by decide +kernel

theorem rowCheck8669 : row8669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8669 := by decide +kernel

theorem rowEval8669 (x : Key → ℝ) : Integer.Sparse.eval row8669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8669, Integer.Sparse.eval_collectBalanced, rawRowCheck8669]

theorem rawRowCheck8670 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form1 = rawRow8670 := by decide +kernel

theorem rowCheck8670 : row8670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8670 := by decide +kernel

theorem rowEval8670 (x : Key → ℝ) : Integer.Sparse.eval row8670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8670, Integer.Sparse.eval_collectBalanced, rawRowCheck8670]

theorem rawRowCheck8671 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form1 = rawRow8671 := by decide +kernel

theorem rowCheck8671 : row8671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8671 := by decide +kernel

theorem rowEval8671 (x : Key → ℝ) : Integer.Sparse.eval row8671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8671, Integer.Sparse.eval_collectBalanced, rawRowCheck8671]

theorem rawRowCheck8672 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8672 := by decide +kernel

theorem rowCheck8672 : row8672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8672 := by decide +kernel

theorem rowEval8672 (x : Key → ℝ) : Integer.Sparse.eval row8672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8672, Integer.Sparse.eval_collectBalanced, rawRowCheck8672]

theorem rawRowCheck8673 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8673 := by decide +kernel

theorem rowCheck8673 : row8673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8673 := by decide +kernel

theorem rowEval8673 (x : Key → ℝ) : Integer.Sparse.eval row8673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8673, Integer.Sparse.eval_collectBalanced, rawRowCheck8673]

theorem rawRowCheck8674 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow8674 := by decide +kernel

theorem rowCheck8674 : row8674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8674 := by decide +kernel

theorem rowEval8674 (x : Key → ℝ) : Integer.Sparse.eval row8674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8674, Integer.Sparse.eval_collectBalanced, rawRowCheck8674]

theorem rawRowCheck8675 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow8675 := by decide +kernel

theorem rowCheck8675 : row8675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8675 := by decide +kernel

theorem rowEval8675 (x : Key → ℝ) : Integer.Sparse.eval row8675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8675, Integer.Sparse.eval_collectBalanced, rawRowCheck8675]

theorem rawRowCheck8676 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow8676 := by decide +kernel

theorem rowCheck8676 : row8676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8676 := by decide +kernel

theorem rowEval8676 (x : Key → ℝ) : Integer.Sparse.eval row8676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck8676, Integer.Sparse.eval_collectBalanced, rawRowCheck8676]

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

theorem rawRowCheck8761 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8761 := by decide +kernel

theorem rowCheck8761 : row8761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8761 := by decide +kernel

theorem rowEval8761 (x : Key → ℝ) : Integer.Sparse.eval row8761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8761, Integer.Sparse.eval_collectBalanced, rawRowCheck8761]

theorem rawRowCheck8762 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow8762 := by decide +kernel

theorem rowCheck8762 : row8762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8762 := by decide +kernel

theorem rowEval8762 (x : Key → ℝ) : Integer.Sparse.eval row8762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8762, Integer.Sparse.eval_collectBalanced, rawRowCheck8762]

theorem rawRowCheck8763 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow8763 := by decide +kernel

theorem rowCheck8763 : row8763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8763 := by decide +kernel

theorem rowEval8763 (x : Key → ℝ) : Integer.Sparse.eval row8763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8763, Integer.Sparse.eval_collectBalanced, rawRowCheck8763]

theorem rawRowCheck8764 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow8764 := by decide +kernel

theorem rowCheck8764 : row8764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8764 := by decide +kernel

theorem rowEval8764 (x : Key → ℝ) : Integer.Sparse.eval row8764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck8764, Integer.Sparse.eval_collectBalanced, rawRowCheck8764]

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

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8669 x
  · exact rowEval8670 x
  · exact rowEval8671 x
  · exact rowEval8672 x
  · exact rowEval8673 x
  · exact rowEval8674 x
  · exact rowEval8675 x
  · exact rowEval8676 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

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

theorem rawRowCheck7510 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7510 := by decide +kernel

theorem rowCheck7510 : row7510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7510 := by decide +kernel

theorem rowEval7510 (x : Key → ℝ) : Integer.Sparse.eval row7510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7510, Integer.Sparse.eval_collectBalanced, rawRowCheck7510]

theorem rawRowCheck7511 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7511 := by decide +kernel

theorem rowCheck7511 : row7511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7511 := by decide +kernel

theorem rowEval7511 (x : Key → ℝ) : Integer.Sparse.eval row7511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7511, Integer.Sparse.eval_collectBalanced, rawRowCheck7511]

theorem rawRowCheck7512 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7512 := by decide +kernel

theorem rowCheck7512 : row7512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7512 := by decide +kernel

theorem rowEval7512 (x : Key → ℝ) : Integer.Sparse.eval row7512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7512, Integer.Sparse.eval_collectBalanced, rawRowCheck7512]

theorem rawRowCheck7513 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7513 := by decide +kernel

theorem rowCheck7513 : row7513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7513 := by decide +kernel

theorem rowEval7513 (x : Key → ℝ) : Integer.Sparse.eval row7513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7513, Integer.Sparse.eval_collectBalanced, rawRowCheck7513]

theorem rawRowCheck7514 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7514 := by decide +kernel

theorem rowCheck7514 : row7514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7514 := by decide +kernel

theorem rowEval7514 (x : Key → ℝ) : Integer.Sparse.eval row7514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7514, Integer.Sparse.eval_collectBalanced, rawRowCheck7514]

theorem rawRowCheck7515 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7515 := by decide +kernel

theorem rowCheck7515 : row7515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7515 := by decide +kernel

theorem rowEval7515 (x : Key → ℝ) : Integer.Sparse.eval row7515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7515, Integer.Sparse.eval_collectBalanced, rawRowCheck7515]

theorem rawRowCheck7516 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7516 := by decide +kernel

theorem rowCheck7516 : row7516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7516 := by decide +kernel

theorem rowEval7516 (x : Key → ℝ) : Integer.Sparse.eval row7516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7516, Integer.Sparse.eval_collectBalanced, rawRowCheck7516]

theorem rawRowCheck7517 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form1 = rawRow7517 := by decide +kernel

theorem rowCheck7517 : row7517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7517 := by decide +kernel

theorem rowEval7517 (x : Key → ℝ) : Integer.Sparse.eval row7517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7517, Integer.Sparse.eval_collectBalanced, rawRowCheck7517]

theorem rawRowCheck7518 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form1 = rawRow7518 := by decide +kernel

theorem rowCheck7518 : row7518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7518 := by decide +kernel

theorem rowEval7518 (x : Key → ℝ) : Integer.Sparse.eval row7518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7518, Integer.Sparse.eval_collectBalanced, rawRowCheck7518]

theorem rawRowCheck7519 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form1 = rawRow7519 := by decide +kernel

theorem rowCheck7519 : row7519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7519 := by decide +kernel

theorem rowEval7519 (x : Key → ℝ) : Integer.Sparse.eval row7519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7519, Integer.Sparse.eval_collectBalanced, rawRowCheck7519]

theorem rawRowCheck7520 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form1 = rawRow7520 := by decide +kernel

theorem rowCheck7520 : row7520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7520 := by decide +kernel

theorem rowEval7520 (x : Key → ℝ) : Integer.Sparse.eval row7520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7520, Integer.Sparse.eval_collectBalanced, rawRowCheck7520]

theorem rawRowCheck7521 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form1 = rawRow7521 := by decide +kernel

theorem rowCheck7521 : row7521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7521 := by decide +kernel

theorem rowEval7521 (x : Key → ℝ) : Integer.Sparse.eval row7521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7521, Integer.Sparse.eval_collectBalanced, rawRowCheck7521]

theorem rawRowCheck7522 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form1 = rawRow7522 := by decide +kernel

theorem rowCheck7522 : row7522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7522 := by decide +kernel

theorem rowEval7522 (x : Key → ℝ) : Integer.Sparse.eval row7522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7522, Integer.Sparse.eval_collectBalanced, rawRowCheck7522]

theorem rawRowCheck7523 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7523 := by decide +kernel

theorem rowCheck7523 : row7523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7523 := by decide +kernel

theorem rowEval7523 (x : Key → ℝ) : Integer.Sparse.eval row7523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7523, Integer.Sparse.eval_collectBalanced, rawRowCheck7523]

theorem rawRowCheck7524 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7524 := by decide +kernel

theorem rowCheck7524 : row7524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7524 := by decide +kernel

theorem rowEval7524 (x : Key → ℝ) : Integer.Sparse.eval row7524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7524, Integer.Sparse.eval_collectBalanced, rawRowCheck7524]

theorem rawRowCheck7525 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7525 := by decide +kernel

theorem rowCheck7525 : row7525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7525 := by decide +kernel

theorem rowEval7525 (x : Key → ℝ) : Integer.Sparse.eval row7525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7525, Integer.Sparse.eval_collectBalanced, rawRowCheck7525]

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

theorem rawRowCheck7610 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7610 := by decide +kernel

theorem rowCheck7610 : row7610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7610 := by decide +kernel

theorem rowEval7610 (x : Key → ℝ) : Integer.Sparse.eval row7610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7610, Integer.Sparse.eval_collectBalanced, rawRowCheck7610]

theorem rawRowCheck7611 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7611 := by decide +kernel

theorem rowCheck7611 : row7611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7611 := by decide +kernel

theorem rowEval7611 (x : Key → ℝ) : Integer.Sparse.eval row7611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7611, Integer.Sparse.eval_collectBalanced, rawRowCheck7611]

theorem rawRowCheck7612 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7612 := by decide +kernel

theorem rowCheck7612 : row7612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7612 := by decide +kernel

theorem rowEval7612 (x : Key → ℝ) : Integer.Sparse.eval row7612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7612, Integer.Sparse.eval_collectBalanced, rawRowCheck7612]

theorem rawRowCheck7613 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form1 = rawRow7613 := by decide +kernel

theorem rowCheck7613 : row7613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7613 := by decide +kernel

theorem rowEval7613 (x : Key → ℝ) : Integer.Sparse.eval row7613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7613, Integer.Sparse.eval_collectBalanced, rawRowCheck7613]

theorem rawRowCheck7614 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form1 = rawRow7614 := by decide +kernel

theorem rowCheck7614 : row7614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7614 := by decide +kernel

theorem rowEval7614 (x : Key → ℝ) : Integer.Sparse.eval row7614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7614, Integer.Sparse.eval_collectBalanced, rawRowCheck7614]

theorem rawRowCheck7615 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form1 = rawRow7615 := by decide +kernel

theorem rowCheck7615 : row7615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7615 := by decide +kernel

theorem rowEval7615 (x : Key → ℝ) : Integer.Sparse.eval row7615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7615, Integer.Sparse.eval_collectBalanced, rawRowCheck7615]

theorem rawRowCheck7616 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form1 = rawRow7616 := by decide +kernel

theorem rowCheck7616 : row7616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7616 := by decide +kernel

theorem rowEval7616 (x : Key → ℝ) : Integer.Sparse.eval row7616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7616, Integer.Sparse.eval_collectBalanced, rawRowCheck7616]

theorem rawRowCheck7617 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form1 = rawRow7617 := by decide +kernel

theorem rowCheck7617 : row7617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7617 := by decide +kernel

theorem rowEval7617 (x : Key → ℝ) : Integer.Sparse.eval row7617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7617, Integer.Sparse.eval_collectBalanced, rawRowCheck7617]

theorem rawRowCheck7618 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form1 = rawRow7618 := by decide +kernel

theorem rowCheck7618 : row7618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7618 := by decide +kernel

theorem rowEval7618 (x : Key → ℝ) : Integer.Sparse.eval row7618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7618, Integer.Sparse.eval_collectBalanced, rawRowCheck7618]

theorem rawRowCheck7619 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7619 := by decide +kernel

theorem rowCheck7619 : row7619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7619 := by decide +kernel

theorem rowEval7619 (x : Key → ℝ) : Integer.Sparse.eval row7619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7619, Integer.Sparse.eval_collectBalanced, rawRowCheck7619]

theorem rawRowCheck7620 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7620 := by decide +kernel

theorem rowCheck7620 : row7620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7620 := by decide +kernel

theorem rowEval7620 (x : Key → ℝ) : Integer.Sparse.eval row7620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7620, Integer.Sparse.eval_collectBalanced, rawRowCheck7620]

theorem rawRowCheck7621 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7621 := by decide +kernel

theorem rowCheck7621 : row7621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7621 := by decide +kernel

theorem rowEval7621 (x : Key → ℝ) : Integer.Sparse.eval row7621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7621, Integer.Sparse.eval_collectBalanced, rawRowCheck7621]

theorem rawRowCheck7622 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form1 = rawRow7622 := by decide +kernel

theorem rowCheck7622 : row7622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7622 := by decide +kernel

theorem rowEval7622 (x : Key → ℝ) : Integer.Sparse.eval row7622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7622, Integer.Sparse.eval_collectBalanced, rawRowCheck7622]

theorem rawRowCheck7623 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form1 = rawRow7623 := by decide +kernel

theorem rowCheck7623 : row7623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7623 := by decide +kernel

theorem rowEval7623 (x : Key → ℝ) : Integer.Sparse.eval row7623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7623, Integer.Sparse.eval_collectBalanced, rawRowCheck7623]

theorem rawRowCheck7624 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form1 = rawRow7624 := by decide +kernel

theorem rowCheck7624 : row7624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7624 := by decide +kernel

theorem rowEval7624 (x : Key → ℝ) : Integer.Sparse.eval row7624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7624, Integer.Sparse.eval_collectBalanced, rawRowCheck7624]

theorem rawRowCheck7625 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form1 = rawRow7625 := by decide +kernel

theorem rowCheck7625 : row7625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7625 := by decide +kernel

theorem rowEval7625 (x : Key → ℝ) : Integer.Sparse.eval row7625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7625, Integer.Sparse.eval_collectBalanced, rawRowCheck7625]

theorem rawRowCheck7626 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form1 = rawRow7626 := by decide +kernel

theorem rowCheck7626 : row7626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7626 := by decide +kernel

theorem rowEval7626 (x : Key → ℝ) : Integer.Sparse.eval row7626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7626, Integer.Sparse.eval_collectBalanced, rawRowCheck7626]

theorem rawRowCheck7627 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form1 = rawRow7627 := by decide +kernel

theorem rowCheck7627 : row7627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7627 := by decide +kernel

theorem rowEval7627 (x : Key → ℝ) : Integer.Sparse.eval row7627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7627, Integer.Sparse.eval_collectBalanced, rawRowCheck7627]

theorem rawRowCheck7628 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form1 = rawRow7628 := by decide +kernel

theorem rowCheck7628 : row7628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7628 := by decide +kernel

theorem rowEval7628 (x : Key → ℝ) : Integer.Sparse.eval row7628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7628, Integer.Sparse.eval_collectBalanced, rawRowCheck7628]

theorem rawRowCheck7629 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form1 = rawRow7629 := by decide +kernel

theorem rowCheck7629 : row7629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7629 := by decide +kernel

theorem rowEval7629 (x : Key → ℝ) : Integer.Sparse.eval row7629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7629, Integer.Sparse.eval_collectBalanced, rawRowCheck7629]

theorem rawRowCheck7630 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form1 = rawRow7630 := by decide +kernel

theorem rowCheck7630 : row7630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7630 := by decide +kernel

theorem rowEval7630 (x : Key → ℝ) : Integer.Sparse.eval row7630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7630, Integer.Sparse.eval_collectBalanced, rawRowCheck7630]

theorem rawRowCheck7631 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form1 = rawRow7631 := by decide +kernel

theorem rowCheck7631 : row7631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7631 := by decide +kernel

theorem rowEval7631 (x : Key → ℝ) : Integer.Sparse.eval row7631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7631, Integer.Sparse.eval_collectBalanced, rawRowCheck7631]

theorem rawRowCheck7632 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form1 = rawRow7632 := by decide +kernel

theorem rowCheck7632 : row7632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7632 := by decide +kernel

theorem rowEval7632 (x : Key → ℝ) : Integer.Sparse.eval row7632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7632, Integer.Sparse.eval_collectBalanced, rawRowCheck7632]

theorem rawRowCheck7633 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form1 = rawRow7633 := by decide +kernel

theorem rowCheck7633 : row7633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7633 := by decide +kernel

theorem rowEval7633 (x : Key → ℝ) : Integer.Sparse.eval row7633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7633, Integer.Sparse.eval_collectBalanced, rawRowCheck7633]

theorem rawRowCheck7634 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form1 = rawRow7634 := by decide +kernel

theorem rowCheck7634 : row7634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7634 := by decide +kernel

theorem rowEval7634 (x : Key → ℝ) : Integer.Sparse.eval row7634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7634, Integer.Sparse.eval_collectBalanced, rawRowCheck7634]

theorem rawRowCheck7635 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form1 = rawRow7635 := by decide +kernel

theorem rowCheck7635 : row7635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7635 := by decide +kernel

theorem rowEval7635 (x : Key → ℝ) : Integer.Sparse.eval row7635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7635, Integer.Sparse.eval_collectBalanced, rawRowCheck7635]

theorem rawRowCheck7636 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form1 = rawRow7636 := by decide +kernel

theorem rowCheck7636 : row7636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7636 := by decide +kernel

theorem rowEval7636 (x : Key → ℝ) : Integer.Sparse.eval row7636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7636, Integer.Sparse.eval_collectBalanced, rawRowCheck7636]

theorem rawRowCheck7637 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form1 = rawRow7637 := by decide +kernel

theorem rowCheck7637 : row7637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7637 := by decide +kernel

theorem rowEval7637 (x : Key → ℝ) : Integer.Sparse.eval row7637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7637, Integer.Sparse.eval_collectBalanced, rawRowCheck7637]

theorem rawRowCheck7638 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form1 = rawRow7638 := by decide +kernel

theorem rowCheck7638 : row7638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7638 := by decide +kernel

theorem rowEval7638 (x : Key → ℝ) : Integer.Sparse.eval row7638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7638, Integer.Sparse.eval_collectBalanced, rawRowCheck7638]

theorem rawRowCheck7639 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form1 = rawRow7639 := by decide +kernel

theorem rowCheck7639 : row7639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7639 := by decide +kernel

theorem rowEval7639 (x : Key → ℝ) : Integer.Sparse.eval row7639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7639, Integer.Sparse.eval_collectBalanced, rawRowCheck7639]

theorem rawRowCheck7640 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form1 = rawRow7640 := by decide +kernel

theorem rowCheck7640 : row7640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7640 := by decide +kernel

theorem rowEval7640 (x : Key → ℝ) : Integer.Sparse.eval row7640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7640, Integer.Sparse.eval_collectBalanced, rawRowCheck7640]

theorem rawRowCheck7641 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form1 = rawRow7641 := by decide +kernel

theorem rowCheck7641 : row7641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7641 := by decide +kernel

theorem rowEval7641 (x : Key → ℝ) : Integer.Sparse.eval row7641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7641, Integer.Sparse.eval_collectBalanced, rawRowCheck7641]

theorem rawRowCheck7642 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form1 = rawRow7642 := by decide +kernel

theorem rowCheck7642 : row7642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7642 := by decide +kernel

theorem rowEval7642 (x : Key → ℝ) : Integer.Sparse.eval row7642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7642, Integer.Sparse.eval_collectBalanced, rawRowCheck7642]

theorem rawRowCheck7643 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form1 = rawRow7643 := by decide +kernel

theorem rowCheck7643 : row7643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7643 := by decide +kernel

theorem rowEval7643 (x : Key → ℝ) : Integer.Sparse.eval row7643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7643, Integer.Sparse.eval_collectBalanced, rawRowCheck7643]

theorem rawRowCheck7644 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form1 = rawRow7644 := by decide +kernel

theorem rowCheck7644 : row7644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7644 := by decide +kernel

theorem rowEval7644 (x : Key → ℝ) : Integer.Sparse.eval row7644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7644, Integer.Sparse.eval_collectBalanced, rawRowCheck7644]

theorem rawRowCheck7645 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form1 = rawRow7645 := by decide +kernel

theorem rowCheck7645 : row7645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7645 := by decide +kernel

theorem rowEval7645 (x : Key → ℝ) : Integer.Sparse.eval row7645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7645, Integer.Sparse.eval_collectBalanced, rawRowCheck7645]

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

theorem rawRowCheck8857 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow8857 := by decide +kernel

theorem rowCheck8857 : row8857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8857 := by decide +kernel

theorem rowEval8857 (x : Key → ℝ) : Integer.Sparse.eval row8857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8857, Integer.Sparse.eval_collectBalanced, rawRowCheck8857]

theorem rawRowCheck8858 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow8858 := by decide +kernel

theorem rowCheck8858 : row8858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8858 := by decide +kernel

theorem rowEval8858 (x : Key → ℝ) : Integer.Sparse.eval row8858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8858, Integer.Sparse.eval_collectBalanced, rawRowCheck8858]

theorem rawRowCheck8859 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow8859 := by decide +kernel

theorem rowCheck8859 : row8859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8859 := by decide +kernel

theorem rowEval8859 (x : Key → ℝ) : Integer.Sparse.eval row8859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8859, Integer.Sparse.eval_collectBalanced, rawRowCheck8859]

theorem rawRowCheck8860 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8860 := by decide +kernel

theorem rowCheck8860 : row8860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8860 := by decide +kernel

theorem rowEval8860 (x : Key → ℝ) : Integer.Sparse.eval row8860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8860, Integer.Sparse.eval_collectBalanced, rawRowCheck8860]

theorem rawRowCheck8861 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form1 = rawRow8861 := by decide +kernel

theorem rowCheck8861 : row8861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8861 := by decide +kernel

theorem rowEval8861 (x : Key → ℝ) : Integer.Sparse.eval row8861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8861, Integer.Sparse.eval_collectBalanced, rawRowCheck8861]

theorem rawRowCheck8862 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form1 = rawRow8862 := by decide +kernel

theorem rowCheck8862 : row8862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8862 := by decide +kernel

theorem rowEval8862 (x : Key → ℝ) : Integer.Sparse.eval row8862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8862, Integer.Sparse.eval_collectBalanced, rawRowCheck8862]

theorem rawRowCheck8863 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form1 = rawRow8863 := by decide +kernel

theorem rowCheck8863 : row8863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8863 := by decide +kernel

theorem rowEval8863 (x : Key → ℝ) : Integer.Sparse.eval row8863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8863, Integer.Sparse.eval_collectBalanced, rawRowCheck8863]

theorem rawRowCheck8864 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form1 = rawRow8864 := by decide +kernel

theorem rowCheck8864 : row8864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8864 := by decide +kernel

theorem rowEval8864 (x : Key → ℝ) : Integer.Sparse.eval row8864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8864, Integer.Sparse.eval_collectBalanced, rawRowCheck8864]

theorem rawRowCheck8865 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form1 = rawRow8865 := by decide +kernel

theorem rowCheck8865 : row8865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8865 := by decide +kernel

theorem rowEval8865 (x : Key → ℝ) : Integer.Sparse.eval row8865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8865, Integer.Sparse.eval_collectBalanced, rawRowCheck8865]

theorem rawRowCheck8866 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form1 = rawRow8866 := by decide +kernel

theorem rowCheck8866 : row8866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8866 := by decide +kernel

theorem rowEval8866 (x : Key → ℝ) : Integer.Sparse.eval row8866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8866, Integer.Sparse.eval_collectBalanced, rawRowCheck8866]

theorem rawRowCheck8867 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form1 = rawRow8867 := by decide +kernel

theorem rowCheck8867 : row8867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8867 := by decide +kernel

theorem rowEval8867 (x : Key → ℝ) : Integer.Sparse.eval row8867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8867, Integer.Sparse.eval_collectBalanced, rawRowCheck8867]

theorem rawRowCheck8868 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form1 = rawRow8868 := by decide +kernel

theorem rowCheck8868 : row8868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8868 := by decide +kernel

theorem rowEval8868 (x : Key → ℝ) : Integer.Sparse.eval row8868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8868, Integer.Sparse.eval_collectBalanced, rawRowCheck8868]

theorem rawRowCheck8869 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form1 = rawRow8869 := by decide +kernel

theorem rowCheck8869 : row8869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8869 := by decide +kernel

theorem rowEval8869 (x : Key → ℝ) : Integer.Sparse.eval row8869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8869, Integer.Sparse.eval_collectBalanced, rawRowCheck8869]

theorem rawRowCheck8870 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow8870 := by decide +kernel

theorem rowCheck8870 : row8870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8870 := by decide +kernel

theorem rowEval8870 (x : Key → ℝ) : Integer.Sparse.eval row8870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8870, Integer.Sparse.eval_collectBalanced, rawRowCheck8870]

theorem rawRowCheck8871 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow8871 := by decide +kernel

theorem rowCheck8871 : row8871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8871 := by decide +kernel

theorem rowEval8871 (x : Key → ℝ) : Integer.Sparse.eval row8871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8871, Integer.Sparse.eval_collectBalanced, rawRowCheck8871]

theorem rawRowCheck8872 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow8872 := by decide +kernel

theorem rowCheck8872 : row8872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8872 := by decide +kernel

theorem rowEval8872 (x : Key → ℝ) : Integer.Sparse.eval row8872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8872, Integer.Sparse.eval_collectBalanced, rawRowCheck8872]

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

theorem entryCheck12_1 : entry12_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_1 k)) := by decide +kernel

theorem rowsSound12_1 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7510 x
  · exact rowEval7511 x
  · exact rowEval7512 x
  · exact rowEval7513 x
  · exact rowEval8761 x
  · exact rowEval8762 x
  · exact rowEval8763 x
  · exact rowEval8764 x

theorem entryEval12_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_1 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck12_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_1]

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

theorem rawRowCheck9069 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow9069 := by decide +kernel

theorem rowCheck9069 : row9069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9069 := by decide +kernel

theorem rowEval9069 (x : Key → ℝ) : Integer.Sparse.eval row9069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9069, Integer.Sparse.eval_collectBalanced, rawRowCheck9069]

theorem rawRowCheck9070 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9070 := by decide +kernel

theorem rowCheck9070 : row9070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9070 := by decide +kernel

theorem rowEval9070 (x : Key → ℝ) : Integer.Sparse.eval row9070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9070, Integer.Sparse.eval_collectBalanced, rawRowCheck9070]

theorem rawRowCheck9071 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9071 := by decide +kernel

theorem rowCheck9071 : row9071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9071 := by decide +kernel

theorem rowEval9071 (x : Key → ℝ) : Integer.Sparse.eval row9071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9071, Integer.Sparse.eval_collectBalanced, rawRowCheck9071]

theorem rawRowCheck9072 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9072 := by decide +kernel

theorem rowCheck9072 : row9072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9072 := by decide +kernel

theorem rowEval9072 (x : Key → ℝ) : Integer.Sparse.eval row9072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9072, Integer.Sparse.eval_collectBalanced, rawRowCheck9072]

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

theorem entryCheck13_1 : entry13_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_1 k)) := by decide +kernel

theorem rowsSound13_1 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8857 x
  · exact rowEval8858 x
  · exact rowEval8859 x
  · exact rowEval8860 x
  · exact rowEval8861 x
  · exact rowEval8862 x
  · exact rowEval8863 x
  · exact rowEval8864 x
  · exact rowEval8865 x
  · exact rowEval8866 x
  · exact rowEval8867 x
  · exact rowEval8868 x
  · exact rowEval8869 x
  · exact rowEval8870 x
  · exact rowEval8871 x
  · exact rowEval8872 x

theorem entryEval13_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_1 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck13_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_1]

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

theorem rawRowCheck9185 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form1 = rawRow9185 := by decide +kernel

theorem rowCheck9185 : row9185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9185 := by decide +kernel

theorem rowEval9185 (x : Key → ℝ) : Integer.Sparse.eval row9185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9185, Integer.Sparse.eval_collectBalanced, rawRowCheck9185]

theorem rawRowCheck9186 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form1 = rawRow9186 := by decide +kernel

theorem rowCheck9186 : row9186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9186 := by decide +kernel

theorem rowEval9186 (x : Key → ℝ) : Integer.Sparse.eval row9186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9186, Integer.Sparse.eval_collectBalanced, rawRowCheck9186]

theorem rawRowCheck9187 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form1 = rawRow9187 := by decide +kernel

theorem rowCheck9187 : row9187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9187 := by decide +kernel

theorem rowEval9187 (x : Key → ℝ) : Integer.Sparse.eval row9187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9187, Integer.Sparse.eval_collectBalanced, rawRowCheck9187]

theorem rawRowCheck9188 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9188 := by decide +kernel

theorem rowCheck9188 : row9188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9188 := by decide +kernel

theorem rowEval9188 (x : Key → ℝ) : Integer.Sparse.eval row9188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9188, Integer.Sparse.eval_collectBalanced, rawRowCheck9188]

theorem rawRowCheck9189 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9189 := by decide +kernel

theorem rowCheck9189 : row9189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9189 := by decide +kernel

theorem rowEval9189 (x : Key → ℝ) : Integer.Sparse.eval row9189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9189, Integer.Sparse.eval_collectBalanced, rawRowCheck9189]

theorem rawRowCheck9190 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9190 := by decide +kernel

theorem rowCheck9190 : row9190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9190 := by decide +kernel

theorem rowEval9190 (x : Key → ℝ) : Integer.Sparse.eval row9190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9190, Integer.Sparse.eval_collectBalanced, rawRowCheck9190]

theorem rawRowCheck9191 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9191 := by decide +kernel

theorem rowCheck9191 : row9191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9191 := by decide +kernel

theorem rowEval9191 (x : Key → ℝ) : Integer.Sparse.eval row9191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9191, Integer.Sparse.eval_collectBalanced, rawRowCheck9191]

theorem rawRowCheck9192 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9192 := by decide +kernel

theorem rowCheck9192 : row9192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9192 := by decide +kernel

theorem rowEval9192 (x : Key → ℝ) : Integer.Sparse.eval row9192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9192, Integer.Sparse.eval_collectBalanced, rawRowCheck9192]

theorem rawRowCheck9193 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9193 := by decide +kernel

theorem rowCheck9193 : row9193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9193 := by decide +kernel

theorem rowEval9193 (x : Key → ℝ) : Integer.Sparse.eval row9193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9193, Integer.Sparse.eval_collectBalanced, rawRowCheck9193]

theorem rawRowCheck9194 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9194 := by decide +kernel

theorem rowCheck9194 : row9194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9194 := by decide +kernel

theorem rowEval9194 (x : Key → ℝ) : Integer.Sparse.eval row9194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9194, Integer.Sparse.eval_collectBalanced, rawRowCheck9194]

theorem rawRowCheck9195 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9195 := by decide +kernel

theorem rowCheck9195 : row9195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9195 := by decide +kernel

theorem rowEval9195 (x : Key → ℝ) : Integer.Sparse.eval row9195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9195, Integer.Sparse.eval_collectBalanced, rawRowCheck9195]

theorem rawRowCheck9196 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9196 := by decide +kernel

theorem rowCheck9196 : row9196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9196 := by decide +kernel

theorem rowEval9196 (x : Key → ℝ) : Integer.Sparse.eval row9196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9196, Integer.Sparse.eval_collectBalanced, rawRowCheck9196]

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

theorem entryCheck14_1 : entry14_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_1 k)) := by decide +kernel

theorem rowsSound14_1 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7398 x
  · exact rowEval7399 x
  · exact rowEval7400 x
  · exact rowEval7401 x
  · exact rowEval9069 x
  · exact rowEval9070 x
  · exact rowEval9071 x
  · exact rowEval9072 x

theorem entryEval14_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_1 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck14_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_1]

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

theorem rawRowCheck9385 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form1 = rawRow9385 := by decide +kernel

theorem rowCheck9385 : row9385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9385 := by decide +kernel

theorem rowEval9385 (x : Key → ℝ) : Integer.Sparse.eval row9385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9385, Integer.Sparse.eval_collectBalanced, rawRowCheck9385]

theorem rawRowCheck9386 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form1 = rawRow9386 := by decide +kernel

theorem rowCheck9386 : row9386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9386 := by decide +kernel

theorem rowEval9386 (x : Key → ℝ) : Integer.Sparse.eval row9386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9386, Integer.Sparse.eval_collectBalanced, rawRowCheck9386]

theorem rawRowCheck9387 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form1 = rawRow9387 := by decide +kernel

theorem rowCheck9387 : row9387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9387 := by decide +kernel

theorem rowEval9387 (x : Key → ℝ) : Integer.Sparse.eval row9387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9387, Integer.Sparse.eval_collectBalanced, rawRowCheck9387]

theorem rawRowCheck9388 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form1 = rawRow9388 := by decide +kernel

theorem rowCheck9388 : row9388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9388 := by decide +kernel

theorem rowEval9388 (x : Key → ℝ) : Integer.Sparse.eval row9388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9388, Integer.Sparse.eval_collectBalanced, rawRowCheck9388]

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

theorem entryCheck15_1 : entry15_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_1 k)) := by decide +kernel

theorem rowsSound15_1 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8669 x
  · exact rowEval8670 x
  · exact rowEval8671 x
  · exact rowEval8672 x
  · exact rowEval9185 x
  · exact rowEval9186 x
  · exact rowEval9187 x
  · exact rowEval9188 x
  · exact rowEval9189 x
  · exact rowEval9190 x
  · exact rowEval9191 x
  · exact rowEval9192 x
  · exact rowEval9193 x
  · exact rowEval9194 x
  · exact rowEval9195 x
  · exact rowEval9196 x

theorem entryEval15_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_1 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck15_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_1]

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

theorem rawRowCheck9525 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form1 = rawRow9525 := by decide +kernel

theorem rowCheck9525 : row9525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9525 := by decide +kernel

theorem rowEval9525 (x : Key → ℝ) : Integer.Sparse.eval row9525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9525, Integer.Sparse.eval_collectBalanced, rawRowCheck9525]

theorem rawRowCheck9526 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form1 = rawRow9526 := by decide +kernel

theorem rowCheck9526 : row9526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9526 := by decide +kernel

theorem rowEval9526 (x : Key → ℝ) : Integer.Sparse.eval row9526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9526, Integer.Sparse.eval_collectBalanced, rawRowCheck9526]

theorem rawRowCheck9527 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form1 = rawRow9527 := by decide +kernel

theorem rowCheck9527 : row9527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9527 := by decide +kernel

theorem rowEval9527 (x : Key → ℝ) : Integer.Sparse.eval row9527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9527, Integer.Sparse.eval_collectBalanced, rawRowCheck9527]

theorem rawRowCheck9528 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form1 = rawRow9528 := by decide +kernel

theorem rowCheck9528 : row9528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9528 := by decide +kernel

theorem rowEval9528 (x : Key → ℝ) : Integer.Sparse.eval row9528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9528, Integer.Sparse.eval_collectBalanced, rawRowCheck9528]

theorem rawRowCheck9529 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form1 = rawRow9529 := by decide +kernel

theorem rowCheck9529 : row9529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9529 := by decide +kernel

theorem rowEval9529 (x : Key → ℝ) : Integer.Sparse.eval row9529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9529, Integer.Sparse.eval_collectBalanced, rawRowCheck9529]

theorem rawRowCheck9530 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form1 = rawRow9530 := by decide +kernel

theorem rowCheck9530 : row9530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9530 := by decide +kernel

theorem rowEval9530 (x : Key → ℝ) : Integer.Sparse.eval row9530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9530, Integer.Sparse.eval_collectBalanced, rawRowCheck9530]

theorem rawRowCheck9531 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form1 = rawRow9531 := by decide +kernel

theorem rowCheck9531 : row9531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9531 := by decide +kernel

theorem rowEval9531 (x : Key → ℝ) : Integer.Sparse.eval row9531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9531, Integer.Sparse.eval_collectBalanced, rawRowCheck9531]

theorem rawRowCheck9532 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form1 = rawRow9532 := by decide +kernel

theorem rowCheck9532 : row9532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9532 := by decide +kernel

theorem rowEval9532 (x : Key → ℝ) : Integer.Sparse.eval row9532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9532, Integer.Sparse.eval_collectBalanced, rawRowCheck9532]

theorem rawRowCheck9533 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form1 = rawRow9533 := by decide +kernel

theorem rowCheck9533 : row9533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9533 := by decide +kernel

theorem rowEval9533 (x : Key → ℝ) : Integer.Sparse.eval row9533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9533, Integer.Sparse.eval_collectBalanced, rawRowCheck9533]

theorem rawRowCheck9534 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form1 = rawRow9534 := by decide +kernel

theorem rowCheck9534 : row9534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9534 := by decide +kernel

theorem rowEval9534 (x : Key → ℝ) : Integer.Sparse.eval row9534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9534, Integer.Sparse.eval_collectBalanced, rawRowCheck9534]

theorem rawRowCheck9535 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form1 = rawRow9535 := by decide +kernel

theorem rowCheck9535 : row9535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9535 := by decide +kernel

theorem rowEval9535 (x : Key → ℝ) : Integer.Sparse.eval row9535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9535, Integer.Sparse.eval_collectBalanced, rawRowCheck9535]

theorem rawRowCheck9536 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form1 = rawRow9536 := by decide +kernel

theorem rowCheck9536 : row9536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9536 := by decide +kernel

theorem rowEval9536 (x : Key → ℝ) : Integer.Sparse.eval row9536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9536, Integer.Sparse.eval_collectBalanced, rawRowCheck9536]

theorem rawRowCheck9537 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form1 = rawRow9537 := by decide +kernel

theorem rowCheck9537 : row9537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9537 := by decide +kernel

theorem rowEval9537 (x : Key → ℝ) : Integer.Sparse.eval row9537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9537, Integer.Sparse.eval_collectBalanced, rawRowCheck9537]

theorem rawRowCheck9538 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form1 = rawRow9538 := by decide +kernel

theorem rowCheck9538 : row9538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9538 := by decide +kernel

theorem rowEval9538 (x : Key → ℝ) : Integer.Sparse.eval row9538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9538, Integer.Sparse.eval_collectBalanced, rawRowCheck9538]

theorem rawRowCheck9539 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form1 = rawRow9539 := by decide +kernel

theorem rowCheck9539 : row9539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9539 := by decide +kernel

theorem rowEval9539 (x : Key → ℝ) : Integer.Sparse.eval row9539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9539, Integer.Sparse.eval_collectBalanced, rawRowCheck9539]

theorem rawRowCheck9540 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form1 = rawRow9540 := by decide +kernel

theorem rowCheck9540 : row9540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9540 := by decide +kernel

theorem rowEval9540 (x : Key → ℝ) : Integer.Sparse.eval row9540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9540, Integer.Sparse.eval_collectBalanced, rawRowCheck9540]

theorem rawRowCheck9541 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form1 = rawRow9541 := by decide +kernel

theorem rowCheck9541 : row9541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9541 := by decide +kernel

theorem rowEval9541 (x : Key → ℝ) : Integer.Sparse.eval row9541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9541, Integer.Sparse.eval_collectBalanced, rawRowCheck9541]

theorem rawRowCheck9542 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form1 = rawRow9542 := by decide +kernel

theorem rowCheck9542 : row9542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9542 := by decide +kernel

theorem rowEval9542 (x : Key → ℝ) : Integer.Sparse.eval row9542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9542, Integer.Sparse.eval_collectBalanced, rawRowCheck9542]

theorem rawRowCheck9543 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form1 = rawRow9543 := by decide +kernel

theorem rowCheck9543 : row9543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9543 := by decide +kernel

theorem rowEval9543 (x : Key → ℝ) : Integer.Sparse.eval row9543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9543, Integer.Sparse.eval_collectBalanced, rawRowCheck9543]

theorem rawRowCheck9544 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form1 = rawRow9544 := by decide +kernel

theorem rowCheck9544 : row9544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9544 := by decide +kernel

theorem rowEval9544 (x : Key → ℝ) : Integer.Sparse.eval row9544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9544, Integer.Sparse.eval_collectBalanced, rawRowCheck9544]

theorem rawRowCheck9545 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form1 = rawRow9545 := by decide +kernel

theorem rowCheck9545 : row9545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9545 := by decide +kernel

theorem rowEval9545 (x : Key → ℝ) : Integer.Sparse.eval row9545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9545, Integer.Sparse.eval_collectBalanced, rawRowCheck9545]

theorem rawRowCheck9546 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form1 = rawRow9546 := by decide +kernel

theorem rowCheck9546 : row9546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9546 := by decide +kernel

theorem rowEval9546 (x : Key → ℝ) : Integer.Sparse.eval row9546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9546, Integer.Sparse.eval_collectBalanced, rawRowCheck9546]

theorem rawRowCheck9547 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form1 = rawRow9547 := by decide +kernel

theorem rowCheck9547 : row9547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9547 := by decide +kernel

theorem rowEval9547 (x : Key → ℝ) : Integer.Sparse.eval row9547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9547, Integer.Sparse.eval_collectBalanced, rawRowCheck9547]

theorem rawRowCheck9548 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form1 = rawRow9548 := by decide +kernel

theorem rowCheck9548 : row9548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9548 := by decide +kernel

theorem rowEval9548 (x : Key → ℝ) : Integer.Sparse.eval row9548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9548, Integer.Sparse.eval_collectBalanced, rawRowCheck9548]

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

theorem entryCheck16_1 : entry16_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_1 k)) := by decide +kernel

theorem rowsSound16_1 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval9385 x
  · exact rowEval9386 x
  · exact rowEval9387 x
  · exact rowEval9388 x
  · exact rowEval7446 x
  · exact rowEval7447 x
  · exact rowEval7448 x
  · exact rowEval7449 x

theorem entryEval16_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_1 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck16_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_1]

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

theorem rawRowCheck9957 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1 = rawRow9957 := by decide +kernel

theorem rowCheck9957 : row9957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9957 := by decide +kernel

theorem rowEval9957 (x : Key → ℝ) : Integer.Sparse.eval row9957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9957, Integer.Sparse.eval_collectBalanced, rawRowCheck9957]

theorem rawRowCheck9958 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1 = rawRow9958 := by decide +kernel

theorem rowCheck9958 : row9958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9958 := by decide +kernel

theorem rowEval9958 (x : Key → ℝ) : Integer.Sparse.eval row9958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9958, Integer.Sparse.eval_collectBalanced, rawRowCheck9958]

theorem rawRowCheck9959 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1 = rawRow9959 := by decide +kernel

theorem rowCheck9959 : row9959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9959 := by decide +kernel

theorem rowEval9959 (x : Key → ℝ) : Integer.Sparse.eval row9959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9959, Integer.Sparse.eval_collectBalanced, rawRowCheck9959]

theorem rawRowCheck9960 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1 = rawRow9960 := by decide +kernel

theorem rowCheck9960 : row9960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9960 := by decide +kernel

theorem rowEval9960 (x : Key → ℝ) : Integer.Sparse.eval row9960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9960, Integer.Sparse.eval_collectBalanced, rawRowCheck9960]

theorem rawRowCheck9961 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1 = rawRow9961 := by decide +kernel

theorem rowCheck9961 : row9961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9961 := by decide +kernel

theorem rowEval9961 (x : Key → ℝ) : Integer.Sparse.eval row9961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9961, Integer.Sparse.eval_collectBalanced, rawRowCheck9961]

theorem rawRowCheck9962 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1 = rawRow9962 := by decide +kernel

theorem rowCheck9962 : row9962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9962 := by decide +kernel

theorem rowEval9962 (x : Key → ℝ) : Integer.Sparse.eval row9962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9962, Integer.Sparse.eval_collectBalanced, rawRowCheck9962]

theorem rawRowCheck9963 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9963 := by decide +kernel

theorem rowCheck9963 : row9963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9963 := by decide +kernel

theorem rowEval9963 (x : Key → ℝ) : Integer.Sparse.eval row9963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9963, Integer.Sparse.eval_collectBalanced, rawRowCheck9963]

theorem rawRowCheck9964 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9964 := by decide +kernel

theorem rowCheck9964 : row9964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9964 := by decide +kernel

theorem rowEval9964 (x : Key → ℝ) : Integer.Sparse.eval row9964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9964, Integer.Sparse.eval_collectBalanced, rawRowCheck9964]

theorem rawRowCheck9965 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9965 := by decide +kernel

theorem rowCheck9965 : row9965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9965 := by decide +kernel

theorem rowEval9965 (x : Key → ℝ) : Integer.Sparse.eval row9965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9965, Integer.Sparse.eval_collectBalanced, rawRowCheck9965]

theorem rawRowCheck9966 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9966 := by decide +kernel

theorem rowCheck9966 : row9966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9966 := by decide +kernel

theorem rowEval9966 (x : Key → ℝ) : Integer.Sparse.eval row9966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9966, Integer.Sparse.eval_collectBalanced, rawRowCheck9966]

theorem rawRowCheck9967 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9967 := by decide +kernel

theorem rowCheck9967 : row9967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9967 := by decide +kernel

theorem rowEval9967 (x : Key → ℝ) : Integer.Sparse.eval row9967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9967, Integer.Sparse.eval_collectBalanced, rawRowCheck9967]

theorem rawRowCheck9968 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9968 := by decide +kernel

theorem rowCheck9968 : row9968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9968 := by decide +kernel

theorem rowEval9968 (x : Key → ℝ) : Integer.Sparse.eval row9968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9968, Integer.Sparse.eval_collectBalanced, rawRowCheck9968]

theorem rawRowCheck9969 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form1 = rawRow9969 := by decide +kernel

theorem rowCheck9969 : row9969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9969 := by decide +kernel

theorem rowEval9969 (x : Key → ℝ) : Integer.Sparse.eval row9969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9969, Integer.Sparse.eval_collectBalanced, rawRowCheck9969]

theorem rawRowCheck9970 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form1 = rawRow9970 := by decide +kernel

theorem rowCheck9970 : row9970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9970 := by decide +kernel

theorem rowEval9970 (x : Key → ℝ) : Integer.Sparse.eval row9970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9970, Integer.Sparse.eval_collectBalanced, rawRowCheck9970]

theorem rawRowCheck9971 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form1 = rawRow9971 := by decide +kernel

theorem rowCheck9971 : row9971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9971 := by decide +kernel

theorem rowEval9971 (x : Key → ℝ) : Integer.Sparse.eval row9971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9971, Integer.Sparse.eval_collectBalanced, rawRowCheck9971]

theorem rawRowCheck9972 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9972 := by decide +kernel

theorem rowCheck9972 : row9972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9972 := by decide +kernel

theorem rowEval9972 (x : Key → ℝ) : Integer.Sparse.eval row9972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9972, Integer.Sparse.eval_collectBalanced, rawRowCheck9972]

theorem rawRowCheck9973 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9973 := by decide +kernel

theorem rowCheck9973 : row9973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9973 := by decide +kernel

theorem rowEval9973 (x : Key → ℝ) : Integer.Sparse.eval row9973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9973, Integer.Sparse.eval_collectBalanced, rawRowCheck9973]

theorem rawRowCheck9974 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9974 := by decide +kernel

theorem rowCheck9974 : row9974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9974 := by decide +kernel

theorem rowEval9974 (x : Key → ℝ) : Integer.Sparse.eval row9974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9974, Integer.Sparse.eval_collectBalanced, rawRowCheck9974]

theorem rawRowCheck9975 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9975 := by decide +kernel

theorem rowCheck9975 : row9975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9975 := by decide +kernel

theorem rowEval9975 (x : Key → ℝ) : Integer.Sparse.eval row9975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9975, Integer.Sparse.eval_collectBalanced, rawRowCheck9975]

theorem rawRowCheck9976 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9976 := by decide +kernel

theorem rowCheck9976 : row9976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9976 := by decide +kernel

theorem rowEval9976 (x : Key → ℝ) : Integer.Sparse.eval row9976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9976, Integer.Sparse.eval_collectBalanced, rawRowCheck9976]

theorem rawRowCheck9977 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9977 := by decide +kernel

theorem rowCheck9977 : row9977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9977 := by decide +kernel

theorem rowEval9977 (x : Key → ℝ) : Integer.Sparse.eval row9977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9977, Integer.Sparse.eval_collectBalanced, rawRowCheck9977]

theorem rawRowCheck9978 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9978 := by decide +kernel

theorem rowCheck9978 : row9978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9978 := by decide +kernel

theorem rowEval9978 (x : Key → ℝ) : Integer.Sparse.eval row9978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9978, Integer.Sparse.eval_collectBalanced, rawRowCheck9978]

theorem rawRowCheck9979 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9979 := by decide +kernel

theorem rowCheck9979 : row9979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9979 := by decide +kernel

theorem rowEval9979 (x : Key → ℝ) : Integer.Sparse.eval row9979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9979, Integer.Sparse.eval_collectBalanced, rawRowCheck9979]

theorem rawRowCheck9980 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9980 := by decide +kernel

theorem rowCheck9980 : row9980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9980 := by decide +kernel

theorem rowEval9980 (x : Key → ℝ) : Integer.Sparse.eval row9980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9980, Integer.Sparse.eval_collectBalanced, rawRowCheck9980]

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

theorem entryCheck17_1 : entry17_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_1 k)) := by decide +kernel

theorem rowsSound17_1 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval9525 x
  · exact rowEval9526 x
  · exact rowEval9527 x
  · exact rowEval9528 x
  · exact rowEval9529 x
  · exact rowEval9530 x
  · exact rowEval9531 x
  · exact rowEval9532 x
  · exact rowEval9533 x
  · exact rowEval9534 x
  · exact rowEval9535 x
  · exact rowEval9536 x
  · exact rowEval9537 x
  · exact rowEval9538 x
  · exact rowEval9539 x
  · exact rowEval9540 x
  · exact rowEval9541 x
  · exact rowEval9542 x
  · exact rowEval9543 x
  · exact rowEval9544 x
  · exact rowEval9545 x
  · exact rowEval9546 x
  · exact rowEval9547 x
  · exact rowEval9548 x

theorem entryEval17_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_1 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck17_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_1]

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

theorem rawRowCheck10399 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form1 = rawRow10399 := by decide +kernel

theorem rowCheck10399 : row10399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10399 := by decide +kernel

theorem rowEval10399 (x : Key → ℝ) : Integer.Sparse.eval row10399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10399, Integer.Sparse.eval_collectBalanced, rawRowCheck10399]

theorem rawRowCheck10400 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form1 = rawRow10400 := by decide +kernel

theorem rowCheck10400 : row10400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10400 := by decide +kernel

theorem rowEval10400 (x : Key → ℝ) : Integer.Sparse.eval row10400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10400, Integer.Sparse.eval_collectBalanced, rawRowCheck10400]

theorem rawRowCheck10401 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form1 = rawRow10401 := by decide +kernel

theorem rowCheck10401 : row10401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10401 := by decide +kernel

theorem rowEval10401 (x : Key → ℝ) : Integer.Sparse.eval row10401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10401, Integer.Sparse.eval_collectBalanced, rawRowCheck10401]

theorem rawRowCheck10402 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form1 = rawRow10402 := by decide +kernel

theorem rowCheck10402 : row10402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10402 := by decide +kernel

theorem rowEval10402 (x : Key → ℝ) : Integer.Sparse.eval row10402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10402, Integer.Sparse.eval_collectBalanced, rawRowCheck10402]

theorem rawRowCheck10403 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form1 = rawRow10403 := by decide +kernel

theorem rowCheck10403 : row10403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10403 := by decide +kernel

theorem rowEval10403 (x : Key → ℝ) : Integer.Sparse.eval row10403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10403, Integer.Sparse.eval_collectBalanced, rawRowCheck10403]

theorem rawRowCheck10404 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form1 = rawRow10404 := by decide +kernel

theorem rowCheck10404 : row10404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10404 := by decide +kernel

theorem rowEval10404 (x : Key → ℝ) : Integer.Sparse.eval row10404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10404, Integer.Sparse.eval_collectBalanced, rawRowCheck10404]

theorem rawRowCheck10405 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form1 = rawRow10405 := by decide +kernel

theorem rowCheck10405 : row10405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10405 := by decide +kernel

theorem rowEval10405 (x : Key → ℝ) : Integer.Sparse.eval row10405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10405, Integer.Sparse.eval_collectBalanced, rawRowCheck10405]

theorem rawRowCheck10406 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form1 = rawRow10406 := by decide +kernel

theorem rowCheck10406 : row10406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10406 := by decide +kernel

theorem rowEval10406 (x : Key → ℝ) : Integer.Sparse.eval row10406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10406, Integer.Sparse.eval_collectBalanced, rawRowCheck10406]

theorem rawRowCheck10407 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form1 = rawRow10407 := by decide +kernel

theorem rowCheck10407 : row10407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10407 := by decide +kernel

theorem rowEval10407 (x : Key → ℝ) : Integer.Sparse.eval row10407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10407, Integer.Sparse.eval_collectBalanced, rawRowCheck10407]

theorem rawRowCheck10408 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form1 = rawRow10408 := by decide +kernel

theorem rowCheck10408 : row10408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10408 := by decide +kernel

theorem rowEval10408 (x : Key → ℝ) : Integer.Sparse.eval row10408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10408, Integer.Sparse.eval_collectBalanced, rawRowCheck10408]

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

theorem entryCheck18_1 : entry18_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_1 k)) := by decide +kernel

theorem rowsSound18_1 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval9957 x
  · exact rowEval9958 x
  · exact rowEval9959 x
  · exact rowEval9960 x
  · exact rowEval9961 x
  · exact rowEval9962 x
  · exact rowEval9963 x
  · exact rowEval9964 x
  · exact rowEval9965 x
  · exact rowEval9966 x
  · exact rowEval9967 x
  · exact rowEval9968 x
  · exact rowEval9969 x
  · exact rowEval9970 x
  · exact rowEval9971 x
  · exact rowEval9972 x
  · exact rowEval9973 x
  · exact rowEval9974 x
  · exact rowEval9975 x
  · exact rowEval9976 x
  · exact rowEval9977 x
  · exact rowEval9978 x
  · exact rowEval9979 x
  · exact rowEval9980 x

theorem entryEval18_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_1 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck18_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_1]

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

theorem rawRowCheck10594 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow10594 := by decide +kernel

theorem rowCheck10594 : row10594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10594 := by decide +kernel

theorem rowEval10594 (x : Key → ℝ) : Integer.Sparse.eval row10594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10594, Integer.Sparse.eval_collectBalanced, rawRowCheck10594]

theorem rawRowCheck10595 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow10595 := by decide +kernel

theorem rowCheck10595 : row10595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10595 := by decide +kernel

theorem rowEval10595 (x : Key → ℝ) : Integer.Sparse.eval row10595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10595, Integer.Sparse.eval_collectBalanced, rawRowCheck10595]

theorem rawRowCheck10596 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow10596 := by decide +kernel

theorem rowCheck10596 : row10596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10596 := by decide +kernel

theorem rowEval10596 (x : Key → ℝ) : Integer.Sparse.eval row10596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10596, Integer.Sparse.eval_collectBalanced, rawRowCheck10596]

theorem rawRowCheck10597 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow10597 := by decide +kernel

theorem rowCheck10597 : row10597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10597 := by decide +kernel

theorem rowEval10597 (x : Key → ℝ) : Integer.Sparse.eval row10597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10597, Integer.Sparse.eval_collectBalanced, rawRowCheck10597]

theorem rawRowCheck10598 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow10598 := by decide +kernel

theorem rowCheck10598 : row10598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10598 := by decide +kernel

theorem rowEval10598 (x : Key → ℝ) : Integer.Sparse.eval row10598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10598, Integer.Sparse.eval_collectBalanced, rawRowCheck10598]

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

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval10399 x
  · exact rowEval10400 x
  · exact rowEval10401 x
  · exact rowEval10402 x
  · exact rowEval10403 x
  · exact rowEval10404 x
  · exact rowEval10405 x
  · exact rowEval10406 x
  · exact rowEval10407 x
  · exact rowEval10408 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

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

theorem rawRowCheck10730 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form1 = rawRow10730 := by decide +kernel

theorem rowCheck10730 : row10730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10730 := by decide +kernel

theorem rowEval10730 (x : Key → ℝ) : Integer.Sparse.eval row10730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10730, Integer.Sparse.eval_collectBalanced, rawRowCheck10730]

theorem rawRowCheck10731 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form1 = rawRow10731 := by decide +kernel

theorem rowCheck10731 : row10731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10731 := by decide +kernel

theorem rowEval10731 (x : Key → ℝ) : Integer.Sparse.eval row10731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10731, Integer.Sparse.eval_collectBalanced, rawRowCheck10731]

theorem rawRowCheck10732 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form1 = rawRow10732 := by decide +kernel

theorem rowCheck10732 : row10732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10732 := by decide +kernel

theorem rowEval10732 (x : Key → ℝ) : Integer.Sparse.eval row10732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10732, Integer.Sparse.eval_collectBalanced, rawRowCheck10732]

theorem rawRowCheck10733 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form1 = rawRow10733 := by decide +kernel

theorem rowCheck10733 : row10733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10733 := by decide +kernel

theorem rowEval10733 (x : Key → ℝ) : Integer.Sparse.eval row10733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10733, Integer.Sparse.eval_collectBalanced, rawRowCheck10733]

theorem rawRowCheck10734 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form1 = rawRow10734 := by decide +kernel

theorem rowCheck10734 : row10734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10734 := by decide +kernel

theorem rowEval10734 (x : Key → ℝ) : Integer.Sparse.eval row10734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10734, Integer.Sparse.eval_collectBalanced, rawRowCheck10734]

theorem rawRowCheck10735 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form1 = rawRow10735 := by decide +kernel

theorem rowCheck10735 : row10735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10735 := by decide +kernel

theorem rowEval10735 (x : Key → ℝ) : Integer.Sparse.eval row10735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10735, Integer.Sparse.eval_collectBalanced, rawRowCheck10735]

theorem rawRowCheck10736 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form1 = rawRow10736 := by decide +kernel

theorem rowCheck10736 : row10736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10736 := by decide +kernel

theorem rowEval10736 (x : Key → ℝ) : Integer.Sparse.eval row10736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10736, Integer.Sparse.eval_collectBalanced, rawRowCheck10736]

theorem rawRowCheck10737 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form1 = rawRow10737 := by decide +kernel

theorem rowCheck10737 : row10737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10737 := by decide +kernel

theorem rowEval10737 (x : Key → ℝ) : Integer.Sparse.eval row10737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10737, Integer.Sparse.eval_collectBalanced, rawRowCheck10737]

theorem rawRowCheck10738 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form1 = rawRow10738 := by decide +kernel

theorem rowCheck10738 : row10738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10738 := by decide +kernel

theorem rowEval10738 (x : Key → ℝ) : Integer.Sparse.eval row10738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10738, Integer.Sparse.eval_collectBalanced, rawRowCheck10738]

theorem rawRowCheck10739 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form1 = rawRow10739 := by decide +kernel

theorem rowCheck10739 : row10739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10739 := by decide +kernel

theorem rowEval10739 (x : Key → ℝ) : Integer.Sparse.eval row10739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10739, Integer.Sparse.eval_collectBalanced, rawRowCheck10739]

theorem rawRowCheck10740 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form1 = rawRow10740 := by decide +kernel

theorem rowCheck10740 : row10740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10740 := by decide +kernel

theorem rowEval10740 (x : Key → ℝ) : Integer.Sparse.eval row10740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10740, Integer.Sparse.eval_collectBalanced, rawRowCheck10740]

theorem rawRowCheck10741 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form1 = rawRow10741 := by decide +kernel

theorem rowCheck10741 : row10741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10741 := by decide +kernel

theorem rowEval10741 (x : Key → ℝ) : Integer.Sparse.eval row10741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10741, Integer.Sparse.eval_collectBalanced, rawRowCheck10741]

theorem rawRowCheck10742 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form1 = rawRow10742 := by decide +kernel

theorem rowCheck10742 : row10742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10742 := by decide +kernel

theorem rowEval10742 (x : Key → ℝ) : Integer.Sparse.eval row10742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10742, Integer.Sparse.eval_collectBalanced, rawRowCheck10742]

theorem rawRowCheck10743 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form1 = rawRow10743 := by decide +kernel

theorem rowCheck10743 : row10743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10743 := by decide +kernel

theorem rowEval10743 (x : Key → ℝ) : Integer.Sparse.eval row10743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10743, Integer.Sparse.eval_collectBalanced, rawRowCheck10743]

theorem rawRowCheck10744 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form1 = rawRow10744 := by decide +kernel

theorem rowCheck10744 : row10744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10744 := by decide +kernel

theorem rowEval10744 (x : Key → ℝ) : Integer.Sparse.eval row10744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10744, Integer.Sparse.eval_collectBalanced, rawRowCheck10744]

theorem rawRowCheck10745 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form1 = rawRow10745 := by decide +kernel

theorem rowCheck10745 : row10745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10745 := by decide +kernel

theorem rowEval10745 (x : Key → ℝ) : Integer.Sparse.eval row10745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10745, Integer.Sparse.eval_collectBalanced, rawRowCheck10745]

theorem rawRowCheck10746 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form1 = rawRow10746 := by decide +kernel

theorem rowCheck10746 : row10746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10746 := by decide +kernel

theorem rowEval10746 (x : Key → ℝ) : Integer.Sparse.eval row10746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10746, Integer.Sparse.eval_collectBalanced, rawRowCheck10746]

theorem rawRowCheck10747 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form1 = rawRow10747 := by decide +kernel

theorem rowCheck10747 : row10747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10747 := by decide +kernel

theorem rowEval10747 (x : Key → ℝ) : Integer.Sparse.eval row10747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10747, Integer.Sparse.eval_collectBalanced, rawRowCheck10747]

theorem rawRowCheck10748 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form1 = rawRow10748 := by decide +kernel

theorem rowCheck10748 : row10748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10748 := by decide +kernel

theorem rowEval10748 (x : Key → ℝ) : Integer.Sparse.eval row10748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10748, Integer.Sparse.eval_collectBalanced, rawRowCheck10748]

theorem rawRowCheck10749 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form1 = rawRow10749 := by decide +kernel

theorem rowCheck10749 : row10749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10749 := by decide +kernel

theorem rowEval10749 (x : Key → ℝ) : Integer.Sparse.eval row10749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10749, Integer.Sparse.eval_collectBalanced, rawRowCheck10749]

theorem rawRowCheck10750 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form1 = rawRow10750 := by decide +kernel

theorem rowCheck10750 : row10750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10750 := by decide +kernel

theorem rowEval10750 (x : Key → ℝ) : Integer.Sparse.eval row10750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10750, Integer.Sparse.eval_collectBalanced, rawRowCheck10750]

theorem rawRowCheck10751 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form1 = rawRow10751 := by decide +kernel

theorem rowCheck10751 : row10751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10751 := by decide +kernel

theorem rowEval10751 (x : Key → ℝ) : Integer.Sparse.eval row10751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10751, Integer.Sparse.eval_collectBalanced, rawRowCheck10751]

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

theorem entryCheck20_1 : entry20_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_1 k)) := by decide +kernel

theorem rowsSound20_1 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval10594 x
  · exact rowEval10595 x
  · exact rowEval10596 x
  · exact rowEval10597 x
  · exact rowEval10598 x

theorem entryEval20_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_1 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck20_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_1]

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

theorem rawRowCheck10752 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form1 = rawRow10752 := by decide +kernel

theorem rowCheck10752 : row10752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10752 := by decide +kernel

theorem rowEval10752 (x : Key → ℝ) : Integer.Sparse.eval row10752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10752, Integer.Sparse.eval_collectBalanced, rawRowCheck10752]

theorem rawRowCheck10753 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form1 = rawRow10753 := by decide +kernel

theorem rowCheck10753 : row10753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10753 := by decide +kernel

theorem rowEval10753 (x : Key → ℝ) : Integer.Sparse.eval row10753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10753, Integer.Sparse.eval_collectBalanced, rawRowCheck10753]

theorem rawRowCheck10754 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow10754 := by decide +kernel

theorem rowCheck10754 : row10754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10754 := by decide +kernel

theorem rowEval10754 (x : Key → ℝ) : Integer.Sparse.eval row10754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10754, Integer.Sparse.eval_collectBalanced, rawRowCheck10754]

theorem rawRowCheck10755 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow10755 := by decide +kernel

theorem rowCheck10755 : row10755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10755 := by decide +kernel

theorem rowEval10755 (x : Key → ℝ) : Integer.Sparse.eval row10755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10755, Integer.Sparse.eval_collectBalanced, rawRowCheck10755]

theorem rawRowCheck10756 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow10756 := by decide +kernel

theorem rowCheck10756 : row10756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10756 := by decide +kernel

theorem rowEval10756 (x : Key → ℝ) : Integer.Sparse.eval row10756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10756, Integer.Sparse.eval_collectBalanced, rawRowCheck10756]

theorem rawRowCheck10757 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow10757 := by decide +kernel

theorem rowCheck10757 : row10757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10757 := by decide +kernel

theorem rowEval10757 (x : Key → ℝ) : Integer.Sparse.eval row10757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10757, Integer.Sparse.eval_collectBalanced, rawRowCheck10757]

theorem rawRowCheck10758 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow10758 := by decide +kernel

theorem rowCheck10758 : row10758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10758 := by decide +kernel

theorem rowEval10758 (x : Key → ℝ) : Integer.Sparse.eval row10758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10758, Integer.Sparse.eval_collectBalanced, rawRowCheck10758]

theorem rawRowCheck10759 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow10759 := by decide +kernel

theorem rowCheck10759 : row10759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10759 := by decide +kernel

theorem rowEval10759 (x : Key → ℝ) : Integer.Sparse.eval row10759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10759, Integer.Sparse.eval_collectBalanced, rawRowCheck10759]

theorem rawRowCheck10760 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form1 = rawRow10760 := by decide +kernel

theorem rowCheck10760 : row10760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10760 := by decide +kernel

theorem rowEval10760 (x : Key → ℝ) : Integer.Sparse.eval row10760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10760, Integer.Sparse.eval_collectBalanced, rawRowCheck10760]

theorem rawRowCheck10761 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form1 = rawRow10761 := by decide +kernel

theorem rowCheck10761 : row10761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10761 := by decide +kernel

theorem rowEval10761 (x : Key → ℝ) : Integer.Sparse.eval row10761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10761, Integer.Sparse.eval_collectBalanced, rawRowCheck10761]

theorem rawRowCheck10762 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form1 = rawRow10762 := by decide +kernel

theorem rowCheck10762 : row10762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10762 := by decide +kernel

theorem rowEval10762 (x : Key → ℝ) : Integer.Sparse.eval row10762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10762, Integer.Sparse.eval_collectBalanced, rawRowCheck10762]

theorem rawRowCheck10763 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form1 = rawRow10763 := by decide +kernel

theorem rowCheck10763 : row10763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10763 := by decide +kernel

theorem rowEval10763 (x : Key → ℝ) : Integer.Sparse.eval row10763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10763, Integer.Sparse.eval_collectBalanced, rawRowCheck10763]

theorem rawRowCheck10764 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form1 = rawRow10764 := by decide +kernel

theorem rowCheck10764 : row10764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10764 := by decide +kernel

theorem rowEval10764 (x : Key → ℝ) : Integer.Sparse.eval row10764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10764, Integer.Sparse.eval_collectBalanced, rawRowCheck10764]

theorem rawRowCheck10765 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form1 = rawRow10765 := by decide +kernel

theorem rowCheck10765 : row10765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10765 := by decide +kernel

theorem rowEval10765 (x : Key → ℝ) : Integer.Sparse.eval row10765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10765, Integer.Sparse.eval_collectBalanced, rawRowCheck10765]

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

theorem entryCheck21_1 : entry21_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_1 k)) := by decide +kernel

theorem rowsSound21_1 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval10730 x
  · exact rowEval10731 x
  · exact rowEval10732 x
  · exact rowEval10733 x
  · exact rowEval10734 x
  · exact rowEval10735 x
  · exact rowEval10736 x
  · exact rowEval10737 x
  · exact rowEval10738 x
  · exact rowEval10739 x
  · exact rowEval10740 x
  · exact rowEval10741 x
  · exact rowEval10742 x
  · exact rowEval10743 x
  · exact rowEval10744 x
  · exact rowEval10745 x
  · exact rowEval10746 x
  · exact rowEval10747 x
  · exact rowEval10748 x
  · exact rowEval10749 x
  · exact rowEval10750 x
  · exact rowEval10751 x
  · exact rowEval10752 x
  · exact rowEval10753 x
  · exact rowEval10754 x
  · exact rowEval10755 x
  · exact rowEval10756 x
  · exact rowEval10757 x
  · exact rowEval10758 x
  · exact rowEval10759 x
  · exact rowEval10760 x
  · exact rowEval10761 x
  · exact rowEval10762 x
  · exact rowEval10763 x
  · exact rowEval10764 x
  · exact rowEval10765 x

theorem entryEval21_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_1 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck21_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_1]

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

theorem rawRowCheck11792 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form1 = rawRow11792 := by decide +kernel

theorem rowCheck11792 : row11792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11792 := by decide +kernel

theorem rowEval11792 (x : Key → ℝ) : Integer.Sparse.eval row11792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11792, Integer.Sparse.eval_collectBalanced, rawRowCheck11792]

theorem rawRowCheck11793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form1 = rawRow11793 := by decide +kernel

theorem rowCheck11793 : row11793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11793 := by decide +kernel

theorem rowEval11793 (x : Key → ℝ) : Integer.Sparse.eval row11793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11793, Integer.Sparse.eval_collectBalanced, rawRowCheck11793]

theorem rawRowCheck11794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form1 = rawRow11794 := by decide +kernel

theorem rowCheck11794 : row11794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11794 := by decide +kernel

theorem rowEval11794 (x : Key → ℝ) : Integer.Sparse.eval row11794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11794, Integer.Sparse.eval_collectBalanced, rawRowCheck11794]

theorem rawRowCheck11795 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form1 = rawRow11795 := by decide +kernel

theorem rowCheck11795 : row11795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11795 := by decide +kernel

theorem rowEval11795 (x : Key → ℝ) : Integer.Sparse.eval row11795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11795, Integer.Sparse.eval_collectBalanced, rawRowCheck11795]

theorem rawRowCheck11796 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form1 = rawRow11796 := by decide +kernel

theorem rowCheck11796 : row11796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11796 := by decide +kernel

theorem rowEval11796 (x : Key → ℝ) : Integer.Sparse.eval row11796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11796, Integer.Sparse.eval_collectBalanced, rawRowCheck11796]

theorem rawRowCheck11797 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form1 = rawRow11797 := by decide +kernel

theorem rowCheck11797 : row11797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11797 := by decide +kernel

theorem rowEval11797 (x : Key → ℝ) : Integer.Sparse.eval row11797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11797, Integer.Sparse.eval_collectBalanced, rawRowCheck11797]

theorem rawRowCheck11798 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1 = rawRow11798 := by decide +kernel

theorem rowCheck11798 : row11798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11798 := by decide +kernel

theorem rowEval11798 (x : Key → ℝ) : Integer.Sparse.eval row11798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11798, Integer.Sparse.eval_collectBalanced, rawRowCheck11798]

theorem rawRowCheck11799 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1 = rawRow11799 := by decide +kernel

theorem rowCheck11799 : row11799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11799 := by decide +kernel

theorem rowEval11799 (x : Key → ℝ) : Integer.Sparse.eval row11799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11799, Integer.Sparse.eval_collectBalanced, rawRowCheck11799]

theorem rawRowCheck11800 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1 = rawRow11800 := by decide +kernel

theorem rowCheck11800 : row11800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11800 := by decide +kernel

theorem rowEval11800 (x : Key → ℝ) : Integer.Sparse.eval row11800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11800, Integer.Sparse.eval_collectBalanced, rawRowCheck11800]

theorem rawRowCheck11801 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1 = rawRow11801 := by decide +kernel

theorem rowCheck11801 : row11801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11801 := by decide +kernel

theorem rowEval11801 (x : Key → ℝ) : Integer.Sparse.eval row11801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11801, Integer.Sparse.eval_collectBalanced, rawRowCheck11801]

theorem rawRowCheck11802 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1 = rawRow11802 := by decide +kernel

theorem rowCheck11802 : row11802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11802 := by decide +kernel

theorem rowEval11802 (x : Key → ℝ) : Integer.Sparse.eval row11802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11802, Integer.Sparse.eval_collectBalanced, rawRowCheck11802]

theorem rawRowCheck11803 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1 = rawRow11803 := by decide +kernel

theorem rowCheck11803 : row11803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11803 := by decide +kernel

theorem rowEval11803 (x : Key → ℝ) : Integer.Sparse.eval row11803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11803, Integer.Sparse.eval_collectBalanced, rawRowCheck11803]

theorem rawRowCheck11804 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1 = rawRow11804 := by decide +kernel

theorem rowCheck11804 : row11804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11804 := by decide +kernel

theorem rowEval11804 (x : Key → ℝ) : Integer.Sparse.eval row11804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11804, Integer.Sparse.eval_collectBalanced, rawRowCheck11804]

theorem rawRowCheck11805 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1 = rawRow11805 := by decide +kernel

theorem rowCheck11805 : row11805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11805 := by decide +kernel

theorem rowEval11805 (x : Key → ℝ) : Integer.Sparse.eval row11805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11805, Integer.Sparse.eval_collectBalanced, rawRowCheck11805]

theorem rawRowCheck11806 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1 = rawRow11806 := by decide +kernel

theorem rowCheck11806 : row11806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11806 := by decide +kernel

theorem rowEval11806 (x : Key → ℝ) : Integer.Sparse.eval row11806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck11806, Integer.Sparse.eval_collectBalanced, rawRowCheck11806]

theorem rawRowCheck11807 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1 = rawRow11807 := by decide +kernel

theorem rowCheck11807 : row11807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11807 := by decide +kernel

theorem rowEval11807 (x : Key → ℝ) : Integer.Sparse.eval row11807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11807, Integer.Sparse.eval_collectBalanced, rawRowCheck11807]

theorem rawRowCheck11808 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1 = rawRow11808 := by decide +kernel

theorem rowCheck11808 : row11808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11808 := by decide +kernel

theorem rowEval11808 (x : Key → ℝ) : Integer.Sparse.eval row11808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck11808, Integer.Sparse.eval_collectBalanced, rawRowCheck11808]

theorem rawRowCheck11809 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1 = rawRow11809 := by decide +kernel

theorem rowCheck11809 : row11809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11809 := by decide +kernel

theorem rowEval11809 (x : Key → ℝ) : Integer.Sparse.eval row11809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck11809, Integer.Sparse.eval_collectBalanced, rawRowCheck11809]

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

theorem rawRowCheck12211 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow12211 := by decide +kernel

theorem rowCheck12211 : row12211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12211 := by decide +kernel

theorem rowEval12211 (x : Key → ℝ) : Integer.Sparse.eval row12211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12211, Integer.Sparse.eval_collectBalanced, rawRowCheck12211]

theorem rawRowCheck12212 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow12212 := by decide +kernel

theorem rowCheck12212 : row12212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12212 := by decide +kernel

theorem rowEval12212 (x : Key → ℝ) : Integer.Sparse.eval row12212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12212, Integer.Sparse.eval_collectBalanced, rawRowCheck12212]

theorem rawRowCheck12213 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form1 = rawRow12213 := by decide +kernel

theorem rowCheck12213 : row12213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12213 := by decide +kernel

theorem rowEval12213 (x : Key → ℝ) : Integer.Sparse.eval row12213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12213, Integer.Sparse.eval_collectBalanced, rawRowCheck12213]

theorem rawRowCheck12214 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form1 = rawRow12214 := by decide +kernel

theorem rowCheck12214 : row12214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12214 := by decide +kernel

theorem rowEval12214 (x : Key → ℝ) : Integer.Sparse.eval row12214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12214, Integer.Sparse.eval_collectBalanced, rawRowCheck12214]

theorem rawRowCheck12215 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form1 = rawRow12215 := by decide +kernel

theorem rowCheck12215 : row12215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12215 := by decide +kernel

theorem rowEval12215 (x : Key → ℝ) : Integer.Sparse.eval row12215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12215, Integer.Sparse.eval_collectBalanced, rawRowCheck12215]

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

theorem entryCheck23_1 : entry23_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_1 k)) := by decide +kernel

theorem rowsSound23_1 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval11792 x
  · exact rowEval11793 x
  · exact rowEval11794 x
  · exact rowEval11795 x
  · exact rowEval11796 x
  · exact rowEval11797 x
  · exact rowEval11798 x
  · exact rowEval11799 x
  · exact rowEval11800 x
  · exact rowEval11801 x
  · exact rowEval11802 x
  · exact rowEval11803 x
  · exact rowEval11804 x
  · exact rowEval11805 x
  · exact rowEval11806 x
  · exact rowEval11807 x
  · exact rowEval11808 x
  · exact rowEval11809 x

theorem entryEval23_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_1 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck23_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_1]

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

theorem rawRowCheck12339 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form1 = rawRow12339 := by decide +kernel

theorem rowCheck12339 : row12339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12339 := by decide +kernel

theorem rowEval12339 (x : Key → ℝ) : Integer.Sparse.eval row12339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12339, Integer.Sparse.eval_collectBalanced, rawRowCheck12339]

theorem rawRowCheck12340 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form1 = rawRow12340 := by decide +kernel

theorem rowCheck12340 : row12340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12340 := by decide +kernel

theorem rowEval12340 (x : Key → ℝ) : Integer.Sparse.eval row12340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12340, Integer.Sparse.eval_collectBalanced, rawRowCheck12340]

theorem rawRowCheck12341 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form1 = rawRow12341 := by decide +kernel

theorem rowCheck12341 : row12341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12341 := by decide +kernel

theorem rowEval12341 (x : Key → ℝ) : Integer.Sparse.eval row12341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12341, Integer.Sparse.eval_collectBalanced, rawRowCheck12341]

theorem rawRowCheck12342 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form1 = rawRow12342 := by decide +kernel

theorem rowCheck12342 : row12342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12342 := by decide +kernel

theorem rowEval12342 (x : Key → ℝ) : Integer.Sparse.eval row12342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12342, Integer.Sparse.eval_collectBalanced, rawRowCheck12342]

theorem rawRowCheck12343 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form1 = rawRow12343 := by decide +kernel

theorem rowCheck12343 : row12343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12343 := by decide +kernel

theorem rowEval12343 (x : Key → ℝ) : Integer.Sparse.eval row12343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12343, Integer.Sparse.eval_collectBalanced, rawRowCheck12343]

theorem rawRowCheck12344 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form1 = rawRow12344 := by decide +kernel

theorem rowCheck12344 : row12344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12344 := by decide +kernel

theorem rowEval12344 (x : Key → ℝ) : Integer.Sparse.eval row12344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12344, Integer.Sparse.eval_collectBalanced, rawRowCheck12344]

theorem rawRowCheck12345 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form1 = rawRow12345 := by decide +kernel

theorem rowCheck12345 : row12345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12345 := by decide +kernel

theorem rowEval12345 (x : Key → ℝ) : Integer.Sparse.eval row12345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12345, Integer.Sparse.eval_collectBalanced, rawRowCheck12345]

theorem rawRowCheck12346 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form1 = rawRow12346 := by decide +kernel

theorem rowCheck12346 : row12346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12346 := by decide +kernel

theorem rowEval12346 (x : Key → ℝ) : Integer.Sparse.eval row12346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12346, Integer.Sparse.eval_collectBalanced, rawRowCheck12346]

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

theorem entryCheck24_1 : entry24_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_1 k)) := by decide +kernel

theorem rowsSound24_1 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12211 x
  · exact rowEval12212 x
  · exact rowEval12213 x
  · exact rowEval12214 x
  · exact rowEval12215 x

theorem entryEval24_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_1 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck24_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_1]

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

theorem entryCheck25_1 : entry25_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_1 k)) := by decide +kernel

theorem rowsSound25_1 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12339 x
  · exact rowEval12340 x
  · exact rowEval12341 x
  · exact rowEval12342 x
  · exact rowEval12343 x
  · exact rowEval12344 x
  · exact rowEval12345 x
  · exact rowEval12346 x

theorem entryEval25_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_1 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck25_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_1]

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

theorem rawRowCheck12563 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form1 = rawRow12563 := by decide +kernel

theorem rowCheck12563 : row12563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12563 := by decide +kernel

theorem rowEval12563 (x : Key → ℝ) : Integer.Sparse.eval row12563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12563, Integer.Sparse.eval_collectBalanced, rawRowCheck12563]

theorem rawRowCheck12564 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form1 = rawRow12564 := by decide +kernel

theorem rowCheck12564 : row12564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12564 := by decide +kernel

theorem rowEval12564 (x : Key → ℝ) : Integer.Sparse.eval row12564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12564, Integer.Sparse.eval_collectBalanced, rawRowCheck12564]

theorem rawRowCheck12565 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form1 = rawRow12565 := by decide +kernel

theorem rowCheck12565 : row12565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12565 := by decide +kernel

theorem rowEval12565 (x : Key → ℝ) : Integer.Sparse.eval row12565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12565, Integer.Sparse.eval_collectBalanced, rawRowCheck12565]

theorem rawRowCheck12566 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form1 = rawRow12566 := by decide +kernel

theorem rowCheck12566 : row12566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12566 := by decide +kernel

theorem rowEval12566 (x : Key → ℝ) : Integer.Sparse.eval row12566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12566, Integer.Sparse.eval_collectBalanced, rawRowCheck12566]

theorem rawRowCheck12567 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form1 = rawRow12567 := by decide +kernel

theorem rowCheck12567 : row12567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12567 := by decide +kernel

theorem rowEval12567 (x : Key → ℝ) : Integer.Sparse.eval row12567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12567, Integer.Sparse.eval_collectBalanced, rawRowCheck12567]

theorem rawRowCheck12568 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form1 = rawRow12568 := by decide +kernel

theorem rowCheck12568 : row12568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12568 := by decide +kernel

theorem rowEval12568 (x : Key → ℝ) : Integer.Sparse.eval row12568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12568, Integer.Sparse.eval_collectBalanced, rawRowCheck12568]

theorem rawRowCheck12569 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form1 = rawRow12569 := by decide +kernel

theorem rowCheck12569 : row12569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12569 := by decide +kernel

theorem rowEval12569 (x : Key → ℝ) : Integer.Sparse.eval row12569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12569, Integer.Sparse.eval_collectBalanced, rawRowCheck12569]

theorem rawRowCheck12570 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form1 = rawRow12570 := by decide +kernel

theorem rowCheck12570 : row12570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12570 := by decide +kernel

theorem rowEval12570 (x : Key → ℝ) : Integer.Sparse.eval row12570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12570, Integer.Sparse.eval_collectBalanced, rawRowCheck12570]

theorem rawRowCheck12571 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form1 = rawRow12571 := by decide +kernel

theorem rowCheck12571 : row12571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12571 := by decide +kernel

theorem rowEval12571 (x : Key → ℝ) : Integer.Sparse.eval row12571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12571, Integer.Sparse.eval_collectBalanced, rawRowCheck12571]

theorem rawRowCheck12572 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form1 = rawRow12572 := by decide +kernel

theorem rowCheck12572 : row12572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12572 := by decide +kernel

theorem rowEval12572 (x : Key → ℝ) : Integer.Sparse.eval row12572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12572, Integer.Sparse.eval_collectBalanced, rawRowCheck12572]

theorem rawRowCheck12573 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form1 = rawRow12573 := by decide +kernel

theorem rowCheck12573 : row12573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12573 := by decide +kernel

theorem rowEval12573 (x : Key → ℝ) : Integer.Sparse.eval row12573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12573, Integer.Sparse.eval_collectBalanced, rawRowCheck12573]

theorem rawRowCheck12574 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form1 = rawRow12574 := by decide +kernel

theorem rowCheck12574 : row12574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12574 := by decide +kernel

theorem rowEval12574 (x : Key → ℝ) : Integer.Sparse.eval row12574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12574, Integer.Sparse.eval_collectBalanced, rawRowCheck12574]

theorem rawRowCheck12575 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form1 = rawRow12575 := by decide +kernel

theorem rowCheck12575 : row12575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12575 := by decide +kernel

theorem rowEval12575 (x : Key → ℝ) : Integer.Sparse.eval row12575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12575, Integer.Sparse.eval_collectBalanced, rawRowCheck12575]

theorem rawRowCheck12576 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form1 = rawRow12576 := by decide +kernel

theorem rowCheck12576 : row12576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12576 := by decide +kernel

theorem rowEval12576 (x : Key → ℝ) : Integer.Sparse.eval row12576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12576, Integer.Sparse.eval_collectBalanced, rawRowCheck12576]

theorem rawRowCheck12577 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form1 = rawRow12577 := by decide +kernel

theorem rowCheck12577 : row12577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12577 := by decide +kernel

theorem rowEval12577 (x : Key → ℝ) : Integer.Sparse.eval row12577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12577, Integer.Sparse.eval_collectBalanced, rawRowCheck12577]

theorem rawRowCheck12578 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form1 = rawRow12578 := by decide +kernel

theorem rowCheck12578 : row12578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12578 := by decide +kernel

theorem rowEval12578 (x : Key → ℝ) : Integer.Sparse.eval row12578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12578, Integer.Sparse.eval_collectBalanced, rawRowCheck12578]

theorem rawRowCheck12579 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form1 = rawRow12579 := by decide +kernel

theorem rowCheck12579 : row12579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12579 := by decide +kernel

theorem rowEval12579 (x : Key → ℝ) : Integer.Sparse.eval row12579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12579, Integer.Sparse.eval_collectBalanced, rawRowCheck12579]

theorem rawRowCheck12580 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form1 = rawRow12580 := by decide +kernel

theorem rowCheck12580 : row12580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12580 := by decide +kernel

theorem rowEval12580 (x : Key → ℝ) : Integer.Sparse.eval row12580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12580, Integer.Sparse.eval_collectBalanced, rawRowCheck12580]

theorem rawRowCheck12581 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form1 = rawRow12581 := by decide +kernel

theorem rowCheck12581 : row12581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12581 := by decide +kernel

theorem rowEval12581 (x : Key → ℝ) : Integer.Sparse.eval row12581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12581, Integer.Sparse.eval_collectBalanced, rawRowCheck12581]

theorem rawRowCheck12582 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form1 = rawRow12582 := by decide +kernel

theorem rowCheck12582 : row12582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12582 := by decide +kernel

theorem rowEval12582 (x : Key → ℝ) : Integer.Sparse.eval row12582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12582, Integer.Sparse.eval_collectBalanced, rawRowCheck12582]

theorem rawRowCheck12583 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form1 = rawRow12583 := by decide +kernel

theorem rowCheck12583 : row12583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12583 := by decide +kernel

theorem rowEval12583 (x : Key → ℝ) : Integer.Sparse.eval row12583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12583, Integer.Sparse.eval_collectBalanced, rawRowCheck12583]

theorem rawRowCheck12584 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow12584 := by decide +kernel

theorem rowCheck12584 : row12584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12584 := by decide +kernel

theorem rowEval12584 (x : Key → ℝ) : Integer.Sparse.eval row12584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12584, Integer.Sparse.eval_collectBalanced, rawRowCheck12584]

theorem rawRowCheck12585 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow12585 := by decide +kernel

theorem rowCheck12585 : row12585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12585 := by decide +kernel

theorem rowEval12585 (x : Key → ℝ) : Integer.Sparse.eval row12585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12585, Integer.Sparse.eval_collectBalanced, rawRowCheck12585]

theorem rawRowCheck12586 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow12586 := by decide +kernel

theorem rowCheck12586 : row12586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12586 := by decide +kernel

theorem rowEval12586 (x : Key → ℝ) : Integer.Sparse.eval row12586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12586, Integer.Sparse.eval_collectBalanced, rawRowCheck12586]

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

theorem entryCheck26_1 : entry26_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_1 k)) := by decide +kernel

theorem rowsSound26_1 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12563 x
  · exact rowEval12564 x
  · exact rowEval12565 x
  · exact rowEval12566 x
  · exact rowEval12567 x
  · exact rowEval12568 x
  · exact rowEval12569 x
  · exact rowEval12570 x
  · exact rowEval12571 x
  · exact rowEval12572 x
  · exact rowEval12573 x
  · exact rowEval12574 x
  · exact rowEval12575 x
  · exact rowEval12576 x
  · exact rowEval12577 x
  · exact rowEval12578 x
  · exact rowEval12579 x
  · exact rowEval12580 x
  · exact rowEval12581 x
  · exact rowEval12582 x
  · exact rowEval12583 x
  · exact rowEval12584 x
  · exact rowEval12585 x
  · exact rowEval12586 x

theorem entryEval26_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_1 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck26_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_1]

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

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7510 x
  · exact rowEval7511 x
  · exact rowEval7512 x
  · exact rowEval7513 x
  · exact rowEval7514 x
  · exact rowEval7515 x
  · exact rowEval7516 x
  · exact rowEval7517 x
  · exact rowEval7518 x
  · exact rowEval7519 x
  · exact rowEval7520 x
  · exact rowEval7521 x
  · exact rowEval7522 x
  · exact rowEval7523 x
  · exact rowEval7524 x
  · exact rowEval7525 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

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

theorem rawRowCheck7795 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7795 := by decide +kernel

theorem rowCheck7795 : row7795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7795 := by decide +kernel

theorem rowEval7795 (x : Key → ℝ) : Integer.Sparse.eval row7795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7795, Integer.Sparse.eval_collectBalanced, rawRowCheck7795]

theorem rawRowCheck7796 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7796 := by decide +kernel

theorem rowCheck7796 : row7796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7796 := by decide +kernel

theorem rowEval7796 (x : Key → ℝ) : Integer.Sparse.eval row7796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7796, Integer.Sparse.eval_collectBalanced, rawRowCheck7796]

theorem rawRowCheck7797 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7797 := by decide +kernel

theorem rowCheck7797 : row7797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7797 := by decide +kernel

theorem rowEval7797 (x : Key → ℝ) : Integer.Sparse.eval row7797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7797, Integer.Sparse.eval_collectBalanced, rawRowCheck7797]

theorem rawRowCheck7798 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7798 := by decide +kernel

theorem rowCheck7798 : row7798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7798 := by decide +kernel

theorem rowEval7798 (x : Key → ℝ) : Integer.Sparse.eval row7798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7798, Integer.Sparse.eval_collectBalanced, rawRowCheck7798]

theorem rawRowCheck7799 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7799 := by decide +kernel

theorem rowCheck7799 : row7799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7799 := by decide +kernel

theorem rowEval7799 (x : Key → ℝ) : Integer.Sparse.eval row7799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7799, Integer.Sparse.eval_collectBalanced, rawRowCheck7799]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block3.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form5.terms k).tag (GramFunctions.Block3.form5.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7610 x
  · exact rowEval7611 x
  · exact rowEval7612 x
  · exact rowEval7613 x
  · exact rowEval7614 x
  · exact rowEval7615 x
  · exact rowEval7616 x
  · exact rowEval7617 x
  · exact rowEval7618 x
  · exact rowEval7619 x
  · exact rowEval7620 x
  · exact rowEval7621 x
  · exact rowEval7622 x
  · exact rowEval7623 x
  · exact rowEval7624 x
  · exact rowEval7625 x
  · exact rowEval7626 x
  · exact rowEval7627 x
  · exact rowEval7628 x
  · exact rowEval7629 x
  · exact rowEval7630 x
  · exact rowEval7631 x
  · exact rowEval7632 x
  · exact rowEval7633 x
  · exact rowEval7634 x
  · exact rowEval7635 x
  · exact rowEval7636 x
  · exact rowEval7637 x
  · exact rowEval7638 x
  · exact rowEval7639 x
  · exact rowEval7640 x
  · exact rowEval7641 x
  · exact rowEval7642 x
  · exact rowEval7643 x
  · exact rowEval7644 x
  · exact rowEval7645 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block3.form5.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form5 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck7837 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7837 := by decide +kernel

theorem rowCheck7837 : row7837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7837 := by decide +kernel

theorem rowEval7837 (x : Key → ℝ) : Integer.Sparse.eval row7837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7837, Integer.Sparse.eval_collectBalanced, rawRowCheck7837]

theorem rawRowCheck7838 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7838 := by decide +kernel

theorem rowCheck7838 : row7838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7838 := by decide +kernel

theorem rowEval7838 (x : Key → ℝ) : Integer.Sparse.eval row7838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7838, Integer.Sparse.eval_collectBalanced, rawRowCheck7838]

theorem rawRowCheck7839 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7839 := by decide +kernel

theorem rowCheck7839 : row7839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7839 := by decide +kernel

theorem rowEval7839 (x : Key → ℝ) : Integer.Sparse.eval row7839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7839, Integer.Sparse.eval_collectBalanced, rawRowCheck7839]

theorem rawRowCheck7840 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form1 = rawRow7840 := by decide +kernel

theorem rowCheck7840 : row7840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7840 := by decide +kernel

theorem rowEval7840 (x : Key → ℝ) : Integer.Sparse.eval row7840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7840, Integer.Sparse.eval_collectBalanced, rawRowCheck7840]

theorem rawRowCheck7841 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form1 = rawRow7841 := by decide +kernel

theorem rowCheck7841 : row7841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7841 := by decide +kernel

theorem rowEval7841 (x : Key → ℝ) : Integer.Sparse.eval row7841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7841, Integer.Sparse.eval_collectBalanced, rawRowCheck7841]

theorem rawRowCheck7842 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form1 = rawRow7842 := by decide +kernel

theorem rowCheck7842 : row7842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7842 := by decide +kernel

theorem rowEval7842 (x : Key → ℝ) : Integer.Sparse.eval row7842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7842, Integer.Sparse.eval_collectBalanced, rawRowCheck7842]

theorem rawRowCheck7843 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form1 = rawRow7843 := by decide +kernel

theorem rowCheck7843 : row7843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7843 := by decide +kernel

theorem rowEval7843 (x : Key → ℝ) : Integer.Sparse.eval row7843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7843, Integer.Sparse.eval_collectBalanced, rawRowCheck7843]

theorem rawRowCheck7844 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form1 = rawRow7844 := by decide +kernel

theorem rowCheck7844 : row7844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7844 := by decide +kernel

theorem rowEval7844 (x : Key → ℝ) : Integer.Sparse.eval row7844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7844, Integer.Sparse.eval_collectBalanced, rawRowCheck7844]

theorem rawRowCheck7845 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form1 = rawRow7845 := by decide +kernel

theorem rowCheck7845 : row7845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7845 := by decide +kernel

theorem rowEval7845 (x : Key → ℝ) : Integer.Sparse.eval row7845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7845, Integer.Sparse.eval_collectBalanced, rawRowCheck7845]

theorem rawRowCheck7846 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow7846 := by decide +kernel

theorem rowCheck7846 : row7846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7846 := by decide +kernel

theorem rowEval7846 (x : Key → ℝ) : Integer.Sparse.eval row7846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7846, Integer.Sparse.eval_collectBalanced, rawRowCheck7846]

theorem rawRowCheck7847 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow7847 := by decide +kernel

theorem rowCheck7847 : row7847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7847 := by decide +kernel

theorem rowEval7847 (x : Key → ℝ) : Integer.Sparse.eval row7847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7847, Integer.Sparse.eval_collectBalanced, rawRowCheck7847]

theorem rawRowCheck7848 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow7848 := by decide +kernel

theorem rowCheck7848 : row7848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7848 := by decide +kernel

theorem rowEval7848 (x : Key → ℝ) : Integer.Sparse.eval row7848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7848, Integer.Sparse.eval_collectBalanced, rawRowCheck7848]

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

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7795 x
  · exact rowEval7796 x
  · exact rowEval7797 x
  · exact rowEval7798 x
  · exact rowEval7799 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7981 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7981 := by decide +kernel

theorem rowCheck7981 : row7981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7981 := by decide +kernel

theorem rowEval7981 (x : Key → ℝ) : Integer.Sparse.eval row7981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7981, Integer.Sparse.eval_collectBalanced, rawRowCheck7981]

theorem rawRowCheck7982 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7982 := by decide +kernel

theorem rowCheck7982 : row7982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7982 := by decide +kernel

theorem rowEval7982 (x : Key → ℝ) : Integer.Sparse.eval row7982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7982, Integer.Sparse.eval_collectBalanced, rawRowCheck7982]

theorem rawRowCheck7983 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7983 := by decide +kernel

theorem rowCheck7983 : row7983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7983 := by decide +kernel

theorem rowEval7983 (x : Key → ℝ) : Integer.Sparse.eval row7983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7983, Integer.Sparse.eval_collectBalanced, rawRowCheck7983]

theorem rawRowCheck7984 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form1 = rawRow7984 := by decide +kernel

theorem rowCheck7984 : row7984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7984 := by decide +kernel

theorem rowEval7984 (x : Key → ℝ) : Integer.Sparse.eval row7984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7984, Integer.Sparse.eval_collectBalanced, rawRowCheck7984]

theorem rawRowCheck7985 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form1 = rawRow7985 := by decide +kernel

theorem rowCheck7985 : row7985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7985 := by decide +kernel

theorem rowEval7985 (x : Key → ℝ) : Integer.Sparse.eval row7985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7985, Integer.Sparse.eval_collectBalanced, rawRowCheck7985]

theorem rawRowCheck7986 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form1 = rawRow7986 := by decide +kernel

theorem rowCheck7986 : row7986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7986 := by decide +kernel

theorem rowEval7986 (x : Key → ℝ) : Integer.Sparse.eval row7986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7986, Integer.Sparse.eval_collectBalanced, rawRowCheck7986]

theorem rawRowCheck7987 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form1 = rawRow7987 := by decide +kernel

theorem rowCheck7987 : row7987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7987 := by decide +kernel

theorem rowEval7987 (x : Key → ℝ) : Integer.Sparse.eval row7987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7987, Integer.Sparse.eval_collectBalanced, rawRowCheck7987]

theorem rawRowCheck7988 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form1 = rawRow7988 := by decide +kernel

theorem rowCheck7988 : row7988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7988 := by decide +kernel

theorem rowEval7988 (x : Key → ℝ) : Integer.Sparse.eval row7988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7988, Integer.Sparse.eval_collectBalanced, rawRowCheck7988]

theorem rawRowCheck7989 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form1 = rawRow7989 := by decide +kernel

theorem rowCheck7989 : row7989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7989 := by decide +kernel

theorem rowEval7989 (x : Key → ℝ) : Integer.Sparse.eval row7989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7989, Integer.Sparse.eval_collectBalanced, rawRowCheck7989]

theorem rawRowCheck7990 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7990 := by decide +kernel

theorem rowCheck7990 : row7990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7990 := by decide +kernel

theorem rowEval7990 (x : Key → ℝ) : Integer.Sparse.eval row7990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7990, Integer.Sparse.eval_collectBalanced, rawRowCheck7990]

theorem rawRowCheck7991 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7991 := by decide +kernel

theorem rowCheck7991 : row7991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7991 := by decide +kernel

theorem rowEval7991 (x : Key → ℝ) : Integer.Sparse.eval row7991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7991, Integer.Sparse.eval_collectBalanced, rawRowCheck7991]

theorem rawRowCheck7992 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7992 := by decide +kernel

theorem rowCheck7992 : row7992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7992 := by decide +kernel

theorem rowEval7992 (x : Key → ℝ) : Integer.Sparse.eval row7992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7992, Integer.Sparse.eval_collectBalanced, rawRowCheck7992]

theorem rawRowCheck7993 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form1 = rawRow7993 := by decide +kernel

theorem rowCheck7993 : row7993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7993 := by decide +kernel

theorem rowEval7993 (x : Key → ℝ) : Integer.Sparse.eval row7993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7993, Integer.Sparse.eval_collectBalanced, rawRowCheck7993]

theorem rawRowCheck7994 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form1 = rawRow7994 := by decide +kernel

theorem rowCheck7994 : row7994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7994 := by decide +kernel

theorem rowEval7994 (x : Key → ℝ) : Integer.Sparse.eval row7994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7994, Integer.Sparse.eval_collectBalanced, rawRowCheck7994]

theorem rawRowCheck7995 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form1 = rawRow7995 := by decide +kernel

theorem rowCheck7995 : row7995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7995 := by decide +kernel

theorem rowEval7995 (x : Key → ℝ) : Integer.Sparse.eval row7995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7995, Integer.Sparse.eval_collectBalanced, rawRowCheck7995]

theorem rawRowCheck7996 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form1 = rawRow7996 := by decide +kernel

theorem rowCheck7996 : row7996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7996 := by decide +kernel

theorem rowEval7996 (x : Key → ℝ) : Integer.Sparse.eval row7996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7996, Integer.Sparse.eval_collectBalanced, rawRowCheck7996]

theorem rawRowCheck7997 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form1 = rawRow7997 := by decide +kernel

theorem rowCheck7997 : row7997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7997 := by decide +kernel

theorem rowEval7997 (x : Key → ℝ) : Integer.Sparse.eval row7997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7997, Integer.Sparse.eval_collectBalanced, rawRowCheck7997]

theorem rawRowCheck7998 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form1 = rawRow7998 := by decide +kernel

theorem rowCheck7998 : row7998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7998 := by decide +kernel

theorem rowEval7998 (x : Key → ℝ) : Integer.Sparse.eval row7998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7998, Integer.Sparse.eval_collectBalanced, rawRowCheck7998]

theorem rawRowCheck7999 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form1 = rawRow7999 := by decide +kernel

theorem rowCheck7999 : row7999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7999 := by decide +kernel

theorem rowEval7999 (x : Key → ℝ) : Integer.Sparse.eval row7999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7999, Integer.Sparse.eval_collectBalanced, rawRowCheck7999]

theorem rawRowCheck8000 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form1 = rawRow8000 := by decide +kernel

theorem rowCheck8000 : row8000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8000 := by decide +kernel

theorem rowEval8000 (x : Key → ℝ) : Integer.Sparse.eval row8000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8000, Integer.Sparse.eval_collectBalanced, rawRowCheck8000]

theorem rawRowCheck8001 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form1 = rawRow8001 := by decide +kernel

theorem rowCheck8001 : row8001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8001 := by decide +kernel

theorem rowEval8001 (x : Key → ℝ) : Integer.Sparse.eval row8001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8001, Integer.Sparse.eval_collectBalanced, rawRowCheck8001]

theorem rawRowCheck8002 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form1 = rawRow8002 := by decide +kernel

theorem rowCheck8002 : row8002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8002 := by decide +kernel

theorem rowEval8002 (x : Key → ℝ) : Integer.Sparse.eval row8002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8002, Integer.Sparse.eval_collectBalanced, rawRowCheck8002]

theorem rawRowCheck8003 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form1 = rawRow8003 := by decide +kernel

theorem rowCheck8003 : row8003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8003 := by decide +kernel

theorem rowEval8003 (x : Key → ℝ) : Integer.Sparse.eval row8003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8003, Integer.Sparse.eval_collectBalanced, rawRowCheck8003]

theorem rawRowCheck8004 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form1 = rawRow8004 := by decide +kernel

theorem rowCheck8004 : row8004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8004 := by decide +kernel

theorem rowEval8004 (x : Key → ℝ) : Integer.Sparse.eval row8004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8004, Integer.Sparse.eval_collectBalanced, rawRowCheck8004]

theorem rawRowCheck8005 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form1 = rawRow8005 := by decide +kernel

theorem rowCheck8005 : row8005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8005 := by decide +kernel

theorem rowEval8005 (x : Key → ℝ) : Integer.Sparse.eval row8005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8005, Integer.Sparse.eval_collectBalanced, rawRowCheck8005]

theorem rawRowCheck8006 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form1 = rawRow8006 := by decide +kernel

theorem rowCheck8006 : row8006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8006 := by decide +kernel

theorem rowEval8006 (x : Key → ℝ) : Integer.Sparse.eval row8006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8006, Integer.Sparse.eval_collectBalanced, rawRowCheck8006]

theorem rawRowCheck8007 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form1 = rawRow8007 := by decide +kernel

theorem rowCheck8007 : row8007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8007 := by decide +kernel

theorem rowEval8007 (x : Key → ℝ) : Integer.Sparse.eval row8007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8007, Integer.Sparse.eval_collectBalanced, rawRowCheck8007]

theorem rawRowCheck8008 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form1 = rawRow8008 := by decide +kernel

theorem rowCheck8008 : row8008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8008 := by decide +kernel

theorem rowEval8008 (x : Key → ℝ) : Integer.Sparse.eval row8008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8008, Integer.Sparse.eval_collectBalanced, rawRowCheck8008]

theorem rawRowCheck8009 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form1 = rawRow8009 := by decide +kernel

theorem rowCheck8009 : row8009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8009 := by decide +kernel

theorem rowEval8009 (x : Key → ℝ) : Integer.Sparse.eval row8009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8009, Integer.Sparse.eval_collectBalanced, rawRowCheck8009]

theorem rawRowCheck8010 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form1 = rawRow8010 := by decide +kernel

theorem rowCheck8010 : row8010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8010 := by decide +kernel

theorem rowEval8010 (x : Key → ℝ) : Integer.Sparse.eval row8010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8010, Integer.Sparse.eval_collectBalanced, rawRowCheck8010]

theorem rawRowCheck8011 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form1 = rawRow8011 := by decide +kernel

theorem rowCheck8011 : row8011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8011 := by decide +kernel

theorem rowEval8011 (x : Key → ℝ) : Integer.Sparse.eval row8011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8011, Integer.Sparse.eval_collectBalanced, rawRowCheck8011]

theorem rawRowCheck8012 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form1 = rawRow8012 := by decide +kernel

theorem rowCheck8012 : row8012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8012 := by decide +kernel

theorem rowEval8012 (x : Key → ℝ) : Integer.Sparse.eval row8012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8012, Integer.Sparse.eval_collectBalanced, rawRowCheck8012]

theorem rawRowCheck8013 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form1 = rawRow8013 := by decide +kernel

theorem rowCheck8013 : row8013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8013 := by decide +kernel

theorem rowEval8013 (x : Key → ℝ) : Integer.Sparse.eval row8013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8013, Integer.Sparse.eval_collectBalanced, rawRowCheck8013]

theorem rawRowCheck8014 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form1 = rawRow8014 := by decide +kernel

theorem rowCheck8014 : row8014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8014 := by decide +kernel

theorem rowEval8014 (x : Key → ℝ) : Integer.Sparse.eval row8014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8014, Integer.Sparse.eval_collectBalanced, rawRowCheck8014]

theorem rawRowCheck8015 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form1 = rawRow8015 := by decide +kernel

theorem rowCheck8015 : row8015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8015 := by decide +kernel

theorem rowEval8015 (x : Key → ℝ) : Integer.Sparse.eval row8015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8015, Integer.Sparse.eval_collectBalanced, rawRowCheck8015]

theorem rawRowCheck8016 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form1 = rawRow8016 := by decide +kernel

theorem rowCheck8016 : row8016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8016 := by decide +kernel

theorem rowEval8016 (x : Key → ℝ) : Integer.Sparse.eval row8016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8016, Integer.Sparse.eval_collectBalanced, rawRowCheck8016]

end MUB6.Certificate.GramRows

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

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7837 x
  · exact rowEval7838 x
  · exact rowEval7839 x
  · exact rowEval7840 x
  · exact rowEval7841 x
  · exact rowEval7842 x
  · exact rowEval7843 x
  · exact rowEval7844 x
  · exact rowEval7845 x
  · exact rowEval7846 x
  · exact rowEval7847 x
  · exact rowEval7848 x
  · exact rowEval7610 x
  · exact rowEval7611 x
  · exact rowEval7612 x
  · exact rowEval7613 x
  · exact rowEval7614 x
  · exact rowEval7615 x
  · exact rowEval7616 x
  · exact rowEval7617 x
  · exact rowEval7618 x
  · exact rowEval7619 x
  · exact rowEval7620 x
  · exact rowEval7621 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7981 x
  · exact rowEval7982 x
  · exact rowEval7983 x
  · exact rowEval7984 x
  · exact rowEval7985 x
  · exact rowEval7986 x
  · exact rowEval7987 x
  · exact rowEval7988 x
  · exact rowEval7989 x
  · exact rowEval7990 x
  · exact rowEval7991 x
  · exact rowEval7992 x
  · exact rowEval7993 x
  · exact rowEval7994 x
  · exact rowEval7995 x
  · exact rowEval7996 x
  · exact rowEval7997 x
  · exact rowEval7998 x
  · exact rowEval7999 x
  · exact rowEval8000 x
  · exact rowEval8001 x
  · exact rowEval8002 x
  · exact rowEval8003 x
  · exact rowEval8004 x
  · exact rowEval8005 x
  · exact rowEval8006 x
  · exact rowEval8007 x
  · exact rowEval8008 x
  · exact rowEval8009 x
  · exact rowEval8010 x
  · exact rowEval8011 x
  · exact rowEval8012 x
  · exact rowEval8013 x
  · exact rowEval8014 x
  · exact rowEval8015 x
  · exact rowEval8016 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

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

theorem entryEvalRow1_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 1).mixedGram (GramFunctions.Block3.forms j) B := by
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
  · exact (entryEval6_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_1 B hB).trans
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
  · exact (entryEval22_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e_oai
