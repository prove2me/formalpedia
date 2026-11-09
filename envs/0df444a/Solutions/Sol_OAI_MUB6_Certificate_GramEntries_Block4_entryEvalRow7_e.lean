-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:53:26.130244+00:00
-- url     : https://prove2.me/submissions/2c74394f-ab57-4122-b783-77a52969cc65

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E034
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval10_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_7_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14080 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form7 = rawRow14080 := by decide +kernel

theorem rowCheck14080 : row14080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14080 := by decide +kernel

theorem rowEval14080 (x : Key → ℝ) : Integer.Sparse.eval row14080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14080, Integer.Sparse.eval_collectBalanced, rawRowCheck14080]

theorem rawRowCheck14081 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14081 := by decide +kernel

theorem rowCheck14081 : row14081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14081 := by decide +kernel

theorem rowEval14081 (x : Key → ℝ) : Integer.Sparse.eval row14081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14081, Integer.Sparse.eval_collectBalanced, rawRowCheck14081]

theorem rawRowCheck14082 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form7 = rawRow14082 := by decide +kernel

theorem rowCheck14082 : row14082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14082 := by decide +kernel

theorem rowEval14082 (x : Key → ℝ) : Integer.Sparse.eval row14082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14082, Integer.Sparse.eval_collectBalanced, rawRowCheck14082]

theorem rawRowCheck14083 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form7 = rawRow14083 := by decide +kernel

theorem rowCheck14083 : row14083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14083 := by decide +kernel

theorem rowEval14083 (x : Key → ℝ) : Integer.Sparse.eval row14083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14083, Integer.Sparse.eval_collectBalanced, rawRowCheck14083]

theorem rawRowCheck14084 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form7 = rawRow14084 := by decide +kernel

theorem rowCheck14084 : row14084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14084 := by decide +kernel

theorem rowEval14084 (x : Key → ℝ) : Integer.Sparse.eval row14084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14084, Integer.Sparse.eval_collectBalanced, rawRowCheck14084]

theorem rawRowCheck14175 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form7 = rawRow14175 := by decide +kernel

theorem rowCheck14175 : row14175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14175 := by decide +kernel

theorem rowEval14175 (x : Key → ℝ) : Integer.Sparse.eval row14175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14175, Integer.Sparse.eval_collectBalanced, rawRowCheck14175]

theorem rawRowCheck14176 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form7 = rawRow14176 := by decide +kernel

theorem rowCheck14176 : row14176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14176 := by decide +kernel

theorem rowEval14176 (x : Key → ℝ) : Integer.Sparse.eval row14176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14176, Integer.Sparse.eval_collectBalanced, rawRowCheck14176]

theorem rawRowCheck14177 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form7 = rawRow14177 := by decide +kernel

theorem rowCheck14177 : row14177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14177 := by decide +kernel

theorem rowEval14177 (x : Key → ℝ) : Integer.Sparse.eval row14177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14177, Integer.Sparse.eval_collectBalanced, rawRowCheck14177]

theorem rawRowCheck14178 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form7 = rawRow14178 := by decide +kernel

theorem rowCheck14178 : row14178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14178 := by decide +kernel

theorem rowEval14178 (x : Key → ℝ) : Integer.Sparse.eval row14178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14178, Integer.Sparse.eval_collectBalanced, rawRowCheck14178]

theorem rawRowCheck14179 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form7 = rawRow14179 := by decide +kernel

theorem rowCheck14179 : row14179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14179 := by decide +kernel

theorem rowEval14179 (x : Key → ℝ) : Integer.Sparse.eval row14179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14179, Integer.Sparse.eval_collectBalanced, rawRowCheck14179]

theorem rawRowCheck14180 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form7 = rawRow14180 := by decide +kernel

theorem rowCheck14180 : row14180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14180 := by decide +kernel

theorem rowEval14180 (x : Key → ℝ) : Integer.Sparse.eval row14180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14180, Integer.Sparse.eval_collectBalanced, rawRowCheck14180]

theorem rawRowCheck14181 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow14181 := by decide +kernel

theorem rowCheck14181 : row14181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14181 := by decide +kernel

theorem rowEval14181 (x : Key → ℝ) : Integer.Sparse.eval row14181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14181, Integer.Sparse.eval_collectBalanced, rawRowCheck14181]

theorem rawRowCheck14182 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow14182 := by decide +kernel

theorem rowCheck14182 : row14182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14182 := by decide +kernel

theorem rowEval14182 (x : Key → ℝ) : Integer.Sparse.eval row14182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14182, Integer.Sparse.eval_collectBalanced, rawRowCheck14182]

theorem rawRowCheck14183 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow14183 := by decide +kernel

theorem rowCheck14183 : row14183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14183 := by decide +kernel

theorem rowEval14183 (x : Key → ℝ) : Integer.Sparse.eval row14183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14183, Integer.Sparse.eval_collectBalanced, rawRowCheck14183]

theorem rawRowCheck14184 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow14184 := by decide +kernel

theorem rowCheck14184 : row14184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14184 := by decide +kernel

theorem rowEval14184 (x : Key → ℝ) : Integer.Sparse.eval row14184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14184, Integer.Sparse.eval_collectBalanced, rawRowCheck14184]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14741 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form7 = rawRow14741 := by decide +kernel

theorem rowCheck14741 : row14741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14741 := by decide +kernel

theorem rowEval14741 (x : Key → ℝ) : Integer.Sparse.eval row14741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14741, Integer.Sparse.eval_collectBalanced, rawRowCheck14741]

theorem rawRowCheck14742 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form7 = rawRow14742 := by decide +kernel

theorem rowCheck14742 : row14742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14742 := by decide +kernel

theorem rowEval14742 (x : Key → ℝ) : Integer.Sparse.eval row14742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14742, Integer.Sparse.eval_collectBalanced, rawRowCheck14742]

theorem rawRowCheck14743 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form7 = rawRow14743 := by decide +kernel

theorem rowCheck14743 : row14743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14743 := by decide +kernel

theorem rowEval14743 (x : Key → ℝ) : Integer.Sparse.eval row14743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14743, Integer.Sparse.eval_collectBalanced, rawRowCheck14743]

theorem rawRowCheck14744 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14744 := by decide +kernel

theorem rowCheck14744 : row14744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14744 := by decide +kernel

theorem rowEval14744 (x : Key → ℝ) : Integer.Sparse.eval row14744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14744, Integer.Sparse.eval_collectBalanced, rawRowCheck14744]

theorem rawRowCheck14745 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form7 = rawRow14745 := by decide +kernel

theorem rowCheck14745 : row14745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14745 := by decide +kernel

theorem rowEval14745 (x : Key → ℝ) : Integer.Sparse.eval row14745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14745, Integer.Sparse.eval_collectBalanced, rawRowCheck14745]

theorem rawRowCheck14746 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form7 = rawRow14746 := by decide +kernel

theorem rowCheck14746 : row14746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14746 := by decide +kernel

theorem rowEval14746 (x : Key → ℝ) : Integer.Sparse.eval row14746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14746, Integer.Sparse.eval_collectBalanced, rawRowCheck14746]

theorem rawRowCheck14747 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form7 = rawRow14747 := by decide +kernel

theorem rowCheck14747 : row14747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14747 := by decide +kernel

theorem rowEval14747 (x : Key → ℝ) : Integer.Sparse.eval row14747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14747, Integer.Sparse.eval_collectBalanced, rawRowCheck14747]

theorem rawRowCheck14748 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form7 = rawRow14748 := by decide +kernel

theorem rowCheck14748 : row14748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14748 := by decide +kernel

theorem rowEval14748 (x : Key → ℝ) : Integer.Sparse.eval row14748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14748, Integer.Sparse.eval_collectBalanced, rawRowCheck14748]

theorem rawRowCheck14749 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form7 = rawRow14749 := by decide +kernel

theorem rowCheck14749 : row14749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14749 := by decide +kernel

theorem rowEval14749 (x : Key → ℝ) : Integer.Sparse.eval row14749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14749, Integer.Sparse.eval_collectBalanced, rawRowCheck14749]

theorem rawRowCheck14750 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form7 = rawRow14750 := by decide +kernel

theorem rowCheck14750 : row14750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14750 := by decide +kernel

theorem rowEval14750 (x : Key → ℝ) : Integer.Sparse.eval row14750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14750, Integer.Sparse.eval_collectBalanced, rawRowCheck14750]

theorem rawRowCheck14751 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form7 = rawRow14751 := by decide +kernel

theorem rowCheck14751 : row14751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14751 := by decide +kernel

theorem rowEval14751 (x : Key → ℝ) : Integer.Sparse.eval row14751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14751, Integer.Sparse.eval_collectBalanced, rawRowCheck14751]

theorem rawRowCheck14752 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form7 = rawRow14752 := by decide +kernel

theorem rowCheck14752 : row14752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14752 := by decide +kernel

theorem rowEval14752 (x : Key → ℝ) : Integer.Sparse.eval row14752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14752, Integer.Sparse.eval_collectBalanced, rawRowCheck14752]

theorem rawRowCheck14753 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form7 = rawRow14753 := by decide +kernel

theorem rowCheck14753 : row14753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14753 := by decide +kernel

theorem rowEval14753 (x : Key → ℝ) : Integer.Sparse.eval row14753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14753, Integer.Sparse.eval_collectBalanced, rawRowCheck14753]

theorem rawRowCheck14754 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form7 = rawRow14754 := by decide +kernel

theorem rowCheck14754 : row14754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14754 := by decide +kernel

theorem rowEval14754 (x : Key → ℝ) : Integer.Sparse.eval row14754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14754, Integer.Sparse.eval_collectBalanced, rawRowCheck14754]

theorem rawRowCheck14755 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form7 = rawRow14755 := by decide +kernel

theorem rowCheck14755 : row14755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14755 := by decide +kernel

theorem rowEval14755 (x : Key → ℝ) : Integer.Sparse.eval row14755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14755, Integer.Sparse.eval_collectBalanced, rawRowCheck14755]

theorem rawRowCheck14756 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form7 = rawRow14756 := by decide +kernel

theorem rowCheck14756 : row14756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14756 := by decide +kernel

theorem rowEval14756 (x : Key → ℝ) : Integer.Sparse.eval row14756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14756, Integer.Sparse.eval_collectBalanced, rawRowCheck14756]

theorem rawRowCheck14757 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14757 := by decide +kernel

theorem rowCheck14757 : row14757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14757 := by decide +kernel

theorem rowEval14757 (x : Key → ℝ) : Integer.Sparse.eval row14757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14757, Integer.Sparse.eval_collectBalanced, rawRowCheck14757]

theorem rawRowCheck14758 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form7 = rawRow14758 := by decide +kernel

theorem rowCheck14758 : row14758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14758 := by decide +kernel

theorem rowEval14758 (x : Key → ℝ) : Integer.Sparse.eval row14758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14758, Integer.Sparse.eval_collectBalanced, rawRowCheck14758]

theorem rawRowCheck14759 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form7 = rawRow14759 := by decide +kernel

theorem rowCheck14759 : row14759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14759 := by decide +kernel

theorem rowEval14759 (x : Key → ℝ) : Integer.Sparse.eval row14759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14759, Integer.Sparse.eval_collectBalanced, rawRowCheck14759]

theorem rawRowCheck14760 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form7 = rawRow14760 := by decide +kernel

theorem rowCheck14760 : row14760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14760 := by decide +kernel

theorem rowEval14760 (x : Key → ℝ) : Integer.Sparse.eval row14760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14760, Integer.Sparse.eval_collectBalanced, rawRowCheck14760]

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

theorem entryCheck11_7 : entry11_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_7 k)) := by decide +kernel

theorem rowsSound11_7 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval14741 x
  · exact rowEval14742 x
  · exact rowEval14743 x
  · exact rowEval14744 x
  · exact rowEval14745 x
  · exact rowEval14746 x
  · exact rowEval14747 x
  · exact rowEval14748 x
  · exact rowEval14749 x
  · exact rowEval14750 x
  · exact rowEval14751 x
  · exact rowEval14752 x
  · exact rowEval14753 x
  · exact rowEval14754 x
  · exact rowEval14755 x
  · exact rowEval14756 x
  · exact rowEval14757 x
  · exact rowEval14758 x
  · exact rowEval14759 x
  · exact rowEval14760 x

theorem entryEval11_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_7 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck11_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_7]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck15015 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form7 = rawRow15015 := by decide +kernel

theorem rowCheck15015 : row15015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15015 := by decide +kernel

theorem rowEval15015 (x : Key → ℝ) : Integer.Sparse.eval row15015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15015, Integer.Sparse.eval_collectBalanced, rawRowCheck15015]

theorem rawRowCheck15016 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form7 = rawRow15016 := by decide +kernel

theorem rowCheck15016 : row15016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15016 := by decide +kernel

theorem rowEval15016 (x : Key → ℝ) : Integer.Sparse.eval row15016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15016, Integer.Sparse.eval_collectBalanced, rawRowCheck15016]

theorem rawRowCheck15017 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form7 = rawRow15017 := by decide +kernel

theorem rowCheck15017 : row15017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15017 := by decide +kernel

theorem rowEval15017 (x : Key → ℝ) : Integer.Sparse.eval row15017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15017, Integer.Sparse.eval_collectBalanced, rawRowCheck15017]

theorem rawRowCheck15018 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form7 = rawRow15018 := by decide +kernel

theorem rowCheck15018 : row15018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15018 := by decide +kernel

theorem rowEval15018 (x : Key → ℝ) : Integer.Sparse.eval row15018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15018, Integer.Sparse.eval_collectBalanced, rawRowCheck15018]

theorem rawRowCheck15019 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form7 = rawRow15019 := by decide +kernel

theorem rowCheck15019 : row15019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15019 := by decide +kernel

theorem rowEval15019 (x : Key → ℝ) : Integer.Sparse.eval row15019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15019, Integer.Sparse.eval_collectBalanced, rawRowCheck15019]

theorem rawRowCheck15020 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form7 = rawRow15020 := by decide +kernel

theorem rowCheck15020 : row15020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15020 := by decide +kernel

theorem rowEval15020 (x : Key → ℝ) : Integer.Sparse.eval row15020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15020, Integer.Sparse.eval_collectBalanced, rawRowCheck15020]

theorem rawRowCheck15021 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form7 = rawRow15021 := by decide +kernel

theorem rowCheck15021 : row15021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15021 := by decide +kernel

theorem rowEval15021 (x : Key → ℝ) : Integer.Sparse.eval row15021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15021, Integer.Sparse.eval_collectBalanced, rawRowCheck15021]

theorem rawRowCheck15022 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form7 = rawRow15022 := by decide +kernel

theorem rowCheck15022 : row15022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15022 := by decide +kernel

theorem rowEval15022 (x : Key → ℝ) : Integer.Sparse.eval row15022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15022, Integer.Sparse.eval_collectBalanced, rawRowCheck15022]

theorem rawRowCheck15023 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form7 = rawRow15023 := by decide +kernel

theorem rowCheck15023 : row15023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15023 := by decide +kernel

theorem rowEval15023 (x : Key → ℝ) : Integer.Sparse.eval row15023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15023, Integer.Sparse.eval_collectBalanced, rawRowCheck15023]

theorem rawRowCheck15024 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form7 = rawRow15024 := by decide +kernel

theorem rowCheck15024 : row15024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15024 := by decide +kernel

theorem rowEval15024 (x : Key → ℝ) : Integer.Sparse.eval row15024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15024, Integer.Sparse.eval_collectBalanced, rawRowCheck15024]

theorem rawRowCheck15025 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form7 = rawRow15025 := by decide +kernel

theorem rowCheck15025 : row15025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15025 := by decide +kernel

theorem rowEval15025 (x : Key → ℝ) : Integer.Sparse.eval row15025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15025, Integer.Sparse.eval_collectBalanced, rawRowCheck15025]

theorem rawRowCheck15026 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form7 = rawRow15026 := by decide +kernel

theorem rowCheck15026 : row15026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15026 := by decide +kernel

theorem rowEval15026 (x : Key → ℝ) : Integer.Sparse.eval row15026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15026, Integer.Sparse.eval_collectBalanced, rawRowCheck15026]

theorem rawRowCheck15027 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form7 = rawRow15027 := by decide +kernel

theorem rowCheck15027 : row15027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15027 := by decide +kernel

theorem rowEval15027 (x : Key → ℝ) : Integer.Sparse.eval row15027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15027, Integer.Sparse.eval_collectBalanced, rawRowCheck15027]

theorem rawRowCheck15028 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form7 = rawRow15028 := by decide +kernel

theorem rowCheck15028 : row15028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15028 := by decide +kernel

theorem rowEval15028 (x : Key → ℝ) : Integer.Sparse.eval row15028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15028, Integer.Sparse.eval_collectBalanced, rawRowCheck15028]

theorem rawRowCheck15029 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form7 = rawRow15029 := by decide +kernel

theorem rowCheck15029 : row15029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15029 := by decide +kernel

theorem rowEval15029 (x : Key → ℝ) : Integer.Sparse.eval row15029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15029, Integer.Sparse.eval_collectBalanced, rawRowCheck15029]

theorem rawRowCheck15030 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form7 = rawRow15030 := by decide +kernel

theorem rowCheck15030 : row15030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15030 := by decide +kernel

theorem rowEval15030 (x : Key → ℝ) : Integer.Sparse.eval row15030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15030, Integer.Sparse.eval_collectBalanced, rawRowCheck15030]

theorem rawRowCheck15031 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form7 = rawRow15031 := by decide +kernel

theorem rowCheck15031 : row15031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15031 := by decide +kernel

theorem rowEval15031 (x : Key → ℝ) : Integer.Sparse.eval row15031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15031, Integer.Sparse.eval_collectBalanced, rawRowCheck15031]

theorem rawRowCheck15032 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form7 = rawRow15032 := by decide +kernel

theorem rowCheck15032 : row15032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15032 := by decide +kernel

theorem rowEval15032 (x : Key → ℝ) : Integer.Sparse.eval row15032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15032, Integer.Sparse.eval_collectBalanced, rawRowCheck15032]

theorem rawRowCheck15033 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form7 = rawRow15033 := by decide +kernel

theorem rowCheck15033 : row15033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15033 := by decide +kernel

theorem rowEval15033 (x : Key → ℝ) : Integer.Sparse.eval row15033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15033, Integer.Sparse.eval_collectBalanced, rawRowCheck15033]

theorem rawRowCheck15034 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form7 = rawRow15034 := by decide +kernel

theorem rowCheck15034 : row15034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15034 := by decide +kernel

theorem rowEval15034 (x : Key → ℝ) : Integer.Sparse.eval row15034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15034, Integer.Sparse.eval_collectBalanced, rawRowCheck15034]

theorem rawRowCheck15035 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form7 = rawRow15035 := by decide +kernel

theorem rowCheck15035 : row15035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15035 := by decide +kernel

theorem rowEval15035 (x : Key → ℝ) : Integer.Sparse.eval row15035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15035, Integer.Sparse.eval_collectBalanced, rawRowCheck15035]

theorem rawRowCheck15036 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form7 = rawRow15036 := by decide +kernel

theorem rowCheck15036 : row15036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15036 := by decide +kernel

theorem rowEval15036 (x : Key → ℝ) : Integer.Sparse.eval row15036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15036, Integer.Sparse.eval_collectBalanced, rawRowCheck15036]

theorem rawRowCheck15037 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form7 = rawRow15037 := by decide +kernel

theorem rowCheck15037 : row15037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15037 := by decide +kernel

theorem rowEval15037 (x : Key → ℝ) : Integer.Sparse.eval row15037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15037, Integer.Sparse.eval_collectBalanced, rawRowCheck15037]

theorem rawRowCheck15038 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form7 = rawRow15038 := by decide +kernel

theorem rowCheck15038 : row15038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15038 := by decide +kernel

theorem rowEval15038 (x : Key → ℝ) : Integer.Sparse.eval row15038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15038, Integer.Sparse.eval_collectBalanced, rawRowCheck15038]

theorem rawRowCheck15039 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form7 = rawRow15039 := by decide +kernel

theorem rowCheck15039 : row15039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15039 := by decide +kernel

theorem rowEval15039 (x : Key → ℝ) : Integer.Sparse.eval row15039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15039, Integer.Sparse.eval_collectBalanced, rawRowCheck15039]

theorem rawRowCheck15040 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form7 = rawRow15040 := by decide +kernel

theorem rowCheck15040 : row15040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15040 := by decide +kernel

theorem rowEval15040 (x : Key → ℝ) : Integer.Sparse.eval row15040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15040, Integer.Sparse.eval_collectBalanced, rawRowCheck15040]

theorem rawRowCheck15041 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form7 = rawRow15041 := by decide +kernel

theorem rowCheck15041 : row15041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15041 := by decide +kernel

theorem rowEval15041 (x : Key → ℝ) : Integer.Sparse.eval row15041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15041, Integer.Sparse.eval_collectBalanced, rawRowCheck15041]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck12_7 : entry12_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_7 k)) := by decide +kernel

theorem rowsSound12_7 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval15015 x
  · exact rowEval15016 x
  · exact rowEval15017 x
  · exact rowEval15018 x
  · exact rowEval15019 x
  · exact rowEval15020 x
  · exact rowEval15021 x
  · exact rowEval15022 x
  · exact rowEval15023 x
  · exact rowEval15024 x
  · exact rowEval15025 x
  · exact rowEval15026 x
  · exact rowEval15027 x
  · exact rowEval15028 x
  · exact rowEval15029 x
  · exact rowEval15030 x
  · exact rowEval15031 x
  · exact rowEval15032 x
  · exact rowEval15033 x
  · exact rowEval15034 x
  · exact rowEval15035 x
  · exact rowEval15036 x
  · exact rowEval15037 x
  · exact rowEval15038 x
  · exact rowEval15039 x
  · exact rowEval15040 x
  · exact rowEval15041 x

theorem entryEval12_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_7 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck12_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_7]

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

theorem rawRowCheck13845 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0 = rawRow13845 := by decide +kernel

theorem rowCheck13845 : row13845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13845 := by decide +kernel

theorem rowEval13845 (x : Key → ℝ) : Integer.Sparse.eval row13845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13845, Integer.Sparse.eval_collectBalanced, rawRowCheck13845]

theorem rawRowCheck13846 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0 = rawRow13846 := by decide +kernel

theorem rowCheck13846 : row13846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13846 := by decide +kernel

theorem rowEval13846 (x : Key → ℝ) : Integer.Sparse.eval row13846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13846, Integer.Sparse.eval_collectBalanced, rawRowCheck13846]

theorem rawRowCheck13847 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0 = rawRow13847 := by decide +kernel

theorem rowCheck13847 : row13847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13847 := by decide +kernel

theorem rowEval13847 (x : Key → ℝ) : Integer.Sparse.eval row13847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13847, Integer.Sparse.eval_collectBalanced, rawRowCheck13847]

theorem rawRowCheck13848 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0 = rawRow13848 := by decide +kernel

theorem rowCheck13848 : row13848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13848 := by decide +kernel

theorem rowEval13848 (x : Key → ℝ) : Integer.Sparse.eval row13848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13848, Integer.Sparse.eval_collectBalanced, rawRowCheck13848]

theorem rawRowCheck13849 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0 = rawRow13849 := by decide +kernel

theorem rowCheck13849 : row13849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13849 := by decide +kernel

theorem rowEval13849 (x : Key → ℝ) : Integer.Sparse.eval row13849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13849, Integer.Sparse.eval_collectBalanced, rawRowCheck13849]

theorem rawRowCheck13850 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0 = rawRow13850 := by decide +kernel

theorem rowCheck13850 : row13850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13850 := by decide +kernel

theorem rowEval13850 (x : Key → ℝ) : Integer.Sparse.eval row13850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13850, Integer.Sparse.eval_collectBalanced, rawRowCheck13850]

theorem rawRowCheck13851 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow13851 := by decide +kernel

theorem rowCheck13851 : row13851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13851 := by decide +kernel

theorem rowEval13851 (x : Key → ℝ) : Integer.Sparse.eval row13851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13851, Integer.Sparse.eval_collectBalanced, rawRowCheck13851]

theorem rawRowCheck13852 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow13852 := by decide +kernel

theorem rowCheck13852 : row13852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13852 := by decide +kernel

theorem rowEval13852 (x : Key → ℝ) : Integer.Sparse.eval row13852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13852, Integer.Sparse.eval_collectBalanced, rawRowCheck13852]

theorem rawRowCheck13853 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow13853 := by decide +kernel

theorem rowCheck13853 : row13853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13853 := by decide +kernel

theorem rowEval13853 (x : Key → ℝ) : Integer.Sparse.eval row13853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13853, Integer.Sparse.eval_collectBalanced, rawRowCheck13853]

theorem rawRowCheck13854 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow13854 := by decide +kernel

theorem rowCheck13854 : row13854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13854 := by decide +kernel

theorem rowEval13854 (x : Key → ℝ) : Integer.Sparse.eval row13854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13854, Integer.Sparse.eval_collectBalanced, rawRowCheck13854]

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

theorem rawRowCheck13885 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4 = rawRow13885 := by decide +kernel

theorem rowCheck13885 : row13885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13885 := by decide +kernel

theorem rowEval13885 (x : Key → ℝ) : Integer.Sparse.eval row13885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13885, Integer.Sparse.eval_collectBalanced, rawRowCheck13885]

theorem rawRowCheck13886 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4 = rawRow13886 := by decide +kernel

theorem rowCheck13886 : row13886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13886 := by decide +kernel

theorem rowEval13886 (x : Key → ℝ) : Integer.Sparse.eval row13886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13886, Integer.Sparse.eval_collectBalanced, rawRowCheck13886]

theorem rawRowCheck13887 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4 = rawRow13887 := by decide +kernel

theorem rowCheck13887 : row13887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13887 := by decide +kernel

theorem rowEval13887 (x : Key → ℝ) : Integer.Sparse.eval row13887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13887, Integer.Sparse.eval_collectBalanced, rawRowCheck13887]

theorem rawRowCheck13888 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4 = rawRow13888 := by decide +kernel

theorem rowCheck13888 : row13888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13888 := by decide +kernel

theorem rowEval13888 (x : Key → ℝ) : Integer.Sparse.eval row13888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13888, Integer.Sparse.eval_collectBalanced, rawRowCheck13888]

theorem rawRowCheck13889 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4 = rawRow13889 := by decide +kernel

theorem rowCheck13889 : row13889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13889 := by decide +kernel

theorem rowEval13889 (x : Key → ℝ) : Integer.Sparse.eval row13889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13889, Integer.Sparse.eval_collectBalanced, rawRowCheck13889]

theorem rawRowCheck13890 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4 = rawRow13890 := by decide +kernel

theorem rowCheck13890 : row13890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13890 := by decide +kernel

theorem rowEval13890 (x : Key → ℝ) : Integer.Sparse.eval row13890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13890, Integer.Sparse.eval_collectBalanced, rawRowCheck13890]

theorem rawRowCheck13891 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow13891 := by decide +kernel

theorem rowCheck13891 : row13891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13891 := by decide +kernel

theorem rowEval13891 (x : Key → ℝ) : Integer.Sparse.eval row13891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13891, Integer.Sparse.eval_collectBalanced, rawRowCheck13891]

theorem rawRowCheck13892 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow13892 := by decide +kernel

theorem rowCheck13892 : row13892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13892 := by decide +kernel

theorem rowEval13892 (x : Key → ℝ) : Integer.Sparse.eval row13892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13892, Integer.Sparse.eval_collectBalanced, rawRowCheck13892]

theorem rawRowCheck13893 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow13893 := by decide +kernel

theorem rowCheck13893 : row13893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13893 := by decide +kernel

theorem rowEval13893 (x : Key → ℝ) : Integer.Sparse.eval row13893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13893, Integer.Sparse.eval_collectBalanced, rawRowCheck13893]

theorem rawRowCheck13894 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow13894 := by decide +kernel

theorem rowCheck13894 : row13894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13894 := by decide +kernel

theorem rowEval13894 (x : Key → ℝ) : Integer.Sparse.eval row13894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13894, Integer.Sparse.eval_collectBalanced, rawRowCheck13894]

theorem rawRowCheck13895 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5 = rawRow13895 := by decide +kernel

theorem rowCheck13895 : row13895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13895 := by decide +kernel

theorem rowEval13895 (x : Key → ℝ) : Integer.Sparse.eval row13895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13895, Integer.Sparse.eval_collectBalanced, rawRowCheck13895]

theorem rawRowCheck13896 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5 = rawRow13896 := by decide +kernel

theorem rowCheck13896 : row13896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13896 := by decide +kernel

theorem rowEval13896 (x : Key → ℝ) : Integer.Sparse.eval row13896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13896, Integer.Sparse.eval_collectBalanced, rawRowCheck13896]

theorem rawRowCheck13897 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5 = rawRow13897 := by decide +kernel

theorem rowCheck13897 : row13897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13897 := by decide +kernel

theorem rowEval13897 (x : Key → ℝ) : Integer.Sparse.eval row13897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13897, Integer.Sparse.eval_collectBalanced, rawRowCheck13897]

theorem rawRowCheck13898 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5 = rawRow13898 := by decide +kernel

theorem rowCheck13898 : row13898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13898 := by decide +kernel

theorem rowEval13898 (x : Key → ℝ) : Integer.Sparse.eval row13898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13898, Integer.Sparse.eval_collectBalanced, rawRowCheck13898]

theorem rawRowCheck13899 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5 = rawRow13899 := by decide +kernel

theorem rowCheck13899 : row13899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13899 := by decide +kernel

theorem rowEval13899 (x : Key → ℝ) : Integer.Sparse.eval row13899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13899, Integer.Sparse.eval_collectBalanced, rawRowCheck13899]

theorem rawRowCheck13900 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5 = rawRow13900 := by decide +kernel

theorem rowCheck13900 : row13900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13900 := by decide +kernel

theorem rowEval13900 (x : Key → ℝ) : Integer.Sparse.eval row13900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13900, Integer.Sparse.eval_collectBalanced, rawRowCheck13900]

theorem rawRowCheck13901 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow13901 := by decide +kernel

theorem rowCheck13901 : row13901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13901 := by decide +kernel

theorem rowEval13901 (x : Key → ℝ) : Integer.Sparse.eval row13901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13901, Integer.Sparse.eval_collectBalanced, rawRowCheck13901]

theorem rawRowCheck13902 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow13902 := by decide +kernel

theorem rowCheck13902 : row13902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13902 := by decide +kernel

theorem rowEval13902 (x : Key → ℝ) : Integer.Sparse.eval row13902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13902, Integer.Sparse.eval_collectBalanced, rawRowCheck13902]

theorem rawRowCheck13903 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow13903 := by decide +kernel

theorem rowCheck13903 : row13903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13903 := by decide +kernel

theorem rowEval13903 (x : Key → ℝ) : Integer.Sparse.eval row13903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13903, Integer.Sparse.eval_collectBalanced, rawRowCheck13903]

theorem rawRowCheck13904 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow13904 := by decide +kernel

theorem rowCheck13904 : row13904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13904 := by decide +kernel

theorem rowEval13904 (x : Key → ℝ) : Integer.Sparse.eval row13904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13904, Integer.Sparse.eval_collectBalanced, rawRowCheck13904]

theorem rawRowCheck13905 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form6 = rawRow13905 := by decide +kernel

theorem rowCheck13905 : row13905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13905 := by decide +kernel

theorem rowEval13905 (x : Key → ℝ) : Integer.Sparse.eval row13905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13905, Integer.Sparse.eval_collectBalanced, rawRowCheck13905]

theorem rawRowCheck13906 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form6 = rawRow13906 := by decide +kernel

theorem rowCheck13906 : row13906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13906 := by decide +kernel

theorem rowEval13906 (x : Key → ℝ) : Integer.Sparse.eval row13906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13906, Integer.Sparse.eval_collectBalanced, rawRowCheck13906]

theorem rawRowCheck13907 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form6 = rawRow13907 := by decide +kernel

theorem rowCheck13907 : row13907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13907 := by decide +kernel

theorem rowEval13907 (x : Key → ℝ) : Integer.Sparse.eval row13907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13907, Integer.Sparse.eval_collectBalanced, rawRowCheck13907]

theorem rawRowCheck13908 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form6 = rawRow13908 := by decide +kernel

theorem rowCheck13908 : row13908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13908 := by decide +kernel

theorem rowEval13908 (x : Key → ℝ) : Integer.Sparse.eval row13908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13908, Integer.Sparse.eval_collectBalanced, rawRowCheck13908]

theorem rawRowCheck13909 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form6 = rawRow13909 := by decide +kernel

theorem rowCheck13909 : row13909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13909 := by decide +kernel

theorem rowEval13909 (x : Key → ℝ) : Integer.Sparse.eval row13909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13909, Integer.Sparse.eval_collectBalanced, rawRowCheck13909]

theorem rawRowCheck13910 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form6 = rawRow13910 := by decide +kernel

theorem rowCheck13910 : row13910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13910 := by decide +kernel

theorem rowEval13910 (x : Key → ℝ) : Integer.Sparse.eval row13910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13910, Integer.Sparse.eval_collectBalanced, rawRowCheck13910]

theorem rawRowCheck13911 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form6 = rawRow13911 := by decide +kernel

theorem rowCheck13911 : row13911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13911 := by decide +kernel

theorem rowEval13911 (x : Key → ℝ) : Integer.Sparse.eval row13911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13911, Integer.Sparse.eval_collectBalanced, rawRowCheck13911]

theorem rawRowCheck13912 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form6 = rawRow13912 := by decide +kernel

theorem rowCheck13912 : row13912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13912 := by decide +kernel

theorem rowEval13912 (x : Key → ℝ) : Integer.Sparse.eval row13912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13912, Integer.Sparse.eval_collectBalanced, rawRowCheck13912]

theorem rawRowCheck13913 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form6 = rawRow13913 := by decide +kernel

theorem rowCheck13913 : row13913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13913 := by decide +kernel

theorem rowEval13913 (x : Key → ℝ) : Integer.Sparse.eval row13913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13913, Integer.Sparse.eval_collectBalanced, rawRowCheck13913]

theorem rawRowCheck13914 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form6 = rawRow13914 := by decide +kernel

theorem rowCheck13914 : row13914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13914 := by decide +kernel

theorem rowEval13914 (x : Key → ℝ) : Integer.Sparse.eval row13914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck13914, Integer.Sparse.eval_collectBalanced, rawRowCheck13914]

theorem rawRowCheck13915 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form7 = rawRow13915 := by decide +kernel

theorem rowCheck13915 : row13915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13915 := by decide +kernel

theorem rowEval13915 (x : Key → ℝ) : Integer.Sparse.eval row13915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck13915, Integer.Sparse.eval_collectBalanced, rawRowCheck13915]

theorem rawRowCheck13916 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form7 = rawRow13916 := by decide +kernel

theorem rowCheck13916 : row13916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13916 := by decide +kernel

theorem rowEval13916 (x : Key → ℝ) : Integer.Sparse.eval row13916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck13916, Integer.Sparse.eval_collectBalanced, rawRowCheck13916]

theorem rawRowCheck13917 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form7 = rawRow13917 := by decide +kernel

theorem rowCheck13917 : row13917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13917 := by decide +kernel

theorem rowEval13917 (x : Key → ℝ) : Integer.Sparse.eval row13917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13917, Integer.Sparse.eval_collectBalanced, rawRowCheck13917]

theorem rawRowCheck13918 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form7 = rawRow13918 := by decide +kernel

theorem rowCheck13918 : row13918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13918 := by decide +kernel

theorem rowEval13918 (x : Key → ℝ) : Integer.Sparse.eval row13918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck13918, Integer.Sparse.eval_collectBalanced, rawRowCheck13918]

theorem rawRowCheck13919 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form7 = rawRow13919 := by decide +kernel

theorem rowCheck13919 : row13919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13919 := by decide +kernel

theorem rowEval13919 (x : Key → ℝ) : Integer.Sparse.eval row13919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13919, Integer.Sparse.eval_collectBalanced, rawRowCheck13919]

theorem rawRowCheck13920 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form7 = rawRow13920 := by decide +kernel

theorem rowCheck13920 : row13920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13920 := by decide +kernel

theorem rowEval13920 (x : Key → ℝ) : Integer.Sparse.eval row13920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13920, Integer.Sparse.eval_collectBalanced, rawRowCheck13920]

theorem rawRowCheck13921 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow13921 := by decide +kernel

theorem rowCheck13921 : row13921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13921 := by decide +kernel

theorem rowEval13921 (x : Key → ℝ) : Integer.Sparse.eval row13921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck13921, Integer.Sparse.eval_collectBalanced, rawRowCheck13921]

theorem rawRowCheck13922 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow13922 := by decide +kernel

theorem rowCheck13922 : row13922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13922 := by decide +kernel

theorem rowEval13922 (x : Key → ℝ) : Integer.Sparse.eval row13922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13922, Integer.Sparse.eval_collectBalanced, rawRowCheck13922]

theorem rawRowCheck13923 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow13923 := by decide +kernel

theorem rowCheck13923 : row13923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13923 := by decide +kernel

theorem rowEval13923 (x : Key → ℝ) : Integer.Sparse.eval row13923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13923, Integer.Sparse.eval_collectBalanced, rawRowCheck13923]

theorem rawRowCheck13924 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow13924 := by decide +kernel

theorem rowCheck13924 : row13924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13924 := by decide +kernel

theorem rowEval13924 (x : Key → ℝ) : Integer.Sparse.eval row13924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13924, Integer.Sparse.eval_collectBalanced, rawRowCheck13924]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck15303 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form7 = rawRow15303 := by decide +kernel

theorem rowCheck15303 : row15303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15303 := by decide +kernel

theorem rowEval15303 (x : Key → ℝ) : Integer.Sparse.eval row15303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15303, Integer.Sparse.eval_collectBalanced, rawRowCheck15303]

theorem rawRowCheck15304 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form7 = rawRow15304 := by decide +kernel

theorem rowCheck15304 : row15304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15304 := by decide +kernel

theorem rowEval15304 (x : Key → ℝ) : Integer.Sparse.eval row15304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15304, Integer.Sparse.eval_collectBalanced, rawRowCheck15304]

theorem rawRowCheck15305 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form7 = rawRow15305 := by decide +kernel

theorem rowCheck15305 : row15305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15305 := by decide +kernel

theorem rowEval15305 (x : Key → ℝ) : Integer.Sparse.eval row15305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15305, Integer.Sparse.eval_collectBalanced, rawRowCheck15305]

theorem rawRowCheck15306 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form7 = rawRow15306 := by decide +kernel

theorem rowCheck15306 : row15306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15306 := by decide +kernel

theorem rowEval15306 (x : Key → ℝ) : Integer.Sparse.eval row15306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15306, Integer.Sparse.eval_collectBalanced, rawRowCheck15306]

theorem rawRowCheck15307 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form7 = rawRow15307 := by decide +kernel

theorem rowCheck15307 : row15307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15307 := by decide +kernel

theorem rowEval15307 (x : Key → ℝ) : Integer.Sparse.eval row15307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15307, Integer.Sparse.eval_collectBalanced, rawRowCheck15307]

theorem rawRowCheck15308 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form7 = rawRow15308 := by decide +kernel

theorem rowCheck15308 : row15308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15308 := by decide +kernel

theorem rowEval15308 (x : Key → ℝ) : Integer.Sparse.eval row15308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15308, Integer.Sparse.eval_collectBalanced, rawRowCheck15308]

theorem rawRowCheck15309 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form7 = rawRow15309 := by decide +kernel

theorem rowCheck15309 : row15309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15309 := by decide +kernel

theorem rowEval15309 (x : Key → ℝ) : Integer.Sparse.eval row15309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15309, Integer.Sparse.eval_collectBalanced, rawRowCheck15309]

theorem rawRowCheck15310 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form7 = rawRow15310 := by decide +kernel

theorem rowCheck15310 : row15310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15310 := by decide +kernel

theorem rowEval15310 (x : Key → ℝ) : Integer.Sparse.eval row15310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15310, Integer.Sparse.eval_collectBalanced, rawRowCheck15310]

theorem rawRowCheck15311 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form7 = rawRow15311 := by decide +kernel

theorem rowCheck15311 : row15311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15311 := by decide +kernel

theorem rowEval15311 (x : Key → ℝ) : Integer.Sparse.eval row15311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15311, Integer.Sparse.eval_collectBalanced, rawRowCheck15311]

theorem rawRowCheck15312 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form7 = rawRow15312 := by decide +kernel

theorem rowCheck15312 : row15312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15312 := by decide +kernel

theorem rowEval15312 (x : Key → ℝ) : Integer.Sparse.eval row15312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15312, Integer.Sparse.eval_collectBalanced, rawRowCheck15312]

theorem rawRowCheck15313 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form7 = rawRow15313 := by decide +kernel

theorem rowCheck15313 : row15313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15313 := by decide +kernel

theorem rowEval15313 (x : Key → ℝ) : Integer.Sparse.eval row15313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15313, Integer.Sparse.eval_collectBalanced, rawRowCheck15313]

theorem rawRowCheck15314 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form7 = rawRow15314 := by decide +kernel

theorem rowCheck15314 : row15314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15314 := by decide +kernel

theorem rowEval15314 (x : Key → ℝ) : Integer.Sparse.eval row15314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15314, Integer.Sparse.eval_collectBalanced, rawRowCheck15314]

theorem rawRowCheck15315 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form7 = rawRow15315 := by decide +kernel

theorem rowCheck15315 : row15315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15315 := by decide +kernel

theorem rowEval15315 (x : Key → ℝ) : Integer.Sparse.eval row15315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15315, Integer.Sparse.eval_collectBalanced, rawRowCheck15315]

theorem rawRowCheck15316 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form7 = rawRow15316 := by decide +kernel

theorem rowCheck15316 : row15316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15316 := by decide +kernel

theorem rowEval15316 (x : Key → ℝ) : Integer.Sparse.eval row15316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15316, Integer.Sparse.eval_collectBalanced, rawRowCheck15316]

theorem rawRowCheck15317 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form7 = rawRow15317 := by decide +kernel

theorem rowCheck15317 : row15317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15317 := by decide +kernel

theorem rowEval15317 (x : Key → ℝ) : Integer.Sparse.eval row15317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15317, Integer.Sparse.eval_collectBalanced, rawRowCheck15317]

theorem rawRowCheck15318 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form7 = rawRow15318 := by decide +kernel

theorem rowCheck15318 : row15318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15318 := by decide +kernel

theorem rowEval15318 (x : Key → ℝ) : Integer.Sparse.eval row15318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15318, Integer.Sparse.eval_collectBalanced, rawRowCheck15318]

theorem rawRowCheck15319 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form7 = rawRow15319 := by decide +kernel

theorem rowCheck15319 : row15319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15319 := by decide +kernel

theorem rowEval15319 (x : Key → ℝ) : Integer.Sparse.eval row15319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15319, Integer.Sparse.eval_collectBalanced, rawRowCheck15319]

theorem rawRowCheck15320 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form7 = rawRow15320 := by decide +kernel

theorem rowCheck15320 : row15320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15320 := by decide +kernel

theorem rowEval15320 (x : Key → ℝ) : Integer.Sparse.eval row15320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15320, Integer.Sparse.eval_collectBalanced, rawRowCheck15320]

theorem rawRowCheck15321 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form7 = rawRow15321 := by decide +kernel

theorem rowCheck15321 : row15321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15321 := by decide +kernel

theorem rowEval15321 (x : Key → ℝ) : Integer.Sparse.eval row15321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15321, Integer.Sparse.eval_collectBalanced, rawRowCheck15321]

theorem rawRowCheck15322 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form7 = rawRow15322 := by decide +kernel

theorem rowCheck15322 : row15322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15322 := by decide +kernel

theorem rowEval15322 (x : Key → ℝ) : Integer.Sparse.eval row15322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15322, Integer.Sparse.eval_collectBalanced, rawRowCheck15322]

theorem rawRowCheck15323 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form7 = rawRow15323 := by decide +kernel

theorem rowCheck15323 : row15323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15323 := by decide +kernel

theorem rowEval15323 (x : Key → ℝ) : Integer.Sparse.eval row15323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15323, Integer.Sparse.eval_collectBalanced, rawRowCheck15323]

theorem rawRowCheck15324 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form7 = rawRow15324 := by decide +kernel

theorem rowCheck15324 : row15324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15324 := by decide +kernel

theorem rowEval15324 (x : Key → ℝ) : Integer.Sparse.eval row15324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15324, Integer.Sparse.eval_collectBalanced, rawRowCheck15324]

theorem rawRowCheck15325 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form7 = rawRow15325 := by decide +kernel

theorem rowCheck15325 : row15325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15325 := by decide +kernel

theorem rowEval15325 (x : Key → ℝ) : Integer.Sparse.eval row15325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15325, Integer.Sparse.eval_collectBalanced, rawRowCheck15325]

theorem rawRowCheck15326 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form7 = rawRow15326 := by decide +kernel

theorem rowCheck15326 : row15326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15326 := by decide +kernel

theorem rowEval15326 (x : Key → ℝ) : Integer.Sparse.eval row15326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15326, Integer.Sparse.eval_collectBalanced, rawRowCheck15326]

theorem rawRowCheck15327 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form7 = rawRow15327 := by decide +kernel

theorem rowCheck15327 : row15327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15327 := by decide +kernel

theorem rowEval15327 (x : Key → ℝ) : Integer.Sparse.eval row15327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15327, Integer.Sparse.eval_collectBalanced, rawRowCheck15327]

theorem rawRowCheck15328 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form7 = rawRow15328 := by decide +kernel

theorem rowCheck15328 : row15328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15328 := by decide +kernel

theorem rowEval15328 (x : Key → ℝ) : Integer.Sparse.eval row15328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15328, Integer.Sparse.eval_collectBalanced, rawRowCheck15328]

theorem rawRowCheck15329 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form7 = rawRow15329 := by decide +kernel

theorem rowCheck15329 : row15329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15329 := by decide +kernel

theorem rowEval15329 (x : Key → ℝ) : Integer.Sparse.eval row15329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15329, Integer.Sparse.eval_collectBalanced, rawRowCheck15329]

theorem rawRowCheck15330 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form7 = rawRow15330 := by decide +kernel

theorem rowCheck15330 : row15330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15330 := by decide +kernel

theorem rowEval15330 (x : Key → ℝ) : Integer.Sparse.eval row15330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15330, Integer.Sparse.eval_collectBalanced, rawRowCheck15330]

theorem rawRowCheck15331 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form7 = rawRow15331 := by decide +kernel

theorem rowCheck15331 : row15331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15331 := by decide +kernel

theorem rowEval15331 (x : Key → ℝ) : Integer.Sparse.eval row15331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15331, Integer.Sparse.eval_collectBalanced, rawRowCheck15331]

theorem rawRowCheck15332 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form7 = rawRow15332 := by decide +kernel

theorem rowCheck15332 : row15332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15332 := by decide +kernel

theorem rowEval15332 (x : Key → ℝ) : Integer.Sparse.eval row15332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15332, Integer.Sparse.eval_collectBalanced, rawRowCheck15332]

theorem rawRowCheck15333 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form7 = rawRow15333 := by decide +kernel

theorem rowCheck15333 : row15333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15333 := by decide +kernel

theorem rowEval15333 (x : Key → ℝ) : Integer.Sparse.eval row15333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15333, Integer.Sparse.eval_collectBalanced, rawRowCheck15333]

theorem rawRowCheck15334 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form7 = rawRow15334 := by decide +kernel

theorem rowCheck15334 : row15334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15334 := by decide +kernel

theorem rowEval15334 (x : Key → ℝ) : Integer.Sparse.eval row15334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15334, Integer.Sparse.eval_collectBalanced, rawRowCheck15334]

theorem rawRowCheck15335 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form7 = rawRow15335 := by decide +kernel

theorem rowCheck15335 : row15335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15335 := by decide +kernel

theorem rowEval15335 (x : Key → ℝ) : Integer.Sparse.eval row15335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15335, Integer.Sparse.eval_collectBalanced, rawRowCheck15335]

theorem rawRowCheck15336 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form7 = rawRow15336 := by decide +kernel

theorem rowCheck15336 : row15336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15336 := by decide +kernel

theorem rowEval15336 (x : Key → ℝ) : Integer.Sparse.eval row15336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15336, Integer.Sparse.eval_collectBalanced, rawRowCheck15336]

theorem rawRowCheck15337 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form7 = rawRow15337 := by decide +kernel

theorem rowCheck15337 : row15337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15337 := by decide +kernel

theorem rowEval15337 (x : Key → ℝ) : Integer.Sparse.eval row15337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15337, Integer.Sparse.eval_collectBalanced, rawRowCheck15337]

theorem rawRowCheck15338 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form7 = rawRow15338 := by decide +kernel

theorem rowCheck15338 : row15338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15338 := by decide +kernel

theorem rowEval15338 (x : Key → ℝ) : Integer.Sparse.eval row15338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15338, Integer.Sparse.eval_collectBalanced, rawRowCheck15338]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck13_7 : entry13_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form13.terms k).coefficient) (rows13_7 k)) := by decide +kernel

theorem rowsSound13_7 (k : Fin GramFunctions.Block4.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form13.terms k).tag (GramFunctions.Block4.form13.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval15303 x
  · exact rowEval15304 x
  · exact rowEval15305 x
  · exact rowEval15306 x
  · exact rowEval15307 x
  · exact rowEval15308 x
  · exact rowEval15309 x
  · exact rowEval15310 x
  · exact rowEval15311 x
  · exact rowEval15312 x
  · exact rowEval15313 x
  · exact rowEval15314 x
  · exact rowEval15315 x
  · exact rowEval15316 x
  · exact rowEval15317 x
  · exact rowEval15318 x
  · exact rowEval15319 x
  · exact rowEval15320 x
  · exact rowEval15321 x
  · exact rowEval15322 x
  · exact rowEval15323 x
  · exact rowEval15324 x
  · exact rowEval15325 x
  · exact rowEval15326 x
  · exact rowEval15327 x
  · exact rowEval15328 x
  · exact rowEval15329 x
  · exact rowEval15330 x
  · exact rowEval15331 x
  · exact rowEval15332 x
  · exact rowEval15333 x
  · exact rowEval15334 x
  · exact rowEval15335 x
  · exact rowEval15336 x
  · exact rowEval15337 x
  · exact rowEval15338 x

theorem entryEval13_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_7 (GramNormalization.eval B) = GramFunctions.Block4.form13.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck13_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form13 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_7]

end MUB6.Certificate.GramEntries.Block4

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

theorem rawRowCheck16833 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form7 = rawRow16833 := by decide +kernel

theorem rowCheck16833 : row16833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16833 := by decide +kernel

theorem rowEval16833 (x : Key → ℝ) : Integer.Sparse.eval row16833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16833, Integer.Sparse.eval_collectBalanced, rawRowCheck16833]

theorem rawRowCheck16834 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form7 = rawRow16834 := by decide +kernel

theorem rowCheck16834 : row16834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16834 := by decide +kernel

theorem rowEval16834 (x : Key → ℝ) : Integer.Sparse.eval row16834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16834, Integer.Sparse.eval_collectBalanced, rawRowCheck16834]

theorem rawRowCheck16835 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form7 = rawRow16835 := by decide +kernel

theorem rowCheck16835 : row16835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16835 := by decide +kernel

theorem rowEval16835 (x : Key → ℝ) : Integer.Sparse.eval row16835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16835, Integer.Sparse.eval_collectBalanced, rawRowCheck16835]

theorem rawRowCheck16836 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form7 = rawRow16836 := by decide +kernel

theorem rowCheck16836 : row16836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16836 := by decide +kernel

theorem rowEval16836 (x : Key → ℝ) : Integer.Sparse.eval row16836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16836, Integer.Sparse.eval_collectBalanced, rawRowCheck16836]

theorem rawRowCheck16837 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form7 = rawRow16837 := by decide +kernel

theorem rowCheck16837 : row16837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16837 := by decide +kernel

theorem rowEval16837 (x : Key → ℝ) : Integer.Sparse.eval row16837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16837, Integer.Sparse.eval_collectBalanced, rawRowCheck16837]

theorem rawRowCheck16838 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form7 = rawRow16838 := by decide +kernel

theorem rowCheck16838 : row16838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16838 := by decide +kernel

theorem rowEval16838 (x : Key → ℝ) : Integer.Sparse.eval row16838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16838, Integer.Sparse.eval_collectBalanced, rawRowCheck16838]

theorem rawRowCheck16839 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form7 = rawRow16839 := by decide +kernel

theorem rowCheck16839 : row16839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16839 := by decide +kernel

theorem rowEval16839 (x : Key → ℝ) : Integer.Sparse.eval row16839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16839, Integer.Sparse.eval_collectBalanced, rawRowCheck16839]

theorem rawRowCheck16840 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form7 = rawRow16840 := by decide +kernel

theorem rowCheck16840 : row16840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16840 := by decide +kernel

theorem rowEval16840 (x : Key → ℝ) : Integer.Sparse.eval row16840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16840, Integer.Sparse.eval_collectBalanced, rawRowCheck16840]

theorem rawRowCheck16841 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form7 = rawRow16841 := by decide +kernel

theorem rowCheck16841 : row16841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16841 := by decide +kernel

theorem rowEval16841 (x : Key → ℝ) : Integer.Sparse.eval row16841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16841, Integer.Sparse.eval_collectBalanced, rawRowCheck16841]

theorem rawRowCheck16842 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form7 = rawRow16842 := by decide +kernel

theorem rowCheck16842 : row16842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16842 := by decide +kernel

theorem rowEval16842 (x : Key → ℝ) : Integer.Sparse.eval row16842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16842, Integer.Sparse.eval_collectBalanced, rawRowCheck16842]

theorem rawRowCheck16843 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form7 = rawRow16843 := by decide +kernel

theorem rowCheck16843 : row16843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16843 := by decide +kernel

theorem rowEval16843 (x : Key → ℝ) : Integer.Sparse.eval row16843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16843, Integer.Sparse.eval_collectBalanced, rawRowCheck16843]

theorem rawRowCheck16844 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form7 = rawRow16844 := by decide +kernel

theorem rowCheck16844 : row16844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16844 := by decide +kernel

theorem rowEval16844 (x : Key → ℝ) : Integer.Sparse.eval row16844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16844, Integer.Sparse.eval_collectBalanced, rawRowCheck16844]

theorem rawRowCheck16845 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form7 = rawRow16845 := by decide +kernel

theorem rowCheck16845 : row16845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16845 := by decide +kernel

theorem rowEval16845 (x : Key → ℝ) : Integer.Sparse.eval row16845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16845, Integer.Sparse.eval_collectBalanced, rawRowCheck16845]

theorem rawRowCheck16846 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form7 = rawRow16846 := by decide +kernel

theorem rowCheck16846 : row16846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16846 := by decide +kernel

theorem rowEval16846 (x : Key → ℝ) : Integer.Sparse.eval row16846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16846, Integer.Sparse.eval_collectBalanced, rawRowCheck16846]

theorem rawRowCheck16847 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form7 = rawRow16847 := by decide +kernel

theorem rowCheck16847 : row16847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16847 := by decide +kernel

theorem rowEval16847 (x : Key → ℝ) : Integer.Sparse.eval row16847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16847, Integer.Sparse.eval_collectBalanced, rawRowCheck16847]

theorem rawRowCheck16848 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form7 = rawRow16848 := by decide +kernel

theorem rowCheck16848 : row16848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16848 := by decide +kernel

theorem rowEval16848 (x : Key → ℝ) : Integer.Sparse.eval row16848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16848, Integer.Sparse.eval_collectBalanced, rawRowCheck16848]

theorem rawRowCheck16849 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form7 = rawRow16849 := by decide +kernel

theorem rowCheck16849 : row16849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16849 := by decide +kernel

theorem rowEval16849 (x : Key → ℝ) : Integer.Sparse.eval row16849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16849, Integer.Sparse.eval_collectBalanced, rawRowCheck16849]

theorem rawRowCheck16850 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form7 = rawRow16850 := by decide +kernel

theorem rowCheck16850 : row16850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16850 := by decide +kernel

theorem rowEval16850 (x : Key → ℝ) : Integer.Sparse.eval row16850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16850, Integer.Sparse.eval_collectBalanced, rawRowCheck16850]

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

theorem entryCheck17_7 : entry17_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_7 k)) := by decide +kernel

theorem rowsSound17_7 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval16833 x
  · exact rowEval16834 x
  · exact rowEval16835 x
  · exact rowEval16836 x
  · exact rowEval16837 x
  · exact rowEval16838 x
  · exact rowEval16839 x
  · exact rowEval16840 x
  · exact rowEval16841 x
  · exact rowEval16842 x
  · exact rowEval16843 x
  · exact rowEval16844 x
  · exact rowEval16845 x
  · exact rowEval16846 x
  · exact rowEval16847 x
  · exact rowEval16848 x
  · exact rowEval16849 x
  · exact rowEval16850 x

theorem entryEval17_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_7 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck17_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_7]

end MUB6.Certificate.GramEntries.Block4

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

theorem rawRowCheck17481 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form7 = rawRow17481 := by decide +kernel

theorem rowCheck17481 : row17481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17481 := by decide +kernel

theorem rowEval17481 (x : Key → ℝ) : Integer.Sparse.eval row17481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17481, Integer.Sparse.eval_collectBalanced, rawRowCheck17481]

theorem rawRowCheck17482 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form7 = rawRow17482 := by decide +kernel

theorem rowCheck17482 : row17482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17482 := by decide +kernel

theorem rowEval17482 (x : Key → ℝ) : Integer.Sparse.eval row17482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17482, Integer.Sparse.eval_collectBalanced, rawRowCheck17482]

theorem rawRowCheck17483 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form7 = rawRow17483 := by decide +kernel

theorem rowCheck17483 : row17483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17483 := by decide +kernel

theorem rowEval17483 (x : Key → ℝ) : Integer.Sparse.eval row17483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17483, Integer.Sparse.eval_collectBalanced, rawRowCheck17483]

theorem rawRowCheck17484 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17484 := by decide +kernel

theorem rowCheck17484 : row17484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17484 := by decide +kernel

theorem rowEval17484 (x : Key → ℝ) : Integer.Sparse.eval row17484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17484, Integer.Sparse.eval_collectBalanced, rawRowCheck17484]

theorem rawRowCheck17485 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17485 := by decide +kernel

theorem rowCheck17485 : row17485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17485 := by decide +kernel

theorem rowEval17485 (x : Key → ℝ) : Integer.Sparse.eval row17485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17485, Integer.Sparse.eval_collectBalanced, rawRowCheck17485]

theorem rawRowCheck17486 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17486 := by decide +kernel

theorem rowCheck17486 : row17486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17486 := by decide +kernel

theorem rowEval17486 (x : Key → ℝ) : Integer.Sparse.eval row17486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17486, Integer.Sparse.eval_collectBalanced, rawRowCheck17486]

theorem rawRowCheck17487 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17487 := by decide +kernel

theorem rowCheck17487 : row17487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17487 := by decide +kernel

theorem rowEval17487 (x : Key → ℝ) : Integer.Sparse.eval row17487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17487, Integer.Sparse.eval_collectBalanced, rawRowCheck17487]

theorem rawRowCheck17488 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17488 := by decide +kernel

theorem rowCheck17488 : row17488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17488 := by decide +kernel

theorem rowEval17488 (x : Key → ℝ) : Integer.Sparse.eval row17488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17488, Integer.Sparse.eval_collectBalanced, rawRowCheck17488]

theorem rawRowCheck17489 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17489 := by decide +kernel

theorem rowCheck17489 : row17489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17489 := by decide +kernel

theorem rowEval17489 (x : Key → ℝ) : Integer.Sparse.eval row17489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17489, Integer.Sparse.eval_collectBalanced, rawRowCheck17489]

theorem rawRowCheck17490 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form7 = rawRow17490 := by decide +kernel

theorem rowCheck17490 : row17490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17490 := by decide +kernel

theorem rowEval17490 (x : Key → ℝ) : Integer.Sparse.eval row17490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17490, Integer.Sparse.eval_collectBalanced, rawRowCheck17490]

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

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval17481 x
  · exact rowEval17482 x
  · exact rowEval17483 x
  · exact rowEval17484 x
  · exact rowEval17485 x
  · exact rowEval17486 x
  · exact rowEval17487 x
  · exact rowEval17488 x
  · exact rowEval17489 x
  · exact rowEval17490 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

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

theorem rawRowCheck17737 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17737 := by decide +kernel

theorem rowCheck17737 : row17737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17737 := by decide +kernel

theorem rowEval17737 (x : Key → ℝ) : Integer.Sparse.eval row17737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17737, Integer.Sparse.eval_collectBalanced, rawRowCheck17737]

theorem rawRowCheck17738 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17738 := by decide +kernel

theorem rowCheck17738 : row17738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17738 := by decide +kernel

theorem rowEval17738 (x : Key → ℝ) : Integer.Sparse.eval row17738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17738, Integer.Sparse.eval_collectBalanced, rawRowCheck17738]

theorem rawRowCheck17739 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17739 := by decide +kernel

theorem rowCheck17739 : row17739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17739 := by decide +kernel

theorem rowEval17739 (x : Key → ℝ) : Integer.Sparse.eval row17739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17739, Integer.Sparse.eval_collectBalanced, rawRowCheck17739]

theorem rawRowCheck17740 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form7 = rawRow17740 := by decide +kernel

theorem rowCheck17740 : row17740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17740 := by decide +kernel

theorem rowEval17740 (x : Key → ℝ) : Integer.Sparse.eval row17740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17740, Integer.Sparse.eval_collectBalanced, rawRowCheck17740]

theorem rawRowCheck17741 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form7 = rawRow17741 := by decide +kernel

theorem rowCheck17741 : row17741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17741 := by decide +kernel

theorem rowEval17741 (x : Key → ℝ) : Integer.Sparse.eval row17741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17741, Integer.Sparse.eval_collectBalanced, rawRowCheck17741]

theorem rawRowCheck17742 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form7 = rawRow17742 := by decide +kernel

theorem rowCheck17742 : row17742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17742 := by decide +kernel

theorem rowEval17742 (x : Key → ℝ) : Integer.Sparse.eval row17742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17742, Integer.Sparse.eval_collectBalanced, rawRowCheck17742]

theorem rawRowCheck17743 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form7 = rawRow17743 := by decide +kernel

theorem rowCheck17743 : row17743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17743 := by decide +kernel

theorem rowEval17743 (x : Key → ℝ) : Integer.Sparse.eval row17743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17743, Integer.Sparse.eval_collectBalanced, rawRowCheck17743]

theorem rawRowCheck17744 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form7 = rawRow17744 := by decide +kernel

theorem rowCheck17744 : row17744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17744 := by decide +kernel

theorem rowEval17744 (x : Key → ℝ) : Integer.Sparse.eval row17744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17744, Integer.Sparse.eval_collectBalanced, rawRowCheck17744]

theorem rawRowCheck17745 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form7 = rawRow17745 := by decide +kernel

theorem rowCheck17745 : row17745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17745 := by decide +kernel

theorem rowEval17745 (x : Key → ℝ) : Integer.Sparse.eval row17745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17745, Integer.Sparse.eval_collectBalanced, rawRowCheck17745]

theorem rawRowCheck17746 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form7 = rawRow17746 := by decide +kernel

theorem rowCheck17746 : row17746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17746 := by decide +kernel

theorem rowEval17746 (x : Key → ℝ) : Integer.Sparse.eval row17746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17746, Integer.Sparse.eval_collectBalanced, rawRowCheck17746]

theorem rawRowCheck17747 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form7 = rawRow17747 := by decide +kernel

theorem rowCheck17747 : row17747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17747 := by decide +kernel

theorem rowEval17747 (x : Key → ℝ) : Integer.Sparse.eval row17747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17747, Integer.Sparse.eval_collectBalanced, rawRowCheck17747]

theorem rawRowCheck17748 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form7 = rawRow17748 := by decide +kernel

theorem rowCheck17748 : row17748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17748 := by decide +kernel

theorem rowEval17748 (x : Key → ℝ) : Integer.Sparse.eval row17748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17748, Integer.Sparse.eval_collectBalanced, rawRowCheck17748]

theorem rawRowCheck17749 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form7 = rawRow17749 := by decide +kernel

theorem rowCheck17749 : row17749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17749 := by decide +kernel

theorem rowEval17749 (x : Key → ℝ) : Integer.Sparse.eval row17749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17749, Integer.Sparse.eval_collectBalanced, rawRowCheck17749]

theorem rawRowCheck17750 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form7 = rawRow17750 := by decide +kernel

theorem rowCheck17750 : row17750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17750 := by decide +kernel

theorem rowEval17750 (x : Key → ℝ) : Integer.Sparse.eval row17750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17750, Integer.Sparse.eval_collectBalanced, rawRowCheck17750]

theorem rawRowCheck17751 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form7 = rawRow17751 := by decide +kernel

theorem rowCheck17751 : row17751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17751 := by decide +kernel

theorem rowEval17751 (x : Key → ℝ) : Integer.Sparse.eval row17751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17751, Integer.Sparse.eval_collectBalanced, rawRowCheck17751]

theorem rawRowCheck17752 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form7 = rawRow17752 := by decide +kernel

theorem rowCheck17752 : row17752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17752 := by decide +kernel

theorem rowEval17752 (x : Key → ℝ) : Integer.Sparse.eval row17752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17752, Integer.Sparse.eval_collectBalanced, rawRowCheck17752]

theorem rawRowCheck17753 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form7 = rawRow17753 := by decide +kernel

theorem rowCheck17753 : row17753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17753 := by decide +kernel

theorem rowEval17753 (x : Key → ℝ) : Integer.Sparse.eval row17753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17753, Integer.Sparse.eval_collectBalanced, rawRowCheck17753]

theorem rawRowCheck17754 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form7 = rawRow17754 := by decide +kernel

theorem rowCheck17754 : row17754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17754 := by decide +kernel

theorem rowEval17754 (x : Key → ℝ) : Integer.Sparse.eval row17754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17754, Integer.Sparse.eval_collectBalanced, rawRowCheck17754]

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

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval17737 x
  · exact rowEval17738 x
  · exact rowEval17739 x
  · exact rowEval17740 x
  · exact rowEval17741 x
  · exact rowEval17742 x
  · exact rowEval17743 x
  · exact rowEval17744 x
  · exact rowEval17745 x
  · exact rowEval17746 x
  · exact rowEval17747 x
  · exact rowEval17748 x
  · exact rowEval17749 x
  · exact rowEval17750 x
  · exact rowEval17751 x
  · exact rowEval17752 x
  · exact rowEval17753 x
  · exact rowEval17754 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

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

theorem rawRowCheck18129 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form7 = rawRow18129 := by decide +kernel

theorem rowCheck18129 : row18129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18129 := by decide +kernel

theorem rowEval18129 (x : Key → ℝ) : Integer.Sparse.eval row18129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18129, Integer.Sparse.eval_collectBalanced, rawRowCheck18129]

theorem rawRowCheck18130 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form7 = rawRow18130 := by decide +kernel

theorem rowCheck18130 : row18130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18130 := by decide +kernel

theorem rowEval18130 (x : Key → ℝ) : Integer.Sparse.eval row18130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18130, Integer.Sparse.eval_collectBalanced, rawRowCheck18130]

theorem rawRowCheck18131 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form7 = rawRow18131 := by decide +kernel

theorem rowCheck18131 : row18131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18131 := by decide +kernel

theorem rowEval18131 (x : Key → ℝ) : Integer.Sparse.eval row18131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18131, Integer.Sparse.eval_collectBalanced, rawRowCheck18131]

theorem rawRowCheck18132 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form7 = rawRow18132 := by decide +kernel

theorem rowCheck18132 : row18132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18132 := by decide +kernel

theorem rowEval18132 (x : Key → ℝ) : Integer.Sparse.eval row18132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18132, Integer.Sparse.eval_collectBalanced, rawRowCheck18132]

theorem rawRowCheck18133 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form7 = rawRow18133 := by decide +kernel

theorem rowCheck18133 : row18133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18133 := by decide +kernel

theorem rowEval18133 (x : Key → ℝ) : Integer.Sparse.eval row18133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18133, Integer.Sparse.eval_collectBalanced, rawRowCheck18133]

theorem rawRowCheck18134 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form7 = rawRow18134 := by decide +kernel

theorem rowCheck18134 : row18134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18134 := by decide +kernel

theorem rowEval18134 (x : Key → ℝ) : Integer.Sparse.eval row18134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18134, Integer.Sparse.eval_collectBalanced, rawRowCheck18134]

theorem rawRowCheck18135 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form7 = rawRow18135 := by decide +kernel

theorem rowCheck18135 : row18135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18135 := by decide +kernel

theorem rowEval18135 (x : Key → ℝ) : Integer.Sparse.eval row18135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18135, Integer.Sparse.eval_collectBalanced, rawRowCheck18135]

theorem rawRowCheck18136 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form7 = rawRow18136 := by decide +kernel

theorem rowCheck18136 : row18136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18136 := by decide +kernel

theorem rowEval18136 (x : Key → ℝ) : Integer.Sparse.eval row18136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18136, Integer.Sparse.eval_collectBalanced, rawRowCheck18136]

theorem rawRowCheck18137 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form7 = rawRow18137 := by decide +kernel

theorem rowCheck18137 : row18137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18137 := by decide +kernel

theorem rowEval18137 (x : Key → ℝ) : Integer.Sparse.eval row18137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18137, Integer.Sparse.eval_collectBalanced, rawRowCheck18137]

theorem rawRowCheck18138 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow18138 := by decide +kernel

theorem rowCheck18138 : row18138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18138 := by decide +kernel

theorem rowEval18138 (x : Key → ℝ) : Integer.Sparse.eval row18138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18138, Integer.Sparse.eval_collectBalanced, rawRowCheck18138]

theorem rawRowCheck18139 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow18139 := by decide +kernel

theorem rowCheck18139 : row18139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18139 := by decide +kernel

theorem rowEval18139 (x : Key → ℝ) : Integer.Sparse.eval row18139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18139, Integer.Sparse.eval_collectBalanced, rawRowCheck18139]

theorem rawRowCheck18140 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow18140 := by decide +kernel

theorem rowCheck18140 : row18140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18140 := by decide +kernel

theorem rowEval18140 (x : Key → ℝ) : Integer.Sparse.eval row18140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18140, Integer.Sparse.eval_collectBalanced, rawRowCheck18140]

theorem rawRowCheck18141 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form7 = rawRow18141 := by decide +kernel

theorem rowCheck18141 : row18141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18141 := by decide +kernel

theorem rowEval18141 (x : Key → ℝ) : Integer.Sparse.eval row18141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18141, Integer.Sparse.eval_collectBalanced, rawRowCheck18141]

theorem rawRowCheck18142 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form7 = rawRow18142 := by decide +kernel

theorem rowCheck18142 : row18142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18142 := by decide +kernel

theorem rowEval18142 (x : Key → ℝ) : Integer.Sparse.eval row18142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18142, Integer.Sparse.eval_collectBalanced, rawRowCheck18142]

theorem rawRowCheck18143 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form7 = rawRow18143 := by decide +kernel

theorem rowCheck18143 : row18143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18143 := by decide +kernel

theorem rowEval18143 (x : Key → ℝ) : Integer.Sparse.eval row18143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18143, Integer.Sparse.eval_collectBalanced, rawRowCheck18143]

theorem rawRowCheck18144 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form7 = rawRow18144 := by decide +kernel

theorem rowCheck18144 : row18144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18144 := by decide +kernel

theorem rowEval18144 (x : Key → ℝ) : Integer.Sparse.eval row18144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18144, Integer.Sparse.eval_collectBalanced, rawRowCheck18144]

theorem rawRowCheck18145 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow18145 := by decide +kernel

theorem rowCheck18145 : row18145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18145 := by decide +kernel

theorem rowEval18145 (x : Key → ℝ) : Integer.Sparse.eval row18145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18145, Integer.Sparse.eval_collectBalanced, rawRowCheck18145]

theorem rawRowCheck18146 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow18146 := by decide +kernel

theorem rowCheck18146 : row18146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18146 := by decide +kernel

theorem rowEval18146 (x : Key → ℝ) : Integer.Sparse.eval row18146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18146, Integer.Sparse.eval_collectBalanced, rawRowCheck18146]

theorem rawRowCheck18147 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow18147 := by decide +kernel

theorem rowCheck18147 : row18147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18147 := by decide +kernel

theorem rowEval18147 (x : Key → ℝ) : Integer.Sparse.eval row18147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18147, Integer.Sparse.eval_collectBalanced, rawRowCheck18147]

theorem rawRowCheck18148 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow18148 := by decide +kernel

theorem rowCheck18148 : row18148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18148 := by decide +kernel

theorem rowEval18148 (x : Key → ℝ) : Integer.Sparse.eval row18148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18148, Integer.Sparse.eval_collectBalanced, rawRowCheck18148]

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

theorem entryCheck21_7 : entry21_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_7 k)) := by decide +kernel

theorem rowsSound21_7 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval18129 x
  · exact rowEval18130 x
  · exact rowEval18131 x
  · exact rowEval18132 x
  · exact rowEval18133 x
  · exact rowEval18134 x
  · exact rowEval18135 x
  · exact rowEval18136 x
  · exact rowEval18137 x
  · exact rowEval18138 x
  · exact rowEval18139 x
  · exact rowEval18140 x
  · exact rowEval18141 x
  · exact rowEval18142 x
  · exact rowEval18143 x
  · exact rowEval18144 x
  · exact rowEval18145 x
  · exact rowEval18146 x
  · exact rowEval18147 x
  · exact rowEval18148 x

theorem entryEval21_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_7 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck21_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_7]

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

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13845 x
  · exact rowEval13846 x
  · exact rowEval13847 x
  · exact rowEval13848 x
  · exact rowEval13849 x
  · exact rowEval13850 x
  · exact rowEval13851 x
  · exact rowEval13852 x
  · exact rowEval13853 x
  · exact rowEval13854 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

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

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval13885 x
  · exact rowEval13886 x
  · exact rowEval13887 x
  · exact rowEval13888 x
  · exact rowEval13889 x
  · exact rowEval13890 x
  · exact rowEval13891 x
  · exact rowEval13892 x
  · exact rowEval13893 x
  · exact rowEval13894 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

theorem entryCheck7_5 : entry7_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_5 k)) := by decide +kernel

theorem rowsSound7_5 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval13895 x
  · exact rowEval13896 x
  · exact rowEval13897 x
  · exact rowEval13898 x
  · exact rowEval13899 x
  · exact rowEval13900 x
  · exact rowEval13901 x
  · exact rowEval13902 x
  · exact rowEval13903 x
  · exact rowEval13904 x

theorem entryEval7_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_5 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck7_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_5]

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval13905 x
  · exact rowEval13906 x
  · exact rowEval13907 x
  · exact rowEval13908 x
  · exact rowEval13909 x
  · exact rowEval13910 x
  · exact rowEval13911 x
  · exact rowEval13912 x
  · exact rowEval13913 x
  · exact rowEval13914 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval13915 x
  · exact rowEval13916 x
  · exact rowEval13917 x
  · exact rowEval13918 x
  · exact rowEval13919 x
  · exact rowEval13920 x
  · exact rowEval13921 x
  · exact rowEval13922 x
  · exact rowEval13923 x
  · exact rowEval13924 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

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

theorem rawRowCheck14065 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form7 = rawRow14065 := by decide +kernel

theorem rowCheck14065 : row14065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14065 := by decide +kernel

theorem rowEval14065 (x : Key → ℝ) : Integer.Sparse.eval row14065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14065, Integer.Sparse.eval_collectBalanced, rawRowCheck14065]

theorem rawRowCheck14066 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form7 = rawRow14066 := by decide +kernel

theorem rowCheck14066 : row14066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14066 := by decide +kernel

theorem rowEval14066 (x : Key → ℝ) : Integer.Sparse.eval row14066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14066, Integer.Sparse.eval_collectBalanced, rawRowCheck14066]

theorem rawRowCheck14067 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form7 = rawRow14067 := by decide +kernel

theorem rowCheck14067 : row14067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14067 := by decide +kernel

theorem rowEval14067 (x : Key → ℝ) : Integer.Sparse.eval row14067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14067, Integer.Sparse.eval_collectBalanced, rawRowCheck14067]

theorem rawRowCheck14068 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14068 := by decide +kernel

theorem rowCheck14068 : row14068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14068 := by decide +kernel

theorem rowEval14068 (x : Key → ℝ) : Integer.Sparse.eval row14068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14068, Integer.Sparse.eval_collectBalanced, rawRowCheck14068]

theorem rawRowCheck14069 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form7 = rawRow14069 := by decide +kernel

theorem rowCheck14069 : row14069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14069 := by decide +kernel

theorem rowEval14069 (x : Key → ℝ) : Integer.Sparse.eval row14069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14069, Integer.Sparse.eval_collectBalanced, rawRowCheck14069]

theorem rawRowCheck14070 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form7 = rawRow14070 := by decide +kernel

theorem rowCheck14070 : row14070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14070 := by decide +kernel

theorem rowEval14070 (x : Key → ℝ) : Integer.Sparse.eval row14070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14070, Integer.Sparse.eval_collectBalanced, rawRowCheck14070]

theorem rawRowCheck14071 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form7 = rawRow14071 := by decide +kernel

theorem rowCheck14071 : row14071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14071 := by decide +kernel

theorem rowEval14071 (x : Key → ℝ) : Integer.Sparse.eval row14071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14071, Integer.Sparse.eval_collectBalanced, rawRowCheck14071]

theorem rawRowCheck14072 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form7 = rawRow14072 := by decide +kernel

theorem rowCheck14072 : row14072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14072 := by decide +kernel

theorem rowEval14072 (x : Key → ℝ) : Integer.Sparse.eval row14072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14072, Integer.Sparse.eval_collectBalanced, rawRowCheck14072]

theorem rawRowCheck14073 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form7 = rawRow14073 := by decide +kernel

theorem rowCheck14073 : row14073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14073 := by decide +kernel

theorem rowEval14073 (x : Key → ℝ) : Integer.Sparse.eval row14073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14073, Integer.Sparse.eval_collectBalanced, rawRowCheck14073]

theorem rawRowCheck14074 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form7 = rawRow14074 := by decide +kernel

theorem rowCheck14074 : row14074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14074 := by decide +kernel

theorem rowEval14074 (x : Key → ℝ) : Integer.Sparse.eval row14074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14074, Integer.Sparse.eval_collectBalanced, rawRowCheck14074]

theorem rawRowCheck14075 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form7 = rawRow14075 := by decide +kernel

theorem rowCheck14075 : row14075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14075 := by decide +kernel

theorem rowEval14075 (x : Key → ℝ) : Integer.Sparse.eval row14075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14075, Integer.Sparse.eval_collectBalanced, rawRowCheck14075]

theorem rawRowCheck14076 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form7 = rawRow14076 := by decide +kernel

theorem rowCheck14076 : row14076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14076 := by decide +kernel

theorem rowEval14076 (x : Key → ℝ) : Integer.Sparse.eval row14076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14076, Integer.Sparse.eval_collectBalanced, rawRowCheck14076]

theorem rawRowCheck14077 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form7 = rawRow14077 := by decide +kernel

theorem rowCheck14077 : row14077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14077 := by decide +kernel

theorem rowEval14077 (x : Key → ℝ) : Integer.Sparse.eval row14077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14077, Integer.Sparse.eval_collectBalanced, rawRowCheck14077]

theorem rawRowCheck14078 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form7 = rawRow14078 := by decide +kernel

theorem rowCheck14078 : row14078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14078 := by decide +kernel

theorem rowEval14078 (x : Key → ℝ) : Integer.Sparse.eval row14078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14078, Integer.Sparse.eval_collectBalanced, rawRowCheck14078]

theorem rawRowCheck14079 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form7 = rawRow14079 := by decide +kernel

theorem rowCheck14079 : row14079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14079 := by decide +kernel

theorem rowEval14079 (x : Key → ℝ) : Integer.Sparse.eval row14079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14079, Integer.Sparse.eval_collectBalanced, rawRowCheck14079]

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

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval14065 x
  · exact rowEval14066 x
  · exact rowEval14067 x
  · exact rowEval14068 x
  · exact rowEval14069 x
  · exact rowEval14070 x
  · exact rowEval14071 x
  · exact rowEval14072 x
  · exact rowEval14073 x
  · exact rowEval14074 x
  · exact rowEval14075 x
  · exact rowEval14076 x
  · exact rowEval14077 x
  · exact rowEval14078 x
  · exact rowEval14079 x
  · exact rowEval14080 x
  · exact rowEval14081 x
  · exact rowEval14082 x
  · exact rowEval14083 x
  · exact rowEval14084 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

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

theorem entryCheck9_7 : entry9_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_7 k)) := by decide +kernel

theorem rowsSound9_7 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval14175 x
  · exact rowEval14176 x
  · exact rowEval14177 x
  · exact rowEval14178 x
  · exact rowEval14179 x
  · exact rowEval14180 x
  · exact rowEval14181 x
  · exact rowEval14182 x
  · exact rowEval14183 x
  · exact rowEval14184 x

theorem entryEval9_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_7 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck9_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_7]

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

theorem entryEvalRow7_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 7 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 7).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval7_0 B hB
  · exact entryEval7_1 B hB
  · exact entryEval7_2 B hB
  · exact entryEval7_3 B hB
  · exact entryEval7_4 B hB
  · exact entryEval7_5 B hB
  · exact entryEval7_6 B hB
  · exact entryEval7_7 B hB
  · exact (entryEval8_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e_oai
