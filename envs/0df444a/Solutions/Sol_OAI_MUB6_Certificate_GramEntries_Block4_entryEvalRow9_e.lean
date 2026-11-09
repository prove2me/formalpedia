-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:59:12.150171+00:00
-- url     : https://prove2.me/submissions/f54f2136-0c9a-4d22-b715-4ed18493a4c5

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_9_e

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

theorem rawRowCheck14105 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0 = rawRow14105 := by decide +kernel

theorem rowCheck14105 : row14105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14105 := by decide +kernel

theorem rowEval14105 (x : Key → ℝ) : Integer.Sparse.eval row14105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14105, Integer.Sparse.eval_collectBalanced, rawRowCheck14105]

theorem rawRowCheck14106 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0 = rawRow14106 := by decide +kernel

theorem rowCheck14106 : row14106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14106 := by decide +kernel

theorem rowEval14106 (x : Key → ℝ) : Integer.Sparse.eval row14106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14106, Integer.Sparse.eval_collectBalanced, rawRowCheck14106]

theorem rawRowCheck14107 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0 = rawRow14107 := by decide +kernel

theorem rowCheck14107 : row14107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14107 := by decide +kernel

theorem rowEval14107 (x : Key → ℝ) : Integer.Sparse.eval row14107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14107, Integer.Sparse.eval_collectBalanced, rawRowCheck14107]

theorem rawRowCheck14108 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0 = rawRow14108 := by decide +kernel

theorem rowCheck14108 : row14108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14108 := by decide +kernel

theorem rowEval14108 (x : Key → ℝ) : Integer.Sparse.eval row14108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14108, Integer.Sparse.eval_collectBalanced, rawRowCheck14108]

theorem rawRowCheck14109 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0 = rawRow14109 := by decide +kernel

theorem rowCheck14109 : row14109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14109 := by decide +kernel

theorem rowEval14109 (x : Key → ℝ) : Integer.Sparse.eval row14109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14109, Integer.Sparse.eval_collectBalanced, rawRowCheck14109]

theorem rawRowCheck14110 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0 = rawRow14110 := by decide +kernel

theorem rowCheck14110 : row14110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14110 := by decide +kernel

theorem rowEval14110 (x : Key → ℝ) : Integer.Sparse.eval row14110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14110, Integer.Sparse.eval_collectBalanced, rawRowCheck14110]

theorem rawRowCheck14111 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow14111 := by decide +kernel

theorem rowCheck14111 : row14111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14111 := by decide +kernel

theorem rowEval14111 (x : Key → ℝ) : Integer.Sparse.eval row14111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14111, Integer.Sparse.eval_collectBalanced, rawRowCheck14111]

theorem rawRowCheck14112 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow14112 := by decide +kernel

theorem rowCheck14112 : row14112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14112 := by decide +kernel

theorem rowEval14112 (x : Key → ℝ) : Integer.Sparse.eval row14112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14112, Integer.Sparse.eval_collectBalanced, rawRowCheck14112]

theorem rawRowCheck14113 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow14113 := by decide +kernel

theorem rowCheck14113 : row14113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14113 := by decide +kernel

theorem rowEval14113 (x : Key → ℝ) : Integer.Sparse.eval row14113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14113, Integer.Sparse.eval_collectBalanced, rawRowCheck14113]

theorem rawRowCheck14114 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow14114 := by decide +kernel

theorem rowCheck14114 : row14114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14114 := by decide +kernel

theorem rowEval14114 (x : Key → ℝ) : Integer.Sparse.eval row14114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14114, Integer.Sparse.eval_collectBalanced, rawRowCheck14114]

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

theorem rawRowCheck14145 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4 = rawRow14145 := by decide +kernel

theorem rowCheck14145 : row14145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14145 := by decide +kernel

theorem rowEval14145 (x : Key → ℝ) : Integer.Sparse.eval row14145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14145, Integer.Sparse.eval_collectBalanced, rawRowCheck14145]

theorem rawRowCheck14146 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4 = rawRow14146 := by decide +kernel

theorem rowCheck14146 : row14146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14146 := by decide +kernel

theorem rowEval14146 (x : Key → ℝ) : Integer.Sparse.eval row14146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14146, Integer.Sparse.eval_collectBalanced, rawRowCheck14146]

theorem rawRowCheck14147 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4 = rawRow14147 := by decide +kernel

theorem rowCheck14147 : row14147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14147 := by decide +kernel

theorem rowEval14147 (x : Key → ℝ) : Integer.Sparse.eval row14147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14147, Integer.Sparse.eval_collectBalanced, rawRowCheck14147]

theorem rawRowCheck14148 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4 = rawRow14148 := by decide +kernel

theorem rowCheck14148 : row14148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14148 := by decide +kernel

theorem rowEval14148 (x : Key → ℝ) : Integer.Sparse.eval row14148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14148, Integer.Sparse.eval_collectBalanced, rawRowCheck14148]

theorem rawRowCheck14149 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4 = rawRow14149 := by decide +kernel

theorem rowCheck14149 : row14149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14149 := by decide +kernel

theorem rowEval14149 (x : Key → ℝ) : Integer.Sparse.eval row14149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14149, Integer.Sparse.eval_collectBalanced, rawRowCheck14149]

theorem rawRowCheck14150 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4 = rawRow14150 := by decide +kernel

theorem rowCheck14150 : row14150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14150 := by decide +kernel

theorem rowEval14150 (x : Key → ℝ) : Integer.Sparse.eval row14150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14150, Integer.Sparse.eval_collectBalanced, rawRowCheck14150]

theorem rawRowCheck14151 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow14151 := by decide +kernel

theorem rowCheck14151 : row14151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14151 := by decide +kernel

theorem rowEval14151 (x : Key → ℝ) : Integer.Sparse.eval row14151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14151, Integer.Sparse.eval_collectBalanced, rawRowCheck14151]

theorem rawRowCheck14152 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow14152 := by decide +kernel

theorem rowCheck14152 : row14152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14152 := by decide +kernel

theorem rowEval14152 (x : Key → ℝ) : Integer.Sparse.eval row14152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14152, Integer.Sparse.eval_collectBalanced, rawRowCheck14152]

theorem rawRowCheck14153 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow14153 := by decide +kernel

theorem rowCheck14153 : row14153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14153 := by decide +kernel

theorem rowEval14153 (x : Key → ℝ) : Integer.Sparse.eval row14153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14153, Integer.Sparse.eval_collectBalanced, rawRowCheck14153]

theorem rawRowCheck14154 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow14154 := by decide +kernel

theorem rowCheck14154 : row14154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14154 := by decide +kernel

theorem rowEval14154 (x : Key → ℝ) : Integer.Sparse.eval row14154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14154, Integer.Sparse.eval_collectBalanced, rawRowCheck14154]

theorem rawRowCheck14155 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5 = rawRow14155 := by decide +kernel

theorem rowCheck14155 : row14155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14155 := by decide +kernel

theorem rowEval14155 (x : Key → ℝ) : Integer.Sparse.eval row14155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14155, Integer.Sparse.eval_collectBalanced, rawRowCheck14155]

theorem rawRowCheck14156 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5 = rawRow14156 := by decide +kernel

theorem rowCheck14156 : row14156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14156 := by decide +kernel

theorem rowEval14156 (x : Key → ℝ) : Integer.Sparse.eval row14156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14156, Integer.Sparse.eval_collectBalanced, rawRowCheck14156]

theorem rawRowCheck14157 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5 = rawRow14157 := by decide +kernel

theorem rowCheck14157 : row14157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14157 := by decide +kernel

theorem rowEval14157 (x : Key → ℝ) : Integer.Sparse.eval row14157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14157, Integer.Sparse.eval_collectBalanced, rawRowCheck14157]

theorem rawRowCheck14158 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5 = rawRow14158 := by decide +kernel

theorem rowCheck14158 : row14158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14158 := by decide +kernel

theorem rowEval14158 (x : Key → ℝ) : Integer.Sparse.eval row14158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14158, Integer.Sparse.eval_collectBalanced, rawRowCheck14158]

theorem rawRowCheck14159 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5 = rawRow14159 := by decide +kernel

theorem rowCheck14159 : row14159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14159 := by decide +kernel

theorem rowEval14159 (x : Key → ℝ) : Integer.Sparse.eval row14159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14159, Integer.Sparse.eval_collectBalanced, rawRowCheck14159]

theorem rawRowCheck14160 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5 = rawRow14160 := by decide +kernel

theorem rowCheck14160 : row14160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14160 := by decide +kernel

theorem rowEval14160 (x : Key → ℝ) : Integer.Sparse.eval row14160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14160, Integer.Sparse.eval_collectBalanced, rawRowCheck14160]

theorem rawRowCheck14161 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow14161 := by decide +kernel

theorem rowCheck14161 : row14161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14161 := by decide +kernel

theorem rowEval14161 (x : Key → ℝ) : Integer.Sparse.eval row14161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14161, Integer.Sparse.eval_collectBalanced, rawRowCheck14161]

theorem rawRowCheck14162 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow14162 := by decide +kernel

theorem rowCheck14162 : row14162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14162 := by decide +kernel

theorem rowEval14162 (x : Key → ℝ) : Integer.Sparse.eval row14162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14162, Integer.Sparse.eval_collectBalanced, rawRowCheck14162]

theorem rawRowCheck14163 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow14163 := by decide +kernel

theorem rowCheck14163 : row14163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14163 := by decide +kernel

theorem rowEval14163 (x : Key → ℝ) : Integer.Sparse.eval row14163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14163, Integer.Sparse.eval_collectBalanced, rawRowCheck14163]

theorem rawRowCheck14164 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow14164 := by decide +kernel

theorem rowCheck14164 : row14164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14164 := by decide +kernel

theorem rowEval14164 (x : Key → ℝ) : Integer.Sparse.eval row14164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14164, Integer.Sparse.eval_collectBalanced, rawRowCheck14164]

theorem rawRowCheck14165 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form6 = rawRow14165 := by decide +kernel

theorem rowCheck14165 : row14165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14165 := by decide +kernel

theorem rowEval14165 (x : Key → ℝ) : Integer.Sparse.eval row14165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14165, Integer.Sparse.eval_collectBalanced, rawRowCheck14165]

theorem rawRowCheck14166 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form6 = rawRow14166 := by decide +kernel

theorem rowCheck14166 : row14166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14166 := by decide +kernel

theorem rowEval14166 (x : Key → ℝ) : Integer.Sparse.eval row14166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14166, Integer.Sparse.eval_collectBalanced, rawRowCheck14166]

theorem rawRowCheck14167 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form6 = rawRow14167 := by decide +kernel

theorem rowCheck14167 : row14167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14167 := by decide +kernel

theorem rowEval14167 (x : Key → ℝ) : Integer.Sparse.eval row14167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14167, Integer.Sparse.eval_collectBalanced, rawRowCheck14167]

theorem rawRowCheck14168 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form6 = rawRow14168 := by decide +kernel

theorem rowCheck14168 : row14168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14168 := by decide +kernel

theorem rowEval14168 (x : Key → ℝ) : Integer.Sparse.eval row14168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14168, Integer.Sparse.eval_collectBalanced, rawRowCheck14168]

theorem rawRowCheck14169 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form6 = rawRow14169 := by decide +kernel

theorem rowCheck14169 : row14169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14169 := by decide +kernel

theorem rowEval14169 (x : Key → ℝ) : Integer.Sparse.eval row14169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14169, Integer.Sparse.eval_collectBalanced, rawRowCheck14169]

theorem rawRowCheck14170 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form6 = rawRow14170 := by decide +kernel

theorem rowCheck14170 : row14170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14170 := by decide +kernel

theorem rowEval14170 (x : Key → ℝ) : Integer.Sparse.eval row14170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14170, Integer.Sparse.eval_collectBalanced, rawRowCheck14170]

theorem rawRowCheck14171 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form6 = rawRow14171 := by decide +kernel

theorem rowCheck14171 : row14171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14171 := by decide +kernel

theorem rowEval14171 (x : Key → ℝ) : Integer.Sparse.eval row14171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14171, Integer.Sparse.eval_collectBalanced, rawRowCheck14171]

theorem rawRowCheck14172 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form6 = rawRow14172 := by decide +kernel

theorem rowCheck14172 : row14172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14172 := by decide +kernel

theorem rowEval14172 (x : Key → ℝ) : Integer.Sparse.eval row14172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14172, Integer.Sparse.eval_collectBalanced, rawRowCheck14172]

theorem rawRowCheck14173 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form6 = rawRow14173 := by decide +kernel

theorem rowCheck14173 : row14173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14173 := by decide +kernel

theorem rowEval14173 (x : Key → ℝ) : Integer.Sparse.eval row14173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14173, Integer.Sparse.eval_collectBalanced, rawRowCheck14173]

theorem rawRowCheck14174 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form6 = rawRow14174 := by decide +kernel

theorem rowCheck14174 : row14174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14174 := by decide +kernel

theorem rowEval14174 (x : Key → ℝ) : Integer.Sparse.eval row14174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14174, Integer.Sparse.eval_collectBalanced, rawRowCheck14174]

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

theorem rawRowCheck14185 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form8 = rawRow14185 := by decide +kernel

theorem rowCheck14185 : row14185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14185 := by decide +kernel

theorem rowEval14185 (x : Key → ℝ) : Integer.Sparse.eval row14185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14185, Integer.Sparse.eval_collectBalanced, rawRowCheck14185]

theorem rawRowCheck14186 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form8 = rawRow14186 := by decide +kernel

theorem rowCheck14186 : row14186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14186 := by decide +kernel

theorem rowEval14186 (x : Key → ℝ) : Integer.Sparse.eval row14186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14186, Integer.Sparse.eval_collectBalanced, rawRowCheck14186]

theorem rawRowCheck14187 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form8 = rawRow14187 := by decide +kernel

theorem rowCheck14187 : row14187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14187 := by decide +kernel

theorem rowEval14187 (x : Key → ℝ) : Integer.Sparse.eval row14187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14187, Integer.Sparse.eval_collectBalanced, rawRowCheck14187]

theorem rawRowCheck14188 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form8 = rawRow14188 := by decide +kernel

theorem rowCheck14188 : row14188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14188 := by decide +kernel

theorem rowEval14188 (x : Key → ℝ) : Integer.Sparse.eval row14188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14188, Integer.Sparse.eval_collectBalanced, rawRowCheck14188]

theorem rawRowCheck14189 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form8 = rawRow14189 := by decide +kernel

theorem rowCheck14189 : row14189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14189 := by decide +kernel

theorem rowEval14189 (x : Key → ℝ) : Integer.Sparse.eval row14189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14189, Integer.Sparse.eval_collectBalanced, rawRowCheck14189]

theorem rawRowCheck14190 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form8 = rawRow14190 := by decide +kernel

theorem rowCheck14190 : row14190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14190 := by decide +kernel

theorem rowEval14190 (x : Key → ℝ) : Integer.Sparse.eval row14190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14190, Integer.Sparse.eval_collectBalanced, rawRowCheck14190]

theorem rawRowCheck14191 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow14191 := by decide +kernel

theorem rowCheck14191 : row14191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14191 := by decide +kernel

theorem rowEval14191 (x : Key → ℝ) : Integer.Sparse.eval row14191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14191, Integer.Sparse.eval_collectBalanced, rawRowCheck14191]

theorem rawRowCheck14192 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow14192 := by decide +kernel

theorem rowCheck14192 : row14192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14192 := by decide +kernel

theorem rowEval14192 (x : Key → ℝ) : Integer.Sparse.eval row14192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14192, Integer.Sparse.eval_collectBalanced, rawRowCheck14192]

theorem rawRowCheck14193 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow14193 := by decide +kernel

theorem rowCheck14193 : row14193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14193 := by decide +kernel

theorem rowEval14193 (x : Key → ℝ) : Integer.Sparse.eval row14193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14193, Integer.Sparse.eval_collectBalanced, rawRowCheck14193]

theorem rawRowCheck14194 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form8 = rawRow14194 := by decide +kernel

theorem rowCheck14194 : row14194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14194 := by decide +kernel

theorem rowEval14194 (x : Key → ℝ) : Integer.Sparse.eval row14194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14194, Integer.Sparse.eval_collectBalanced, rawRowCheck14194]

theorem rawRowCheck14195 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form9 = rawRow14195 := by decide +kernel

theorem rowCheck14195 : row14195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14195 := by decide +kernel

theorem rowEval14195 (x : Key → ℝ) : Integer.Sparse.eval row14195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14195, Integer.Sparse.eval_collectBalanced, rawRowCheck14195]

theorem rawRowCheck14196 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form9 = rawRow14196 := by decide +kernel

theorem rowCheck14196 : row14196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14196 := by decide +kernel

theorem rowEval14196 (x : Key → ℝ) : Integer.Sparse.eval row14196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14196, Integer.Sparse.eval_collectBalanced, rawRowCheck14196]

theorem rawRowCheck14197 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form9 = rawRow14197 := by decide +kernel

theorem rowCheck14197 : row14197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14197 := by decide +kernel

theorem rowEval14197 (x : Key → ℝ) : Integer.Sparse.eval row14197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14197, Integer.Sparse.eval_collectBalanced, rawRowCheck14197]

theorem rawRowCheck14198 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form9 = rawRow14198 := by decide +kernel

theorem rowCheck14198 : row14198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14198 := by decide +kernel

theorem rowEval14198 (x : Key → ℝ) : Integer.Sparse.eval row14198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14198, Integer.Sparse.eval_collectBalanced, rawRowCheck14198]

theorem rawRowCheck14199 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form9 = rawRow14199 := by decide +kernel

theorem rowCheck14199 : row14199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14199 := by decide +kernel

theorem rowEval14199 (x : Key → ℝ) : Integer.Sparse.eval row14199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14199, Integer.Sparse.eval_collectBalanced, rawRowCheck14199]

theorem rawRowCheck14200 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form9 = rawRow14200 := by decide +kernel

theorem rowCheck14200 : row14200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14200 := by decide +kernel

theorem rowEval14200 (x : Key → ℝ) : Integer.Sparse.eval row14200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14200, Integer.Sparse.eval_collectBalanced, rawRowCheck14200]

theorem rawRowCheck14201 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow14201 := by decide +kernel

theorem rowCheck14201 : row14201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14201 := by decide +kernel

theorem rowEval14201 (x : Key → ℝ) : Integer.Sparse.eval row14201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14201, Integer.Sparse.eval_collectBalanced, rawRowCheck14201]

theorem rawRowCheck14202 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow14202 := by decide +kernel

theorem rowCheck14202 : row14202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14202 := by decide +kernel

theorem rowEval14202 (x : Key → ℝ) : Integer.Sparse.eval row14202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14202, Integer.Sparse.eval_collectBalanced, rawRowCheck14202]

theorem rawRowCheck14203 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow14203 := by decide +kernel

theorem rowCheck14203 : row14203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14203 := by decide +kernel

theorem rowEval14203 (x : Key → ℝ) : Integer.Sparse.eval row14203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14203, Integer.Sparse.eval_collectBalanced, rawRowCheck14203]

theorem rawRowCheck14204 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form9 = rawRow14204 := by decide +kernel

theorem rowCheck14204 : row14204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14204 := by decide +kernel

theorem rowEval14204 (x : Key → ℝ) : Integer.Sparse.eval row14204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14204, Integer.Sparse.eval_collectBalanced, rawRowCheck14204]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14529 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form9 = rawRow14529 := by decide +kernel

theorem rowCheck14529 : row14529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14529 := by decide +kernel

theorem rowEval14529 (x : Key → ℝ) : Integer.Sparse.eval row14529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14529, Integer.Sparse.eval_collectBalanced, rawRowCheck14529]

theorem rawRowCheck14530 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form9 = rawRow14530 := by decide +kernel

theorem rowCheck14530 : row14530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14530 := by decide +kernel

theorem rowEval14530 (x : Key → ℝ) : Integer.Sparse.eval row14530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14530, Integer.Sparse.eval_collectBalanced, rawRowCheck14530]

theorem rawRowCheck14531 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form9 = rawRow14531 := by decide +kernel

theorem rowCheck14531 : row14531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14531 := by decide +kernel

theorem rowEval14531 (x : Key → ℝ) : Integer.Sparse.eval row14531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14531, Integer.Sparse.eval_collectBalanced, rawRowCheck14531]

theorem rawRowCheck14532 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form9 = rawRow14532 := by decide +kernel

theorem rowCheck14532 : row14532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14532 := by decide +kernel

theorem rowEval14532 (x : Key → ℝ) : Integer.Sparse.eval row14532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14532, Integer.Sparse.eval_collectBalanced, rawRowCheck14532]

theorem rawRowCheck14533 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form9 = rawRow14533 := by decide +kernel

theorem rowCheck14533 : row14533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14533 := by decide +kernel

theorem rowEval14533 (x : Key → ℝ) : Integer.Sparse.eval row14533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14533, Integer.Sparse.eval_collectBalanced, rawRowCheck14533]

theorem rawRowCheck14534 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form9 = rawRow14534 := by decide +kernel

theorem rowCheck14534 : row14534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14534 := by decide +kernel

theorem rowEval14534 (x : Key → ℝ) : Integer.Sparse.eval row14534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14534, Integer.Sparse.eval_collectBalanced, rawRowCheck14534]

theorem rawRowCheck14535 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form9 = rawRow14535 := by decide +kernel

theorem rowCheck14535 : row14535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14535 := by decide +kernel

theorem rowEval14535 (x : Key → ℝ) : Integer.Sparse.eval row14535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14535, Integer.Sparse.eval_collectBalanced, rawRowCheck14535]

theorem rawRowCheck14536 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form9 = rawRow14536 := by decide +kernel

theorem rowCheck14536 : row14536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14536 := by decide +kernel

theorem rowEval14536 (x : Key → ℝ) : Integer.Sparse.eval row14536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14536, Integer.Sparse.eval_collectBalanced, rawRowCheck14536]

theorem rawRowCheck14537 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form9 = rawRow14537 := by decide +kernel

theorem rowCheck14537 : row14537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14537 := by decide +kernel

theorem rowEval14537 (x : Key → ℝ) : Integer.Sparse.eval row14537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14537, Integer.Sparse.eval_collectBalanced, rawRowCheck14537]

theorem rawRowCheck14538 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form9 = rawRow14538 := by decide +kernel

theorem rowCheck14538 : row14538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14538 := by decide +kernel

theorem rowEval14538 (x : Key → ℝ) : Integer.Sparse.eval row14538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14538, Integer.Sparse.eval_collectBalanced, rawRowCheck14538]

theorem rawRowCheck14539 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form9 = rawRow14539 := by decide +kernel

theorem rowCheck14539 : row14539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14539 := by decide +kernel

theorem rowEval14539 (x : Key → ℝ) : Integer.Sparse.eval row14539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14539, Integer.Sparse.eval_collectBalanced, rawRowCheck14539]

theorem rawRowCheck14540 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form9 = rawRow14540 := by decide +kernel

theorem rowCheck14540 : row14540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14540 := by decide +kernel

theorem rowEval14540 (x : Key → ℝ) : Integer.Sparse.eval row14540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14540, Integer.Sparse.eval_collectBalanced, rawRowCheck14540]

theorem rawRowCheck14541 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form9 = rawRow14541 := by decide +kernel

theorem rowCheck14541 : row14541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14541 := by decide +kernel

theorem rowEval14541 (x : Key → ℝ) : Integer.Sparse.eval row14541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14541, Integer.Sparse.eval_collectBalanced, rawRowCheck14541]

theorem rawRowCheck14542 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form9 = rawRow14542 := by decide +kernel

theorem rowCheck14542 : row14542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14542 := by decide +kernel

theorem rowEval14542 (x : Key → ℝ) : Integer.Sparse.eval row14542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14542, Integer.Sparse.eval_collectBalanced, rawRowCheck14542]

theorem rawRowCheck14543 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form9 = rawRow14543 := by decide +kernel

theorem rowCheck14543 : row14543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14543 := by decide +kernel

theorem rowEval14543 (x : Key → ℝ) : Integer.Sparse.eval row14543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14543, Integer.Sparse.eval_collectBalanced, rawRowCheck14543]

theorem rawRowCheck14544 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form9 = rawRow14544 := by decide +kernel

theorem rowCheck14544 : row14544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14544 := by decide +kernel

theorem rowEval14544 (x : Key → ℝ) : Integer.Sparse.eval row14544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14544, Integer.Sparse.eval_collectBalanced, rawRowCheck14544]

theorem rawRowCheck14545 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form9 = rawRow14545 := by decide +kernel

theorem rowCheck14545 : row14545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14545 := by decide +kernel

theorem rowEval14545 (x : Key → ℝ) : Integer.Sparse.eval row14545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14545, Integer.Sparse.eval_collectBalanced, rawRowCheck14545]

theorem rawRowCheck14546 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form9 = rawRow14546 := by decide +kernel

theorem rowCheck14546 : row14546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14546 := by decide +kernel

theorem rowEval14546 (x : Key → ℝ) : Integer.Sparse.eval row14546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14546, Integer.Sparse.eval_collectBalanced, rawRowCheck14546]

theorem rawRowCheck14547 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form9 = rawRow14547 := by decide +kernel

theorem rowCheck14547 : row14547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14547 := by decide +kernel

theorem rowEval14547 (x : Key → ℝ) : Integer.Sparse.eval row14547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14547, Integer.Sparse.eval_collectBalanced, rawRowCheck14547]

theorem rawRowCheck14548 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form9 = rawRow14548 := by decide +kernel

theorem rowCheck14548 : row14548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14548 := by decide +kernel

theorem rowEval14548 (x : Key → ℝ) : Integer.Sparse.eval row14548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14548, Integer.Sparse.eval_collectBalanced, rawRowCheck14548]

theorem rawRowCheck14549 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form9 = rawRow14549 := by decide +kernel

theorem rowCheck14549 : row14549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14549 := by decide +kernel

theorem rowEval14549 (x : Key → ℝ) : Integer.Sparse.eval row14549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14549, Integer.Sparse.eval_collectBalanced, rawRowCheck14549]

theorem rawRowCheck14550 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form9 = rawRow14550 := by decide +kernel

theorem rowCheck14550 : row14550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14550 := by decide +kernel

theorem rowEval14550 (x : Key → ℝ) : Integer.Sparse.eval row14550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14550, Integer.Sparse.eval_collectBalanced, rawRowCheck14550]

theorem rawRowCheck14551 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form9 = rawRow14551 := by decide +kernel

theorem rowCheck14551 : row14551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14551 := by decide +kernel

theorem rowEval14551 (x : Key → ℝ) : Integer.Sparse.eval row14551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14551, Integer.Sparse.eval_collectBalanced, rawRowCheck14551]

theorem rawRowCheck14552 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form9 = rawRow14552 := by decide +kernel

theorem rowCheck14552 : row14552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14552 := by decide +kernel

theorem rowEval14552 (x : Key → ℝ) : Integer.Sparse.eval row14552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14552, Integer.Sparse.eval_collectBalanced, rawRowCheck14552]

theorem rawRowCheck14553 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form9 = rawRow14553 := by decide +kernel

theorem rowCheck14553 : row14553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14553 := by decide +kernel

theorem rowEval14553 (x : Key → ℝ) : Integer.Sparse.eval row14553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14553, Integer.Sparse.eval_collectBalanced, rawRowCheck14553]

theorem rawRowCheck14554 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form9 = rawRow14554 := by decide +kernel

theorem rowCheck14554 : row14554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14554 := by decide +kernel

theorem rowEval14554 (x : Key → ℝ) : Integer.Sparse.eval row14554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14554, Integer.Sparse.eval_collectBalanced, rawRowCheck14554]

theorem rawRowCheck14555 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form9 = rawRow14555 := by decide +kernel

theorem rowCheck14555 : row14555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14555 := by decide +kernel

theorem rowEval14555 (x : Key → ℝ) : Integer.Sparse.eval row14555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14555, Integer.Sparse.eval_collectBalanced, rawRowCheck14555]

theorem rawRowCheck14556 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form9 = rawRow14556 := by decide +kernel

theorem rowCheck14556 : row14556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14556 := by decide +kernel

theorem rowEval14556 (x : Key → ℝ) : Integer.Sparse.eval row14556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14556, Integer.Sparse.eval_collectBalanced, rawRowCheck14556]

theorem rawRowCheck14557 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form9 = rawRow14557 := by decide +kernel

theorem rowCheck14557 : row14557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14557 := by decide +kernel

theorem rowEval14557 (x : Key → ℝ) : Integer.Sparse.eval row14557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14557, Integer.Sparse.eval_collectBalanced, rawRowCheck14557]

theorem rawRowCheck14558 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form9 = rawRow14558 := by decide +kernel

theorem rowCheck14558 : row14558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14558 := by decide +kernel

theorem rowEval14558 (x : Key → ℝ) : Integer.Sparse.eval row14558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14558, Integer.Sparse.eval_collectBalanced, rawRowCheck14558]

theorem rawRowCheck14559 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form9 = rawRow14559 := by decide +kernel

theorem rowCheck14559 : row14559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14559 := by decide +kernel

theorem rowEval14559 (x : Key → ℝ) : Integer.Sparse.eval row14559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14559, Integer.Sparse.eval_collectBalanced, rawRowCheck14559]

theorem rawRowCheck14560 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form9 = rawRow14560 := by decide +kernel

theorem rowCheck14560 : row14560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14560 := by decide +kernel

theorem rowEval14560 (x : Key → ℝ) : Integer.Sparse.eval row14560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14560, Integer.Sparse.eval_collectBalanced, rawRowCheck14560]

theorem rawRowCheck14561 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form9 = rawRow14561 := by decide +kernel

theorem rowCheck14561 : row14561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14561 := by decide +kernel

theorem rowEval14561 (x : Key → ℝ) : Integer.Sparse.eval row14561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14561, Integer.Sparse.eval_collectBalanced, rawRowCheck14561]

theorem rawRowCheck14562 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form9 = rawRow14562 := by decide +kernel

theorem rowCheck14562 : row14562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14562 := by decide +kernel

theorem rowEval14562 (x : Key → ℝ) : Integer.Sparse.eval row14562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14562, Integer.Sparse.eval_collectBalanced, rawRowCheck14562]

theorem rawRowCheck14563 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form9 = rawRow14563 := by decide +kernel

theorem rowCheck14563 : row14563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14563 := by decide +kernel

theorem rowEval14563 (x : Key → ℝ) : Integer.Sparse.eval row14563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14563, Integer.Sparse.eval_collectBalanced, rawRowCheck14563]

theorem rawRowCheck14564 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form9 = rawRow14564 := by decide +kernel

theorem rowCheck14564 : row14564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14564 := by decide +kernel

theorem rowEval14564 (x : Key → ℝ) : Integer.Sparse.eval row14564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14564, Integer.Sparse.eval_collectBalanced, rawRowCheck14564]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval14529 x
  · exact rowEval14530 x
  · exact rowEval14531 x
  · exact rowEval14532 x
  · exact rowEval14533 x
  · exact rowEval14534 x
  · exact rowEval14535 x
  · exact rowEval14536 x
  · exact rowEval14537 x
  · exact rowEval14538 x
  · exact rowEval14539 x
  · exact rowEval14540 x
  · exact rowEval14541 x
  · exact rowEval14542 x
  · exact rowEval14543 x
  · exact rowEval14544 x
  · exact rowEval14545 x
  · exact rowEval14546 x
  · exact rowEval14547 x
  · exact rowEval14548 x
  · exact rowEval14549 x
  · exact rowEval14550 x
  · exact rowEval14551 x
  · exact rowEval14552 x
  · exact rowEval14553 x
  · exact rowEval14554 x
  · exact rowEval14555 x
  · exact rowEval14556 x
  · exact rowEval14557 x
  · exact rowEval14558 x
  · exact rowEval14559 x
  · exact rowEval14560 x
  · exact rowEval14561 x
  · exact rowEval14562 x
  · exact rowEval14563 x
  · exact rowEval14564 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

end MUB6.Certificate.GramEntries.Block4

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

theorem rawRowCheck14781 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form9 = rawRow14781 := by decide +kernel

theorem rowCheck14781 : row14781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14781 := by decide +kernel

theorem rowEval14781 (x : Key → ℝ) : Integer.Sparse.eval row14781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14781, Integer.Sparse.eval_collectBalanced, rawRowCheck14781]

theorem rawRowCheck14782 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form9 = rawRow14782 := by decide +kernel

theorem rowCheck14782 : row14782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14782 := by decide +kernel

theorem rowEval14782 (x : Key → ℝ) : Integer.Sparse.eval row14782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14782, Integer.Sparse.eval_collectBalanced, rawRowCheck14782]

theorem rawRowCheck14783 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form9 = rawRow14783 := by decide +kernel

theorem rowCheck14783 : row14783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14783 := by decide +kernel

theorem rowEval14783 (x : Key → ℝ) : Integer.Sparse.eval row14783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14783, Integer.Sparse.eval_collectBalanced, rawRowCheck14783]

theorem rawRowCheck14784 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form9 = rawRow14784 := by decide +kernel

theorem rowCheck14784 : row14784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14784 := by decide +kernel

theorem rowEval14784 (x : Key → ℝ) : Integer.Sparse.eval row14784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14784, Integer.Sparse.eval_collectBalanced, rawRowCheck14784]

theorem rawRowCheck14785 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form9 = rawRow14785 := by decide +kernel

theorem rowCheck14785 : row14785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14785 := by decide +kernel

theorem rowEval14785 (x : Key → ℝ) : Integer.Sparse.eval row14785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14785, Integer.Sparse.eval_collectBalanced, rawRowCheck14785]

theorem rawRowCheck14786 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form9 = rawRow14786 := by decide +kernel

theorem rowCheck14786 : row14786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14786 := by decide +kernel

theorem rowEval14786 (x : Key → ℝ) : Integer.Sparse.eval row14786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14786, Integer.Sparse.eval_collectBalanced, rawRowCheck14786]

theorem rawRowCheck14787 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form9 = rawRow14787 := by decide +kernel

theorem rowCheck14787 : row14787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14787 := by decide +kernel

theorem rowEval14787 (x : Key → ℝ) : Integer.Sparse.eval row14787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14787, Integer.Sparse.eval_collectBalanced, rawRowCheck14787]

theorem rawRowCheck14788 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form9 = rawRow14788 := by decide +kernel

theorem rowCheck14788 : row14788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14788 := by decide +kernel

theorem rowEval14788 (x : Key → ℝ) : Integer.Sparse.eval row14788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14788, Integer.Sparse.eval_collectBalanced, rawRowCheck14788]

theorem rawRowCheck14789 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form9 = rawRow14789 := by decide +kernel

theorem rowCheck14789 : row14789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14789 := by decide +kernel

theorem rowEval14789 (x : Key → ℝ) : Integer.Sparse.eval row14789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14789, Integer.Sparse.eval_collectBalanced, rawRowCheck14789]

theorem rawRowCheck14790 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form9 = rawRow14790 := by decide +kernel

theorem rowCheck14790 : row14790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14790 := by decide +kernel

theorem rowEval14790 (x : Key → ℝ) : Integer.Sparse.eval row14790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14790, Integer.Sparse.eval_collectBalanced, rawRowCheck14790]

theorem rawRowCheck14791 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form9 = rawRow14791 := by decide +kernel

theorem rowCheck14791 : row14791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14791 := by decide +kernel

theorem rowEval14791 (x : Key → ℝ) : Integer.Sparse.eval row14791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14791, Integer.Sparse.eval_collectBalanced, rawRowCheck14791]

theorem rawRowCheck14792 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form9 = rawRow14792 := by decide +kernel

theorem rowCheck14792 : row14792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14792 := by decide +kernel

theorem rowEval14792 (x : Key → ℝ) : Integer.Sparse.eval row14792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14792, Integer.Sparse.eval_collectBalanced, rawRowCheck14792]

theorem rawRowCheck14793 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form9 = rawRow14793 := by decide +kernel

theorem rowCheck14793 : row14793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14793 := by decide +kernel

theorem rowEval14793 (x : Key → ℝ) : Integer.Sparse.eval row14793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14793, Integer.Sparse.eval_collectBalanced, rawRowCheck14793]

theorem rawRowCheck14794 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form9 = rawRow14794 := by decide +kernel

theorem rowCheck14794 : row14794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14794 := by decide +kernel

theorem rowEval14794 (x : Key → ℝ) : Integer.Sparse.eval row14794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14794, Integer.Sparse.eval_collectBalanced, rawRowCheck14794]

theorem rawRowCheck14795 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form9 = rawRow14795 := by decide +kernel

theorem rowCheck14795 : row14795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14795 := by decide +kernel

theorem rowEval14795 (x : Key → ℝ) : Integer.Sparse.eval row14795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14795, Integer.Sparse.eval_collectBalanced, rawRowCheck14795]

theorem rawRowCheck14796 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form9 = rawRow14796 := by decide +kernel

theorem rowCheck14796 : row14796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14796 := by decide +kernel

theorem rowEval14796 (x : Key → ℝ) : Integer.Sparse.eval row14796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14796, Integer.Sparse.eval_collectBalanced, rawRowCheck14796]

theorem rawRowCheck14797 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form9 = rawRow14797 := by decide +kernel

theorem rowCheck14797 : row14797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14797 := by decide +kernel

theorem rowEval14797 (x : Key → ℝ) : Integer.Sparse.eval row14797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14797, Integer.Sparse.eval_collectBalanced, rawRowCheck14797]

theorem rawRowCheck14798 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form9 = rawRow14798 := by decide +kernel

theorem rowCheck14798 : row14798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14798 := by decide +kernel

theorem rowEval14798 (x : Key → ℝ) : Integer.Sparse.eval row14798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14798, Integer.Sparse.eval_collectBalanced, rawRowCheck14798]

theorem rawRowCheck14799 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form9 = rawRow14799 := by decide +kernel

theorem rowCheck14799 : row14799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14799 := by decide +kernel

theorem rowEval14799 (x : Key → ℝ) : Integer.Sparse.eval row14799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14799, Integer.Sparse.eval_collectBalanced, rawRowCheck14799]

theorem rawRowCheck14800 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form9 = rawRow14800 := by decide +kernel

theorem rowCheck14800 : row14800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14800 := by decide +kernel

theorem rowEval14800 (x : Key → ℝ) : Integer.Sparse.eval row14800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14800, Integer.Sparse.eval_collectBalanced, rawRowCheck14800]

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

theorem entryCheck11_9 : entry11_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_9 k)) := by decide +kernel

theorem rowsSound11_9 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval14781 x
  · exact rowEval14782 x
  · exact rowEval14783 x
  · exact rowEval14784 x
  · exact rowEval14785 x
  · exact rowEval14786 x
  · exact rowEval14787 x
  · exact rowEval14788 x
  · exact rowEval14789 x
  · exact rowEval14790 x
  · exact rowEval14791 x
  · exact rowEval14792 x
  · exact rowEval14793 x
  · exact rowEval14794 x
  · exact rowEval14795 x
  · exact rowEval14796 x
  · exact rowEval14797 x
  · exact rowEval14798 x
  · exact rowEval14799 x
  · exact rowEval14800 x

theorem entryEval11_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_9 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck11_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_9]

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

theorem rawRowCheck15069 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form9 = rawRow15069 := by decide +kernel

theorem rowCheck15069 : row15069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15069 := by decide +kernel

theorem rowEval15069 (x : Key → ℝ) : Integer.Sparse.eval row15069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15069, Integer.Sparse.eval_collectBalanced, rawRowCheck15069]

theorem rawRowCheck15070 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form9 = rawRow15070 := by decide +kernel

theorem rowCheck15070 : row15070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15070 := by decide +kernel

theorem rowEval15070 (x : Key → ℝ) : Integer.Sparse.eval row15070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15070, Integer.Sparse.eval_collectBalanced, rawRowCheck15070]

theorem rawRowCheck15071 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form9 = rawRow15071 := by decide +kernel

theorem rowCheck15071 : row15071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15071 := by decide +kernel

theorem rowEval15071 (x : Key → ℝ) : Integer.Sparse.eval row15071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15071, Integer.Sparse.eval_collectBalanced, rawRowCheck15071]

theorem rawRowCheck15072 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form9 = rawRow15072 := by decide +kernel

theorem rowCheck15072 : row15072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15072 := by decide +kernel

theorem rowEval15072 (x : Key → ℝ) : Integer.Sparse.eval row15072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15072, Integer.Sparse.eval_collectBalanced, rawRowCheck15072]

theorem rawRowCheck15073 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form9 = rawRow15073 := by decide +kernel

theorem rowCheck15073 : row15073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15073 := by decide +kernel

theorem rowEval15073 (x : Key → ℝ) : Integer.Sparse.eval row15073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15073, Integer.Sparse.eval_collectBalanced, rawRowCheck15073]

theorem rawRowCheck15074 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form9 = rawRow15074 := by decide +kernel

theorem rowCheck15074 : row15074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15074 := by decide +kernel

theorem rowEval15074 (x : Key → ℝ) : Integer.Sparse.eval row15074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15074, Integer.Sparse.eval_collectBalanced, rawRowCheck15074]

theorem rawRowCheck15075 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form9 = rawRow15075 := by decide +kernel

theorem rowCheck15075 : row15075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15075 := by decide +kernel

theorem rowEval15075 (x : Key → ℝ) : Integer.Sparse.eval row15075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15075, Integer.Sparse.eval_collectBalanced, rawRowCheck15075]

theorem rawRowCheck15076 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form9 = rawRow15076 := by decide +kernel

theorem rowCheck15076 : row15076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15076 := by decide +kernel

theorem rowEval15076 (x : Key → ℝ) : Integer.Sparse.eval row15076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15076, Integer.Sparse.eval_collectBalanced, rawRowCheck15076]

theorem rawRowCheck15077 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form9 = rawRow15077 := by decide +kernel

theorem rowCheck15077 : row15077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15077 := by decide +kernel

theorem rowEval15077 (x : Key → ℝ) : Integer.Sparse.eval row15077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15077, Integer.Sparse.eval_collectBalanced, rawRowCheck15077]

theorem rawRowCheck15078 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form9 = rawRow15078 := by decide +kernel

theorem rowCheck15078 : row15078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15078 := by decide +kernel

theorem rowEval15078 (x : Key → ℝ) : Integer.Sparse.eval row15078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15078, Integer.Sparse.eval_collectBalanced, rawRowCheck15078]

theorem rawRowCheck15079 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form9 = rawRow15079 := by decide +kernel

theorem rowCheck15079 : row15079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15079 := by decide +kernel

theorem rowEval15079 (x : Key → ℝ) : Integer.Sparse.eval row15079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15079, Integer.Sparse.eval_collectBalanced, rawRowCheck15079]

theorem rawRowCheck15080 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form9 = rawRow15080 := by decide +kernel

theorem rowCheck15080 : row15080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15080 := by decide +kernel

theorem rowEval15080 (x : Key → ℝ) : Integer.Sparse.eval row15080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15080, Integer.Sparse.eval_collectBalanced, rawRowCheck15080]

theorem rawRowCheck15081 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form9 = rawRow15081 := by decide +kernel

theorem rowCheck15081 : row15081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15081 := by decide +kernel

theorem rowEval15081 (x : Key → ℝ) : Integer.Sparse.eval row15081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15081, Integer.Sparse.eval_collectBalanced, rawRowCheck15081]

theorem rawRowCheck15082 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form9 = rawRow15082 := by decide +kernel

theorem rowCheck15082 : row15082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15082 := by decide +kernel

theorem rowEval15082 (x : Key → ℝ) : Integer.Sparse.eval row15082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15082, Integer.Sparse.eval_collectBalanced, rawRowCheck15082]

theorem rawRowCheck15083 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form9 = rawRow15083 := by decide +kernel

theorem rowCheck15083 : row15083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15083 := by decide +kernel

theorem rowEval15083 (x : Key → ℝ) : Integer.Sparse.eval row15083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15083, Integer.Sparse.eval_collectBalanced, rawRowCheck15083]

theorem rawRowCheck15084 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form9 = rawRow15084 := by decide +kernel

theorem rowCheck15084 : row15084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15084 := by decide +kernel

theorem rowEval15084 (x : Key → ℝ) : Integer.Sparse.eval row15084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15084, Integer.Sparse.eval_collectBalanced, rawRowCheck15084]

theorem rawRowCheck15085 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form9 = rawRow15085 := by decide +kernel

theorem rowCheck15085 : row15085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15085 := by decide +kernel

theorem rowEval15085 (x : Key → ℝ) : Integer.Sparse.eval row15085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15085, Integer.Sparse.eval_collectBalanced, rawRowCheck15085]

theorem rawRowCheck15086 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form9 = rawRow15086 := by decide +kernel

theorem rowCheck15086 : row15086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15086 := by decide +kernel

theorem rowEval15086 (x : Key → ℝ) : Integer.Sparse.eval row15086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15086, Integer.Sparse.eval_collectBalanced, rawRowCheck15086]

theorem rawRowCheck15087 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form9 = rawRow15087 := by decide +kernel

theorem rowCheck15087 : row15087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15087 := by decide +kernel

theorem rowEval15087 (x : Key → ℝ) : Integer.Sparse.eval row15087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15087, Integer.Sparse.eval_collectBalanced, rawRowCheck15087]

theorem rawRowCheck15088 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form9 = rawRow15088 := by decide +kernel

theorem rowCheck15088 : row15088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15088 := by decide +kernel

theorem rowEval15088 (x : Key → ℝ) : Integer.Sparse.eval row15088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15088, Integer.Sparse.eval_collectBalanced, rawRowCheck15088]

theorem rawRowCheck15089 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form9 = rawRow15089 := by decide +kernel

theorem rowCheck15089 : row15089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15089 := by decide +kernel

theorem rowEval15089 (x : Key → ℝ) : Integer.Sparse.eval row15089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15089, Integer.Sparse.eval_collectBalanced, rawRowCheck15089]

theorem rawRowCheck15090 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form9 = rawRow15090 := by decide +kernel

theorem rowCheck15090 : row15090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15090 := by decide +kernel

theorem rowEval15090 (x : Key → ℝ) : Integer.Sparse.eval row15090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15090, Integer.Sparse.eval_collectBalanced, rawRowCheck15090]

theorem rawRowCheck15091 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form9 = rawRow15091 := by decide +kernel

theorem rowCheck15091 : row15091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15091 := by decide +kernel

theorem rowEval15091 (x : Key → ℝ) : Integer.Sparse.eval row15091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15091, Integer.Sparse.eval_collectBalanced, rawRowCheck15091]

theorem rawRowCheck15092 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form9 = rawRow15092 := by decide +kernel

theorem rowCheck15092 : row15092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15092 := by decide +kernel

theorem rowEval15092 (x : Key → ℝ) : Integer.Sparse.eval row15092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15092, Integer.Sparse.eval_collectBalanced, rawRowCheck15092]

theorem rawRowCheck15093 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form9 = rawRow15093 := by decide +kernel

theorem rowCheck15093 : row15093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15093 := by decide +kernel

theorem rowEval15093 (x : Key → ℝ) : Integer.Sparse.eval row15093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15093, Integer.Sparse.eval_collectBalanced, rawRowCheck15093]

theorem rawRowCheck15094 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form9 = rawRow15094 := by decide +kernel

theorem rowCheck15094 : row15094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15094 := by decide +kernel

theorem rowEval15094 (x : Key → ℝ) : Integer.Sparse.eval row15094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15094, Integer.Sparse.eval_collectBalanced, rawRowCheck15094]

theorem rawRowCheck15095 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form9 = rawRow15095 := by decide +kernel

theorem rowCheck15095 : row15095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15095 := by decide +kernel

theorem rowEval15095 (x : Key → ℝ) : Integer.Sparse.eval row15095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15095, Integer.Sparse.eval_collectBalanced, rawRowCheck15095]

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

theorem entryCheck12_9 : entry12_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_9 k)) := by decide +kernel

theorem rowsSound12_9 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval15069 x
  · exact rowEval15070 x
  · exact rowEval15071 x
  · exact rowEval15072 x
  · exact rowEval15073 x
  · exact rowEval15074 x
  · exact rowEval15075 x
  · exact rowEval15076 x
  · exact rowEval15077 x
  · exact rowEval15078 x
  · exact rowEval15079 x
  · exact rowEval15080 x
  · exact rowEval15081 x
  · exact rowEval15082 x
  · exact rowEval15083 x
  · exact rowEval15084 x
  · exact rowEval15085 x
  · exact rowEval15086 x
  · exact rowEval15087 x
  · exact rowEval15088 x
  · exact rowEval15089 x
  · exact rowEval15090 x
  · exact rowEval15091 x
  · exact rowEval15092 x
  · exact rowEval15093 x
  · exact rowEval15094 x
  · exact rowEval15095 x

theorem entryEval12_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_9 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck12_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_9]

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

theorem rawRowCheck16869 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form9 = rawRow16869 := by decide +kernel

theorem rowCheck16869 : row16869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16869 := by decide +kernel

theorem rowEval16869 (x : Key → ℝ) : Integer.Sparse.eval row16869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16869, Integer.Sparse.eval_collectBalanced, rawRowCheck16869]

theorem rawRowCheck16870 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form9 = rawRow16870 := by decide +kernel

theorem rowCheck16870 : row16870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16870 := by decide +kernel

theorem rowEval16870 (x : Key → ℝ) : Integer.Sparse.eval row16870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16870, Integer.Sparse.eval_collectBalanced, rawRowCheck16870]

theorem rawRowCheck16871 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form9 = rawRow16871 := by decide +kernel

theorem rowCheck16871 : row16871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16871 := by decide +kernel

theorem rowEval16871 (x : Key → ℝ) : Integer.Sparse.eval row16871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16871, Integer.Sparse.eval_collectBalanced, rawRowCheck16871]

theorem rawRowCheck16872 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form9 = rawRow16872 := by decide +kernel

theorem rowCheck16872 : row16872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16872 := by decide +kernel

theorem rowEval16872 (x : Key → ℝ) : Integer.Sparse.eval row16872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16872, Integer.Sparse.eval_collectBalanced, rawRowCheck16872]

theorem rawRowCheck16873 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form9 = rawRow16873 := by decide +kernel

theorem rowCheck16873 : row16873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16873 := by decide +kernel

theorem rowEval16873 (x : Key → ℝ) : Integer.Sparse.eval row16873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16873, Integer.Sparse.eval_collectBalanced, rawRowCheck16873]

theorem rawRowCheck16874 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form9 = rawRow16874 := by decide +kernel

theorem rowCheck16874 : row16874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16874 := by decide +kernel

theorem rowEval16874 (x : Key → ℝ) : Integer.Sparse.eval row16874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16874, Integer.Sparse.eval_collectBalanced, rawRowCheck16874]

theorem rawRowCheck16875 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form9 = rawRow16875 := by decide +kernel

theorem rowCheck16875 : row16875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16875 := by decide +kernel

theorem rowEval16875 (x : Key → ℝ) : Integer.Sparse.eval row16875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16875, Integer.Sparse.eval_collectBalanced, rawRowCheck16875]

theorem rawRowCheck16876 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form9 = rawRow16876 := by decide +kernel

theorem rowCheck16876 : row16876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16876 := by decide +kernel

theorem rowEval16876 (x : Key → ℝ) : Integer.Sparse.eval row16876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16876, Integer.Sparse.eval_collectBalanced, rawRowCheck16876]

theorem rawRowCheck16877 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form9 = rawRow16877 := by decide +kernel

theorem rowCheck16877 : row16877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16877 := by decide +kernel

theorem rowEval16877 (x : Key → ℝ) : Integer.Sparse.eval row16877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16877, Integer.Sparse.eval_collectBalanced, rawRowCheck16877]

theorem rawRowCheck16878 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form9 = rawRow16878 := by decide +kernel

theorem rowCheck16878 : row16878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16878 := by decide +kernel

theorem rowEval16878 (x : Key → ℝ) : Integer.Sparse.eval row16878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16878, Integer.Sparse.eval_collectBalanced, rawRowCheck16878]

theorem rawRowCheck16879 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form9 = rawRow16879 := by decide +kernel

theorem rowCheck16879 : row16879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16879 := by decide +kernel

theorem rowEval16879 (x : Key → ℝ) : Integer.Sparse.eval row16879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16879, Integer.Sparse.eval_collectBalanced, rawRowCheck16879]

theorem rawRowCheck16880 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form9 = rawRow16880 := by decide +kernel

theorem rowCheck16880 : row16880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16880 := by decide +kernel

theorem rowEval16880 (x : Key → ℝ) : Integer.Sparse.eval row16880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16880, Integer.Sparse.eval_collectBalanced, rawRowCheck16880]

theorem rawRowCheck16881 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form9 = rawRow16881 := by decide +kernel

theorem rowCheck16881 : row16881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16881 := by decide +kernel

theorem rowEval16881 (x : Key → ℝ) : Integer.Sparse.eval row16881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16881, Integer.Sparse.eval_collectBalanced, rawRowCheck16881]

theorem rawRowCheck16882 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form9 = rawRow16882 := by decide +kernel

theorem rowCheck16882 : row16882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16882 := by decide +kernel

theorem rowEval16882 (x : Key → ℝ) : Integer.Sparse.eval row16882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16882, Integer.Sparse.eval_collectBalanced, rawRowCheck16882]

theorem rawRowCheck16883 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form9 = rawRow16883 := by decide +kernel

theorem rowCheck16883 : row16883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16883 := by decide +kernel

theorem rowEval16883 (x : Key → ℝ) : Integer.Sparse.eval row16883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16883, Integer.Sparse.eval_collectBalanced, rawRowCheck16883]

theorem rawRowCheck16884 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form9 = rawRow16884 := by decide +kernel

theorem rowCheck16884 : row16884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16884 := by decide +kernel

theorem rowEval16884 (x : Key → ℝ) : Integer.Sparse.eval row16884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16884, Integer.Sparse.eval_collectBalanced, rawRowCheck16884]

theorem rawRowCheck16885 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form9 = rawRow16885 := by decide +kernel

theorem rowCheck16885 : row16885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16885 := by decide +kernel

theorem rowEval16885 (x : Key → ℝ) : Integer.Sparse.eval row16885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16885, Integer.Sparse.eval_collectBalanced, rawRowCheck16885]

theorem rawRowCheck16886 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form9 = rawRow16886 := by decide +kernel

theorem rowCheck16886 : row16886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16886 := by decide +kernel

theorem rowEval16886 (x : Key → ℝ) : Integer.Sparse.eval row16886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16886, Integer.Sparse.eval_collectBalanced, rawRowCheck16886]

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

theorem entryCheck17_9 : entry17_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_9 k)) := by decide +kernel

theorem rowsSound17_9 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval16869 x
  · exact rowEval16870 x
  · exact rowEval16871 x
  · exact rowEval16872 x
  · exact rowEval16873 x
  · exact rowEval16874 x
  · exact rowEval16875 x
  · exact rowEval16876 x
  · exact rowEval16877 x
  · exact rowEval16878 x
  · exact rowEval16879 x
  · exact rowEval16880 x
  · exact rowEval16881 x
  · exact rowEval16882 x
  · exact rowEval16883 x
  · exact rowEval16884 x
  · exact rowEval16885 x
  · exact rowEval16886 x

theorem entryEval17_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_9 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck17_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_9]

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

theorem rawRowCheck17211 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form9 = rawRow17211 := by decide +kernel

theorem rowCheck17211 : row17211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17211 := by decide +kernel

theorem rowEval17211 (x : Key → ℝ) : Integer.Sparse.eval row17211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17211, Integer.Sparse.eval_collectBalanced, rawRowCheck17211]

theorem rawRowCheck17212 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form9 = rawRow17212 := by decide +kernel

theorem rowCheck17212 : row17212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17212 := by decide +kernel

theorem rowEval17212 (x : Key → ℝ) : Integer.Sparse.eval row17212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17212, Integer.Sparse.eval_collectBalanced, rawRowCheck17212]

theorem rawRowCheck17213 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form9 = rawRow17213 := by decide +kernel

theorem rowCheck17213 : row17213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17213 := by decide +kernel

theorem rowEval17213 (x : Key → ℝ) : Integer.Sparse.eval row17213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17213, Integer.Sparse.eval_collectBalanced, rawRowCheck17213]

theorem rawRowCheck17214 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form9 = rawRow17214 := by decide +kernel

theorem rowCheck17214 : row17214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17214 := by decide +kernel

theorem rowEval17214 (x : Key → ℝ) : Integer.Sparse.eval row17214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17214, Integer.Sparse.eval_collectBalanced, rawRowCheck17214]

theorem rawRowCheck17215 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form9 = rawRow17215 := by decide +kernel

theorem rowCheck17215 : row17215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17215 := by decide +kernel

theorem rowEval17215 (x : Key → ℝ) : Integer.Sparse.eval row17215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17215, Integer.Sparse.eval_collectBalanced, rawRowCheck17215]

theorem rawRowCheck17216 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form9 = rawRow17216 := by decide +kernel

theorem rowCheck17216 : row17216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17216 := by decide +kernel

theorem rowEval17216 (x : Key → ℝ) : Integer.Sparse.eval row17216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17216, Integer.Sparse.eval_collectBalanced, rawRowCheck17216]

theorem rawRowCheck17217 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form9 = rawRow17217 := by decide +kernel

theorem rowCheck17217 : row17217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17217 := by decide +kernel

theorem rowEval17217 (x : Key → ℝ) : Integer.Sparse.eval row17217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17217, Integer.Sparse.eval_collectBalanced, rawRowCheck17217]

theorem rawRowCheck17218 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form9 = rawRow17218 := by decide +kernel

theorem rowCheck17218 : row17218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17218 := by decide +kernel

theorem rowEval17218 (x : Key → ℝ) : Integer.Sparse.eval row17218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17218, Integer.Sparse.eval_collectBalanced, rawRowCheck17218]

theorem rawRowCheck17219 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form9 = rawRow17219 := by decide +kernel

theorem rowCheck17219 : row17219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17219 := by decide +kernel

theorem rowEval17219 (x : Key → ℝ) : Integer.Sparse.eval row17219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17219, Integer.Sparse.eval_collectBalanced, rawRowCheck17219]

theorem rawRowCheck17220 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form9 = rawRow17220 := by decide +kernel

theorem rowCheck17220 : row17220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17220 := by decide +kernel

theorem rowEval17220 (x : Key → ℝ) : Integer.Sparse.eval row17220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17220, Integer.Sparse.eval_collectBalanced, rawRowCheck17220]

theorem rawRowCheck17221 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form9 = rawRow17221 := by decide +kernel

theorem rowCheck17221 : row17221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17221 := by decide +kernel

theorem rowEval17221 (x : Key → ℝ) : Integer.Sparse.eval row17221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17221, Integer.Sparse.eval_collectBalanced, rawRowCheck17221]

theorem rawRowCheck17222 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form9 = rawRow17222 := by decide +kernel

theorem rowCheck17222 : row17222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17222 := by decide +kernel

theorem rowEval17222 (x : Key → ℝ) : Integer.Sparse.eval row17222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17222, Integer.Sparse.eval_collectBalanced, rawRowCheck17222]

theorem rawRowCheck17223 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form9 = rawRow17223 := by decide +kernel

theorem rowCheck17223 : row17223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17223 := by decide +kernel

theorem rowEval17223 (x : Key → ℝ) : Integer.Sparse.eval row17223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17223, Integer.Sparse.eval_collectBalanced, rawRowCheck17223]

theorem rawRowCheck17224 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form9 = rawRow17224 := by decide +kernel

theorem rowCheck17224 : row17224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17224 := by decide +kernel

theorem rowEval17224 (x : Key → ℝ) : Integer.Sparse.eval row17224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17224, Integer.Sparse.eval_collectBalanced, rawRowCheck17224]

theorem rawRowCheck17225 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form9 = rawRow17225 := by decide +kernel

theorem rowCheck17225 : row17225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17225 := by decide +kernel

theorem rowEval17225 (x : Key → ℝ) : Integer.Sparse.eval row17225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17225, Integer.Sparse.eval_collectBalanced, rawRowCheck17225]

theorem rawRowCheck17226 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form9 = rawRow17226 := by decide +kernel

theorem rowCheck17226 : row17226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17226 := by decide +kernel

theorem rowEval17226 (x : Key → ℝ) : Integer.Sparse.eval row17226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17226, Integer.Sparse.eval_collectBalanced, rawRowCheck17226]

theorem rawRowCheck17227 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow17227 := by decide +kernel

theorem rowCheck17227 : row17227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17227 := by decide +kernel

theorem rowEval17227 (x : Key → ℝ) : Integer.Sparse.eval row17227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17227, Integer.Sparse.eval_collectBalanced, rawRowCheck17227]

theorem rawRowCheck17228 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow17228 := by decide +kernel

theorem rowCheck17228 : row17228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17228 := by decide +kernel

theorem rowEval17228 (x : Key → ℝ) : Integer.Sparse.eval row17228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17228, Integer.Sparse.eval_collectBalanced, rawRowCheck17228]

theorem rawRowCheck17229 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow17229 := by decide +kernel

theorem rowCheck17229 : row17229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17229 := by decide +kernel

theorem rowEval17229 (x : Key → ℝ) : Integer.Sparse.eval row17229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17229, Integer.Sparse.eval_collectBalanced, rawRowCheck17229]

theorem rawRowCheck17230 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form9 = rawRow17230 := by decide +kernel

theorem rowCheck17230 : row17230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17230 := by decide +kernel

theorem rowEval17230 (x : Key → ℝ) : Integer.Sparse.eval row17230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17230, Integer.Sparse.eval_collectBalanced, rawRowCheck17230]

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

theorem rawRowCheck17501 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form9 = rawRow17501 := by decide +kernel

theorem rowCheck17501 : row17501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17501 := by decide +kernel

theorem rowEval17501 (x : Key → ℝ) : Integer.Sparse.eval row17501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17501, Integer.Sparse.eval_collectBalanced, rawRowCheck17501]

theorem rawRowCheck17502 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form9 = rawRow17502 := by decide +kernel

theorem rowCheck17502 : row17502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17502 := by decide +kernel

theorem rowEval17502 (x : Key → ℝ) : Integer.Sparse.eval row17502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17502, Integer.Sparse.eval_collectBalanced, rawRowCheck17502]

theorem rawRowCheck17503 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form9 = rawRow17503 := by decide +kernel

theorem rowCheck17503 : row17503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17503 := by decide +kernel

theorem rowEval17503 (x : Key → ℝ) : Integer.Sparse.eval row17503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17503, Integer.Sparse.eval_collectBalanced, rawRowCheck17503]

theorem rawRowCheck17504 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17504 := by decide +kernel

theorem rowCheck17504 : row17504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17504 := by decide +kernel

theorem rowEval17504 (x : Key → ℝ) : Integer.Sparse.eval row17504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17504, Integer.Sparse.eval_collectBalanced, rawRowCheck17504]

theorem rawRowCheck17505 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17505 := by decide +kernel

theorem rowCheck17505 : row17505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17505 := by decide +kernel

theorem rowEval17505 (x : Key → ℝ) : Integer.Sparse.eval row17505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17505, Integer.Sparse.eval_collectBalanced, rawRowCheck17505]

theorem rawRowCheck17506 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17506 := by decide +kernel

theorem rowCheck17506 : row17506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17506 := by decide +kernel

theorem rowEval17506 (x : Key → ℝ) : Integer.Sparse.eval row17506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17506, Integer.Sparse.eval_collectBalanced, rawRowCheck17506]

theorem rawRowCheck17507 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17507 := by decide +kernel

theorem rowCheck17507 : row17507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17507 := by decide +kernel

theorem rowEval17507 (x : Key → ℝ) : Integer.Sparse.eval row17507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17507, Integer.Sparse.eval_collectBalanced, rawRowCheck17507]

theorem rawRowCheck17508 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17508 := by decide +kernel

theorem rowCheck17508 : row17508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17508 := by decide +kernel

theorem rowEval17508 (x : Key → ℝ) : Integer.Sparse.eval row17508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17508, Integer.Sparse.eval_collectBalanced, rawRowCheck17508]

theorem rawRowCheck17509 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17509 := by decide +kernel

theorem rowCheck17509 : row17509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17509 := by decide +kernel

theorem rowEval17509 (x : Key → ℝ) : Integer.Sparse.eval row17509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17509, Integer.Sparse.eval_collectBalanced, rawRowCheck17509]

theorem rawRowCheck17510 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form9 = rawRow17510 := by decide +kernel

theorem rowCheck17510 : row17510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17510 := by decide +kernel

theorem rowEval17510 (x : Key → ℝ) : Integer.Sparse.eval row17510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17510, Integer.Sparse.eval_collectBalanced, rawRowCheck17510]

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

theorem entryCheck18_9 : entry18_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_9 k)) := by decide +kernel

theorem rowsSound18_9 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17211 x
  · exact rowEval17212 x
  · exact rowEval17213 x
  · exact rowEval17214 x
  · exact rowEval17215 x
  · exact rowEval17216 x
  · exact rowEval17217 x
  · exact rowEval17218 x
  · exact rowEval17219 x
  · exact rowEval17220 x
  · exact rowEval17221 x
  · exact rowEval17222 x
  · exact rowEval17223 x
  · exact rowEval17224 x
  · exact rowEval17225 x
  · exact rowEval17226 x
  · exact rowEval17227 x
  · exact rowEval17228 x
  · exact rowEval17229 x
  · exact rowEval17230 x

theorem entryEval18_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_9 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck18_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_9]

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

theorem entryCheck19_9 : entry19_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_9 k)) := by decide +kernel

theorem rowsSound19_9 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17501 x
  · exact rowEval17502 x
  · exact rowEval17503 x
  · exact rowEval17504 x
  · exact rowEval17505 x
  · exact rowEval17506 x
  · exact rowEval17507 x
  · exact rowEval17508 x
  · exact rowEval17509 x
  · exact rowEval17510 x

theorem entryEval19_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_9 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck19_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_9]

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

theorem rawRowCheck17773 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17773 := by decide +kernel

theorem rowCheck17773 : row17773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17773 := by decide +kernel

theorem rowEval17773 (x : Key → ℝ) : Integer.Sparse.eval row17773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17773, Integer.Sparse.eval_collectBalanced, rawRowCheck17773]

theorem rawRowCheck17774 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17774 := by decide +kernel

theorem rowCheck17774 : row17774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17774 := by decide +kernel

theorem rowEval17774 (x : Key → ℝ) : Integer.Sparse.eval row17774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17774, Integer.Sparse.eval_collectBalanced, rawRowCheck17774]

theorem rawRowCheck17775 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17775 := by decide +kernel

theorem rowCheck17775 : row17775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17775 := by decide +kernel

theorem rowEval17775 (x : Key → ℝ) : Integer.Sparse.eval row17775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17775, Integer.Sparse.eval_collectBalanced, rawRowCheck17775]

theorem rawRowCheck17776 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form9 = rawRow17776 := by decide +kernel

theorem rowCheck17776 : row17776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17776 := by decide +kernel

theorem rowEval17776 (x : Key → ℝ) : Integer.Sparse.eval row17776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17776, Integer.Sparse.eval_collectBalanced, rawRowCheck17776]

theorem rawRowCheck17777 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form9 = rawRow17777 := by decide +kernel

theorem rowCheck17777 : row17777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17777 := by decide +kernel

theorem rowEval17777 (x : Key → ℝ) : Integer.Sparse.eval row17777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17777, Integer.Sparse.eval_collectBalanced, rawRowCheck17777]

theorem rawRowCheck17778 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form9 = rawRow17778 := by decide +kernel

theorem rowCheck17778 : row17778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17778 := by decide +kernel

theorem rowEval17778 (x : Key → ℝ) : Integer.Sparse.eval row17778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17778, Integer.Sparse.eval_collectBalanced, rawRowCheck17778]

theorem rawRowCheck17779 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form9 = rawRow17779 := by decide +kernel

theorem rowCheck17779 : row17779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17779 := by decide +kernel

theorem rowEval17779 (x : Key → ℝ) : Integer.Sparse.eval row17779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17779, Integer.Sparse.eval_collectBalanced, rawRowCheck17779]

theorem rawRowCheck17780 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form9 = rawRow17780 := by decide +kernel

theorem rowCheck17780 : row17780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17780 := by decide +kernel

theorem rowEval17780 (x : Key → ℝ) : Integer.Sparse.eval row17780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17780, Integer.Sparse.eval_collectBalanced, rawRowCheck17780]

theorem rawRowCheck17781 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form9 = rawRow17781 := by decide +kernel

theorem rowCheck17781 : row17781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17781 := by decide +kernel

theorem rowEval17781 (x : Key → ℝ) : Integer.Sparse.eval row17781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17781, Integer.Sparse.eval_collectBalanced, rawRowCheck17781]

theorem rawRowCheck17782 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form9 = rawRow17782 := by decide +kernel

theorem rowCheck17782 : row17782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17782 := by decide +kernel

theorem rowEval17782 (x : Key → ℝ) : Integer.Sparse.eval row17782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17782, Integer.Sparse.eval_collectBalanced, rawRowCheck17782]

theorem rawRowCheck17783 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form9 = rawRow17783 := by decide +kernel

theorem rowCheck17783 : row17783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17783 := by decide +kernel

theorem rowEval17783 (x : Key → ℝ) : Integer.Sparse.eval row17783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17783, Integer.Sparse.eval_collectBalanced, rawRowCheck17783]

theorem rawRowCheck17784 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form9 = rawRow17784 := by decide +kernel

theorem rowCheck17784 : row17784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17784 := by decide +kernel

theorem rowEval17784 (x : Key → ℝ) : Integer.Sparse.eval row17784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17784, Integer.Sparse.eval_collectBalanced, rawRowCheck17784]

theorem rawRowCheck17785 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form9 = rawRow17785 := by decide +kernel

theorem rowCheck17785 : row17785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17785 := by decide +kernel

theorem rowEval17785 (x : Key → ℝ) : Integer.Sparse.eval row17785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17785, Integer.Sparse.eval_collectBalanced, rawRowCheck17785]

theorem rawRowCheck17786 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form9 = rawRow17786 := by decide +kernel

theorem rowCheck17786 : row17786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17786 := by decide +kernel

theorem rowEval17786 (x : Key → ℝ) : Integer.Sparse.eval row17786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17786, Integer.Sparse.eval_collectBalanced, rawRowCheck17786]

theorem rawRowCheck17787 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form9 = rawRow17787 := by decide +kernel

theorem rowCheck17787 : row17787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17787 := by decide +kernel

theorem rowEval17787 (x : Key → ℝ) : Integer.Sparse.eval row17787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17787, Integer.Sparse.eval_collectBalanced, rawRowCheck17787]

theorem rawRowCheck17788 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form9 = rawRow17788 := by decide +kernel

theorem rowCheck17788 : row17788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17788 := by decide +kernel

theorem rowEval17788 (x : Key → ℝ) : Integer.Sparse.eval row17788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17788, Integer.Sparse.eval_collectBalanced, rawRowCheck17788]

theorem rawRowCheck17789 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form9 = rawRow17789 := by decide +kernel

theorem rowCheck17789 : row17789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17789 := by decide +kernel

theorem rowEval17789 (x : Key → ℝ) : Integer.Sparse.eval row17789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17789, Integer.Sparse.eval_collectBalanced, rawRowCheck17789]

theorem rawRowCheck17790 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form9 = rawRow17790 := by decide +kernel

theorem rowCheck17790 : row17790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17790 := by decide +kernel

theorem rowEval17790 (x : Key → ℝ) : Integer.Sparse.eval row17790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17790, Integer.Sparse.eval_collectBalanced, rawRowCheck17790]

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

theorem entryCheck20_9 : entry20_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_9 k)) := by decide +kernel

theorem rowsSound20_9 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17773 x
  · exact rowEval17774 x
  · exact rowEval17775 x
  · exact rowEval17776 x
  · exact rowEval17777 x
  · exact rowEval17778 x
  · exact rowEval17779 x
  · exact rowEval17780 x
  · exact rowEval17781 x
  · exact rowEval17782 x
  · exact rowEval17783 x
  · exact rowEval17784 x
  · exact rowEval17785 x
  · exact rowEval17786 x
  · exact rowEval17787 x
  · exact rowEval17788 x
  · exact rowEval17789 x
  · exact rowEval17790 x

theorem entryEval20_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_9 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck20_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_9]

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

theorem rawRowCheck18169 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form9 = rawRow18169 := by decide +kernel

theorem rowCheck18169 : row18169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18169 := by decide +kernel

theorem rowEval18169 (x : Key → ℝ) : Integer.Sparse.eval row18169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18169, Integer.Sparse.eval_collectBalanced, rawRowCheck18169]

theorem rawRowCheck18170 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form9 = rawRow18170 := by decide +kernel

theorem rowCheck18170 : row18170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18170 := by decide +kernel

theorem rowEval18170 (x : Key → ℝ) : Integer.Sparse.eval row18170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18170, Integer.Sparse.eval_collectBalanced, rawRowCheck18170]

theorem rawRowCheck18171 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form9 = rawRow18171 := by decide +kernel

theorem rowCheck18171 : row18171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18171 := by decide +kernel

theorem rowEval18171 (x : Key → ℝ) : Integer.Sparse.eval row18171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18171, Integer.Sparse.eval_collectBalanced, rawRowCheck18171]

theorem rawRowCheck18172 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form9 = rawRow18172 := by decide +kernel

theorem rowCheck18172 : row18172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18172 := by decide +kernel

theorem rowEval18172 (x : Key → ℝ) : Integer.Sparse.eval row18172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18172, Integer.Sparse.eval_collectBalanced, rawRowCheck18172]

theorem rawRowCheck18173 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form9 = rawRow18173 := by decide +kernel

theorem rowCheck18173 : row18173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18173 := by decide +kernel

theorem rowEval18173 (x : Key → ℝ) : Integer.Sparse.eval row18173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18173, Integer.Sparse.eval_collectBalanced, rawRowCheck18173]

theorem rawRowCheck18174 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form9 = rawRow18174 := by decide +kernel

theorem rowCheck18174 : row18174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18174 := by decide +kernel

theorem rowEval18174 (x : Key → ℝ) : Integer.Sparse.eval row18174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18174, Integer.Sparse.eval_collectBalanced, rawRowCheck18174]

theorem rawRowCheck18175 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form9 = rawRow18175 := by decide +kernel

theorem rowCheck18175 : row18175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18175 := by decide +kernel

theorem rowEval18175 (x : Key → ℝ) : Integer.Sparse.eval row18175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18175, Integer.Sparse.eval_collectBalanced, rawRowCheck18175]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18176 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form9 = rawRow18176 := by decide +kernel

theorem rowCheck18176 : row18176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18176 := by decide +kernel

theorem rowEval18176 (x : Key → ℝ) : Integer.Sparse.eval row18176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18176, Integer.Sparse.eval_collectBalanced, rawRowCheck18176]

theorem rawRowCheck18177 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form9 = rawRow18177 := by decide +kernel

theorem rowCheck18177 : row18177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18177 := by decide +kernel

theorem rowEval18177 (x : Key → ℝ) : Integer.Sparse.eval row18177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18177, Integer.Sparse.eval_collectBalanced, rawRowCheck18177]

theorem rawRowCheck18178 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow18178 := by decide +kernel

theorem rowCheck18178 : row18178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18178 := by decide +kernel

theorem rowEval18178 (x : Key → ℝ) : Integer.Sparse.eval row18178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18178, Integer.Sparse.eval_collectBalanced, rawRowCheck18178]

theorem rawRowCheck18179 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow18179 := by decide +kernel

theorem rowCheck18179 : row18179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18179 := by decide +kernel

theorem rowEval18179 (x : Key → ℝ) : Integer.Sparse.eval row18179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18179, Integer.Sparse.eval_collectBalanced, rawRowCheck18179]

theorem rawRowCheck18180 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow18180 := by decide +kernel

theorem rowCheck18180 : row18180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18180 := by decide +kernel

theorem rowEval18180 (x : Key → ℝ) : Integer.Sparse.eval row18180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18180, Integer.Sparse.eval_collectBalanced, rawRowCheck18180]

theorem rawRowCheck18181 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form9 = rawRow18181 := by decide +kernel

theorem rowCheck18181 : row18181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18181 := by decide +kernel

theorem rowEval18181 (x : Key → ℝ) : Integer.Sparse.eval row18181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18181, Integer.Sparse.eval_collectBalanced, rawRowCheck18181]

theorem rawRowCheck18182 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form9 = rawRow18182 := by decide +kernel

theorem rowCheck18182 : row18182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18182 := by decide +kernel

theorem rowEval18182 (x : Key → ℝ) : Integer.Sparse.eval row18182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18182, Integer.Sparse.eval_collectBalanced, rawRowCheck18182]

theorem rawRowCheck18183 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form9 = rawRow18183 := by decide +kernel

theorem rowCheck18183 : row18183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18183 := by decide +kernel

theorem rowEval18183 (x : Key → ℝ) : Integer.Sparse.eval row18183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18183, Integer.Sparse.eval_collectBalanced, rawRowCheck18183]

theorem rawRowCheck18184 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form9 = rawRow18184 := by decide +kernel

theorem rowCheck18184 : row18184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18184 := by decide +kernel

theorem rowEval18184 (x : Key → ℝ) : Integer.Sparse.eval row18184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18184, Integer.Sparse.eval_collectBalanced, rawRowCheck18184]

theorem rawRowCheck18185 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow18185 := by decide +kernel

theorem rowCheck18185 : row18185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18185 := by decide +kernel

theorem rowEval18185 (x : Key → ℝ) : Integer.Sparse.eval row18185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18185, Integer.Sparse.eval_collectBalanced, rawRowCheck18185]

theorem rawRowCheck18186 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow18186 := by decide +kernel

theorem rowCheck18186 : row18186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18186 := by decide +kernel

theorem rowEval18186 (x : Key → ℝ) : Integer.Sparse.eval row18186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18186, Integer.Sparse.eval_collectBalanced, rawRowCheck18186]

theorem rawRowCheck18187 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow18187 := by decide +kernel

theorem rowCheck18187 : row18187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18187 := by decide +kernel

theorem rowEval18187 (x : Key → ℝ) : Integer.Sparse.eval row18187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18187, Integer.Sparse.eval_collectBalanced, rawRowCheck18187]

theorem rawRowCheck18188 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form9 = rawRow18188 := by decide +kernel

theorem rowCheck18188 : row18188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18188 := by decide +kernel

theorem rowEval18188 (x : Key → ℝ) : Integer.Sparse.eval row18188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18188, Integer.Sparse.eval_collectBalanced, rawRowCheck18188]

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

theorem entryCheck21_9 : entry21_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_9 k)) := by decide +kernel

theorem rowsSound21_9 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval18169 x
  · exact rowEval18170 x
  · exact rowEval18171 x
  · exact rowEval18172 x
  · exact rowEval18173 x
  · exact rowEval18174 x
  · exact rowEval18175 x
  · exact rowEval18176 x
  · exact rowEval18177 x
  · exact rowEval18178 x
  · exact rowEval18179 x
  · exact rowEval18180 x
  · exact rowEval18181 x
  · exact rowEval18182 x
  · exact rowEval18183 x
  · exact rowEval18184 x
  · exact rowEval18185 x
  · exact rowEval18186 x
  · exact rowEval18187 x
  · exact rowEval18188 x

theorem entryEval21_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_9 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck21_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_9]

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

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14105 x
  · exact rowEval14106 x
  · exact rowEval14107 x
  · exact rowEval14108 x
  · exact rowEval14109 x
  · exact rowEval14110 x
  · exact rowEval14111 x
  · exact rowEval14112 x
  · exact rowEval14113 x
  · exact rowEval14114 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

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

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14145 x
  · exact rowEval14146 x
  · exact rowEval14147 x
  · exact rowEval14148 x
  · exact rowEval14149 x
  · exact rowEval14150 x
  · exact rowEval14151 x
  · exact rowEval14152 x
  · exact rowEval14153 x
  · exact rowEval14154 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14155 x
  · exact rowEval14156 x
  · exact rowEval14157 x
  · exact rowEval14158 x
  · exact rowEval14159 x
  · exact rowEval14160 x
  · exact rowEval14161 x
  · exact rowEval14162 x
  · exact rowEval14163 x
  · exact rowEval14164 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval14165 x
  · exact rowEval14166 x
  · exact rowEval14167 x
  · exact rowEval14168 x
  · exact rowEval14169 x
  · exact rowEval14170 x
  · exact rowEval14171 x
  · exact rowEval14172 x
  · exact rowEval14173 x
  · exact rowEval14174 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

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

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14185 x
  · exact rowEval14186 x
  · exact rowEval14187 x
  · exact rowEval14188 x
  · exact rowEval14189 x
  · exact rowEval14190 x
  · exact rowEval14191 x
  · exact rowEval14192 x
  · exact rowEval14193 x
  · exact rowEval14194 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

theorem entryCheck9_9 : entry9_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_9 k)) := by decide +kernel

theorem rowsSound9_9 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval14195 x
  · exact rowEval14196 x
  · exact rowEval14197 x
  · exact rowEval14198 x
  · exact rowEval14199 x
  · exact rowEval14200 x
  · exact rowEval14201 x
  · exact rowEval14202 x
  · exact rowEval14203 x
  · exact rowEval14204 x

theorem entryEval9_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_9 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck9_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_9]

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

theorem entryEvalRow9_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 9 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 9).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval9_0 B hB
  · exact entryEval9_1 B hB
  · exact entryEval9_2 B hB
  · exact entryEval9_3 B hB
  · exact entryEval9_4 B hB
  · exact entryEval9_5 B hB
  · exact entryEval9_6 B hB
  · exact entryEval9_7 B hB
  · exact entryEval9_8 B hB
  · exact entryEval9_9 B hB
  · exact (entryEval10_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e_oai
