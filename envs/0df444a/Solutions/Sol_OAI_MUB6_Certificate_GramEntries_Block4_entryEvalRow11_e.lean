-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:54:26.912332+00:00
-- url     : https://prove2.me/submissions/ac3641bd-46cf-4b21-a1e8-78b73ee83c1c

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval11_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval11_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_11_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14601 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form0 = rawRow14601 := by decide +kernel

theorem rowCheck14601 : row14601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14601 := by decide +kernel

theorem rowEval14601 (x : Key → ℝ) : Integer.Sparse.eval row14601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14601, Integer.Sparse.eval_collectBalanced, rawRowCheck14601]

theorem rawRowCheck14602 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form0 = rawRow14602 := by decide +kernel

theorem rowCheck14602 : row14602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14602 := by decide +kernel

theorem rowEval14602 (x : Key → ℝ) : Integer.Sparse.eval row14602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14602, Integer.Sparse.eval_collectBalanced, rawRowCheck14602]

theorem rawRowCheck14603 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form0 = rawRow14603 := by decide +kernel

theorem rowCheck14603 : row14603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14603 := by decide +kernel

theorem rowEval14603 (x : Key → ℝ) : Integer.Sparse.eval row14603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14603, Integer.Sparse.eval_collectBalanced, rawRowCheck14603]

theorem rawRowCheck14604 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow14604 := by decide +kernel

theorem rowCheck14604 : row14604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14604 := by decide +kernel

theorem rowEval14604 (x : Key → ℝ) : Integer.Sparse.eval row14604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14604, Integer.Sparse.eval_collectBalanced, rawRowCheck14604]

theorem rawRowCheck14605 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form0 = rawRow14605 := by decide +kernel

theorem rowCheck14605 : row14605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14605 := by decide +kernel

theorem rowEval14605 (x : Key → ℝ) : Integer.Sparse.eval row14605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14605, Integer.Sparse.eval_collectBalanced, rawRowCheck14605]

theorem rawRowCheck14606 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form0 = rawRow14606 := by decide +kernel

theorem rowCheck14606 : row14606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14606 := by decide +kernel

theorem rowEval14606 (x : Key → ℝ) : Integer.Sparse.eval row14606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14606, Integer.Sparse.eval_collectBalanced, rawRowCheck14606]

theorem rawRowCheck14607 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form0 = rawRow14607 := by decide +kernel

theorem rowCheck14607 : row14607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14607 := by decide +kernel

theorem rowEval14607 (x : Key → ℝ) : Integer.Sparse.eval row14607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14607, Integer.Sparse.eval_collectBalanced, rawRowCheck14607]

theorem rawRowCheck14608 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form0 = rawRow14608 := by decide +kernel

theorem rowCheck14608 : row14608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14608 := by decide +kernel

theorem rowEval14608 (x : Key → ℝ) : Integer.Sparse.eval row14608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14608, Integer.Sparse.eval_collectBalanced, rawRowCheck14608]

theorem rawRowCheck14609 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form0 = rawRow14609 := by decide +kernel

theorem rowCheck14609 : row14609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14609 := by decide +kernel

theorem rowEval14609 (x : Key → ℝ) : Integer.Sparse.eval row14609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14609, Integer.Sparse.eval_collectBalanced, rawRowCheck14609]

theorem rawRowCheck14610 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form0 = rawRow14610 := by decide +kernel

theorem rowCheck14610 : row14610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14610 := by decide +kernel

theorem rowEval14610 (x : Key → ℝ) : Integer.Sparse.eval row14610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14610, Integer.Sparse.eval_collectBalanced, rawRowCheck14610]

theorem rawRowCheck14611 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form0 = rawRow14611 := by decide +kernel

theorem rowCheck14611 : row14611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14611 := by decide +kernel

theorem rowEval14611 (x : Key → ℝ) : Integer.Sparse.eval row14611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14611, Integer.Sparse.eval_collectBalanced, rawRowCheck14611]

theorem rawRowCheck14612 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form0 = rawRow14612 := by decide +kernel

theorem rowCheck14612 : row14612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14612 := by decide +kernel

theorem rowEval14612 (x : Key → ℝ) : Integer.Sparse.eval row14612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14612, Integer.Sparse.eval_collectBalanced, rawRowCheck14612]

theorem rawRowCheck14613 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form0 = rawRow14613 := by decide +kernel

theorem rowCheck14613 : row14613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14613 := by decide +kernel

theorem rowEval14613 (x : Key → ℝ) : Integer.Sparse.eval row14613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14613, Integer.Sparse.eval_collectBalanced, rawRowCheck14613]

theorem rawRowCheck14614 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form0 = rawRow14614 := by decide +kernel

theorem rowCheck14614 : row14614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14614 := by decide +kernel

theorem rowEval14614 (x : Key → ℝ) : Integer.Sparse.eval row14614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14614, Integer.Sparse.eval_collectBalanced, rawRowCheck14614]

theorem rawRowCheck14615 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form0 = rawRow14615 := by decide +kernel

theorem rowCheck14615 : row14615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14615 := by decide +kernel

theorem rowEval14615 (x : Key → ℝ) : Integer.Sparse.eval row14615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14615, Integer.Sparse.eval_collectBalanced, rawRowCheck14615]

theorem rawRowCheck14616 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form0 = rawRow14616 := by decide +kernel

theorem rowCheck14616 : row14616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14616 := by decide +kernel

theorem rowEval14616 (x : Key → ℝ) : Integer.Sparse.eval row14616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14616, Integer.Sparse.eval_collectBalanced, rawRowCheck14616]

theorem rawRowCheck14617 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow14617 := by decide +kernel

theorem rowCheck14617 : row14617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14617 := by decide +kernel

theorem rowEval14617 (x : Key → ℝ) : Integer.Sparse.eval row14617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14617, Integer.Sparse.eval_collectBalanced, rawRowCheck14617]

theorem rawRowCheck14618 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form0 = rawRow14618 := by decide +kernel

theorem rowCheck14618 : row14618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14618 := by decide +kernel

theorem rowEval14618 (x : Key → ℝ) : Integer.Sparse.eval row14618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14618, Integer.Sparse.eval_collectBalanced, rawRowCheck14618]

theorem rawRowCheck14619 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form0 = rawRow14619 := by decide +kernel

theorem rowCheck14619 : row14619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14619 := by decide +kernel

theorem rowEval14619 (x : Key → ℝ) : Integer.Sparse.eval row14619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14619, Integer.Sparse.eval_collectBalanced, rawRowCheck14619]

theorem rawRowCheck14620 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form0 = rawRow14620 := by decide +kernel

theorem rowCheck14620 : row14620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14620 := by decide +kernel

theorem rowEval14620 (x : Key → ℝ) : Integer.Sparse.eval row14620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14620, Integer.Sparse.eval_collectBalanced, rawRowCheck14620]

theorem rawRowCheck14621 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form1 = rawRow14621 := by decide +kernel

theorem rowCheck14621 : row14621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14621 := by decide +kernel

theorem rowEval14621 (x : Key → ℝ) : Integer.Sparse.eval row14621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14621, Integer.Sparse.eval_collectBalanced, rawRowCheck14621]

theorem rawRowCheck14622 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form1 = rawRow14622 := by decide +kernel

theorem rowCheck14622 : row14622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14622 := by decide +kernel

theorem rowEval14622 (x : Key → ℝ) : Integer.Sparse.eval row14622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14622, Integer.Sparse.eval_collectBalanced, rawRowCheck14622]

theorem rawRowCheck14623 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form1 = rawRow14623 := by decide +kernel

theorem rowCheck14623 : row14623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14623 := by decide +kernel

theorem rowEval14623 (x : Key → ℝ) : Integer.Sparse.eval row14623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14623, Integer.Sparse.eval_collectBalanced, rawRowCheck14623]

theorem rawRowCheck14624 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow14624 := by decide +kernel

theorem rowCheck14624 : row14624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14624 := by decide +kernel

theorem rowEval14624 (x : Key → ℝ) : Integer.Sparse.eval row14624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14624, Integer.Sparse.eval_collectBalanced, rawRowCheck14624]

theorem rawRowCheck14625 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form1 = rawRow14625 := by decide +kernel

theorem rowCheck14625 : row14625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14625 := by decide +kernel

theorem rowEval14625 (x : Key → ℝ) : Integer.Sparse.eval row14625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14625, Integer.Sparse.eval_collectBalanced, rawRowCheck14625]

theorem rawRowCheck14626 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form1 = rawRow14626 := by decide +kernel

theorem rowCheck14626 : row14626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14626 := by decide +kernel

theorem rowEval14626 (x : Key → ℝ) : Integer.Sparse.eval row14626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14626, Integer.Sparse.eval_collectBalanced, rawRowCheck14626]

theorem rawRowCheck14627 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form1 = rawRow14627 := by decide +kernel

theorem rowCheck14627 : row14627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14627 := by decide +kernel

theorem rowEval14627 (x : Key → ℝ) : Integer.Sparse.eval row14627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14627, Integer.Sparse.eval_collectBalanced, rawRowCheck14627]

theorem rawRowCheck14628 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form1 = rawRow14628 := by decide +kernel

theorem rowCheck14628 : row14628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14628 := by decide +kernel

theorem rowEval14628 (x : Key → ℝ) : Integer.Sparse.eval row14628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14628, Integer.Sparse.eval_collectBalanced, rawRowCheck14628]

theorem rawRowCheck14629 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form1 = rawRow14629 := by decide +kernel

theorem rowCheck14629 : row14629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14629 := by decide +kernel

theorem rowEval14629 (x : Key → ℝ) : Integer.Sparse.eval row14629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14629, Integer.Sparse.eval_collectBalanced, rawRowCheck14629]

theorem rawRowCheck14630 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form1 = rawRow14630 := by decide +kernel

theorem rowCheck14630 : row14630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14630 := by decide +kernel

theorem rowEval14630 (x : Key → ℝ) : Integer.Sparse.eval row14630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14630, Integer.Sparse.eval_collectBalanced, rawRowCheck14630]

theorem rawRowCheck14631 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form1 = rawRow14631 := by decide +kernel

theorem rowCheck14631 : row14631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14631 := by decide +kernel

theorem rowEval14631 (x : Key → ℝ) : Integer.Sparse.eval row14631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14631, Integer.Sparse.eval_collectBalanced, rawRowCheck14631]

theorem rawRowCheck14632 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form1 = rawRow14632 := by decide +kernel

theorem rowCheck14632 : row14632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14632 := by decide +kernel

theorem rowEval14632 (x : Key → ℝ) : Integer.Sparse.eval row14632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14632, Integer.Sparse.eval_collectBalanced, rawRowCheck14632]

theorem rawRowCheck14633 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form1 = rawRow14633 := by decide +kernel

theorem rowCheck14633 : row14633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14633 := by decide +kernel

theorem rowEval14633 (x : Key → ℝ) : Integer.Sparse.eval row14633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14633, Integer.Sparse.eval_collectBalanced, rawRowCheck14633]

theorem rawRowCheck14634 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form1 = rawRow14634 := by decide +kernel

theorem rowCheck14634 : row14634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14634 := by decide +kernel

theorem rowEval14634 (x : Key → ℝ) : Integer.Sparse.eval row14634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14634, Integer.Sparse.eval_collectBalanced, rawRowCheck14634]

theorem rawRowCheck14635 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form1 = rawRow14635 := by decide +kernel

theorem rowCheck14635 : row14635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14635 := by decide +kernel

theorem rowEval14635 (x : Key → ℝ) : Integer.Sparse.eval row14635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14635, Integer.Sparse.eval_collectBalanced, rawRowCheck14635]

theorem rawRowCheck14636 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form1 = rawRow14636 := by decide +kernel

theorem rowCheck14636 : row14636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14636 := by decide +kernel

theorem rowEval14636 (x : Key → ℝ) : Integer.Sparse.eval row14636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14636, Integer.Sparse.eval_collectBalanced, rawRowCheck14636]

theorem rawRowCheck14637 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow14637 := by decide +kernel

theorem rowCheck14637 : row14637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14637 := by decide +kernel

theorem rowEval14637 (x : Key → ℝ) : Integer.Sparse.eval row14637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14637, Integer.Sparse.eval_collectBalanced, rawRowCheck14637]

theorem rawRowCheck14638 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form1 = rawRow14638 := by decide +kernel

theorem rowCheck14638 : row14638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14638 := by decide +kernel

theorem rowEval14638 (x : Key → ℝ) : Integer.Sparse.eval row14638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14638, Integer.Sparse.eval_collectBalanced, rawRowCheck14638]

theorem rawRowCheck14639 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form1 = rawRow14639 := by decide +kernel

theorem rowCheck14639 : row14639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14639 := by decide +kernel

theorem rowEval14639 (x : Key → ℝ) : Integer.Sparse.eval row14639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck14639, Integer.Sparse.eval_collectBalanced, rawRowCheck14639]

theorem rawRowCheck14640 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form1 = rawRow14640 := by decide +kernel

theorem rowCheck14640 : row14640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14640 := by decide +kernel

theorem rowEval14640 (x : Key → ℝ) : Integer.Sparse.eval row14640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck14640, Integer.Sparse.eval_collectBalanced, rawRowCheck14640]

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

theorem rawRowCheck14681 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form4 = rawRow14681 := by decide +kernel

theorem rowCheck14681 : row14681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14681 := by decide +kernel

theorem rowEval14681 (x : Key → ℝ) : Integer.Sparse.eval row14681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14681, Integer.Sparse.eval_collectBalanced, rawRowCheck14681]

theorem rawRowCheck14682 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form4 = rawRow14682 := by decide +kernel

theorem rowCheck14682 : row14682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14682 := by decide +kernel

theorem rowEval14682 (x : Key → ℝ) : Integer.Sparse.eval row14682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14682, Integer.Sparse.eval_collectBalanced, rawRowCheck14682]

theorem rawRowCheck14683 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form4 = rawRow14683 := by decide +kernel

theorem rowCheck14683 : row14683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14683 := by decide +kernel

theorem rowEval14683 (x : Key → ℝ) : Integer.Sparse.eval row14683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14683, Integer.Sparse.eval_collectBalanced, rawRowCheck14683]

theorem rawRowCheck14684 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14684 := by decide +kernel

theorem rowCheck14684 : row14684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14684 := by decide +kernel

theorem rowEval14684 (x : Key → ℝ) : Integer.Sparse.eval row14684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14684, Integer.Sparse.eval_collectBalanced, rawRowCheck14684]

theorem rawRowCheck14685 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form4 = rawRow14685 := by decide +kernel

theorem rowCheck14685 : row14685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14685 := by decide +kernel

theorem rowEval14685 (x : Key → ℝ) : Integer.Sparse.eval row14685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14685, Integer.Sparse.eval_collectBalanced, rawRowCheck14685]

theorem rawRowCheck14686 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form4 = rawRow14686 := by decide +kernel

theorem rowCheck14686 : row14686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14686 := by decide +kernel

theorem rowEval14686 (x : Key → ℝ) : Integer.Sparse.eval row14686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14686, Integer.Sparse.eval_collectBalanced, rawRowCheck14686]

theorem rawRowCheck14687 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form4 = rawRow14687 := by decide +kernel

theorem rowCheck14687 : row14687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14687 := by decide +kernel

theorem rowEval14687 (x : Key → ℝ) : Integer.Sparse.eval row14687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14687, Integer.Sparse.eval_collectBalanced, rawRowCheck14687]

theorem rawRowCheck14688 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form4 = rawRow14688 := by decide +kernel

theorem rowCheck14688 : row14688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14688 := by decide +kernel

theorem rowEval14688 (x : Key → ℝ) : Integer.Sparse.eval row14688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14688, Integer.Sparse.eval_collectBalanced, rawRowCheck14688]

theorem rawRowCheck14689 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form4 = rawRow14689 := by decide +kernel

theorem rowCheck14689 : row14689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14689 := by decide +kernel

theorem rowEval14689 (x : Key → ℝ) : Integer.Sparse.eval row14689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14689, Integer.Sparse.eval_collectBalanced, rawRowCheck14689]

theorem rawRowCheck14690 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form4 = rawRow14690 := by decide +kernel

theorem rowCheck14690 : row14690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14690 := by decide +kernel

theorem rowEval14690 (x : Key → ℝ) : Integer.Sparse.eval row14690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14690, Integer.Sparse.eval_collectBalanced, rawRowCheck14690]

theorem rawRowCheck14691 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form4 = rawRow14691 := by decide +kernel

theorem rowCheck14691 : row14691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14691 := by decide +kernel

theorem rowEval14691 (x : Key → ℝ) : Integer.Sparse.eval row14691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14691, Integer.Sparse.eval_collectBalanced, rawRowCheck14691]

theorem rawRowCheck14692 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form4 = rawRow14692 := by decide +kernel

theorem rowCheck14692 : row14692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14692 := by decide +kernel

theorem rowEval14692 (x : Key → ℝ) : Integer.Sparse.eval row14692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14692, Integer.Sparse.eval_collectBalanced, rawRowCheck14692]

theorem rawRowCheck14693 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form4 = rawRow14693 := by decide +kernel

theorem rowCheck14693 : row14693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14693 := by decide +kernel

theorem rowEval14693 (x : Key → ℝ) : Integer.Sparse.eval row14693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14693, Integer.Sparse.eval_collectBalanced, rawRowCheck14693]

theorem rawRowCheck14694 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form4 = rawRow14694 := by decide +kernel

theorem rowCheck14694 : row14694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14694 := by decide +kernel

theorem rowEval14694 (x : Key → ℝ) : Integer.Sparse.eval row14694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14694, Integer.Sparse.eval_collectBalanced, rawRowCheck14694]

theorem rawRowCheck14695 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form4 = rawRow14695 := by decide +kernel

theorem rowCheck14695 : row14695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14695 := by decide +kernel

theorem rowEval14695 (x : Key → ℝ) : Integer.Sparse.eval row14695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14695, Integer.Sparse.eval_collectBalanced, rawRowCheck14695]

theorem rawRowCheck14696 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form4 = rawRow14696 := by decide +kernel

theorem rowCheck14696 : row14696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14696 := by decide +kernel

theorem rowEval14696 (x : Key → ℝ) : Integer.Sparse.eval row14696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14696, Integer.Sparse.eval_collectBalanced, rawRowCheck14696]

theorem rawRowCheck14697 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14697 := by decide +kernel

theorem rowCheck14697 : row14697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14697 := by decide +kernel

theorem rowEval14697 (x : Key → ℝ) : Integer.Sparse.eval row14697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14697, Integer.Sparse.eval_collectBalanced, rawRowCheck14697]

theorem rawRowCheck14698 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form4 = rawRow14698 := by decide +kernel

theorem rowCheck14698 : row14698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14698 := by decide +kernel

theorem rowEval14698 (x : Key → ℝ) : Integer.Sparse.eval row14698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14698, Integer.Sparse.eval_collectBalanced, rawRowCheck14698]

theorem rawRowCheck14699 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form4 = rawRow14699 := by decide +kernel

theorem rowCheck14699 : row14699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14699 := by decide +kernel

theorem rowEval14699 (x : Key → ℝ) : Integer.Sparse.eval row14699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14699, Integer.Sparse.eval_collectBalanced, rawRowCheck14699]

theorem rawRowCheck14700 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form4 = rawRow14700 := by decide +kernel

theorem rowCheck14700 : row14700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14700 := by decide +kernel

theorem rowEval14700 (x : Key → ℝ) : Integer.Sparse.eval row14700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14700, Integer.Sparse.eval_collectBalanced, rawRowCheck14700]

theorem rawRowCheck14701 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form5 = rawRow14701 := by decide +kernel

theorem rowCheck14701 : row14701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14701 := by decide +kernel

theorem rowEval14701 (x : Key → ℝ) : Integer.Sparse.eval row14701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14701, Integer.Sparse.eval_collectBalanced, rawRowCheck14701]

theorem rawRowCheck14702 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form5 = rawRow14702 := by decide +kernel

theorem rowCheck14702 : row14702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14702 := by decide +kernel

theorem rowEval14702 (x : Key → ℝ) : Integer.Sparse.eval row14702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14702, Integer.Sparse.eval_collectBalanced, rawRowCheck14702]

theorem rawRowCheck14703 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form5 = rawRow14703 := by decide +kernel

theorem rowCheck14703 : row14703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14703 := by decide +kernel

theorem rowEval14703 (x : Key → ℝ) : Integer.Sparse.eval row14703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14703, Integer.Sparse.eval_collectBalanced, rawRowCheck14703]

theorem rawRowCheck14704 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14704 := by decide +kernel

theorem rowCheck14704 : row14704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14704 := by decide +kernel

theorem rowEval14704 (x : Key → ℝ) : Integer.Sparse.eval row14704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14704, Integer.Sparse.eval_collectBalanced, rawRowCheck14704]

theorem rawRowCheck14705 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form5 = rawRow14705 := by decide +kernel

theorem rowCheck14705 : row14705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14705 := by decide +kernel

theorem rowEval14705 (x : Key → ℝ) : Integer.Sparse.eval row14705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14705, Integer.Sparse.eval_collectBalanced, rawRowCheck14705]

theorem rawRowCheck14706 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form5 = rawRow14706 := by decide +kernel

theorem rowCheck14706 : row14706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14706 := by decide +kernel

theorem rowEval14706 (x : Key → ℝ) : Integer.Sparse.eval row14706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14706, Integer.Sparse.eval_collectBalanced, rawRowCheck14706]

theorem rawRowCheck14707 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form5 = rawRow14707 := by decide +kernel

theorem rowCheck14707 : row14707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14707 := by decide +kernel

theorem rowEval14707 (x : Key → ℝ) : Integer.Sparse.eval row14707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14707, Integer.Sparse.eval_collectBalanced, rawRowCheck14707]

theorem rawRowCheck14708 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form5 = rawRow14708 := by decide +kernel

theorem rowCheck14708 : row14708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14708 := by decide +kernel

theorem rowEval14708 (x : Key → ℝ) : Integer.Sparse.eval row14708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14708, Integer.Sparse.eval_collectBalanced, rawRowCheck14708]

theorem rawRowCheck14709 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form5 = rawRow14709 := by decide +kernel

theorem rowCheck14709 : row14709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14709 := by decide +kernel

theorem rowEval14709 (x : Key → ℝ) : Integer.Sparse.eval row14709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14709, Integer.Sparse.eval_collectBalanced, rawRowCheck14709]

theorem rawRowCheck14710 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form5 = rawRow14710 := by decide +kernel

theorem rowCheck14710 : row14710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14710 := by decide +kernel

theorem rowEval14710 (x : Key → ℝ) : Integer.Sparse.eval row14710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14710, Integer.Sparse.eval_collectBalanced, rawRowCheck14710]

theorem rawRowCheck14711 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form5 = rawRow14711 := by decide +kernel

theorem rowCheck14711 : row14711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14711 := by decide +kernel

theorem rowEval14711 (x : Key → ℝ) : Integer.Sparse.eval row14711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14711, Integer.Sparse.eval_collectBalanced, rawRowCheck14711]

theorem rawRowCheck14712 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form5 = rawRow14712 := by decide +kernel

theorem rowCheck14712 : row14712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14712 := by decide +kernel

theorem rowEval14712 (x : Key → ℝ) : Integer.Sparse.eval row14712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14712, Integer.Sparse.eval_collectBalanced, rawRowCheck14712]

theorem rawRowCheck14713 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form5 = rawRow14713 := by decide +kernel

theorem rowCheck14713 : row14713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14713 := by decide +kernel

theorem rowEval14713 (x : Key → ℝ) : Integer.Sparse.eval row14713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14713, Integer.Sparse.eval_collectBalanced, rawRowCheck14713]

theorem rawRowCheck14714 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form5 = rawRow14714 := by decide +kernel

theorem rowCheck14714 : row14714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14714 := by decide +kernel

theorem rowEval14714 (x : Key → ℝ) : Integer.Sparse.eval row14714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14714, Integer.Sparse.eval_collectBalanced, rawRowCheck14714]

theorem rawRowCheck14715 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form5 = rawRow14715 := by decide +kernel

theorem rowCheck14715 : row14715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14715 := by decide +kernel

theorem rowEval14715 (x : Key → ℝ) : Integer.Sparse.eval row14715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14715, Integer.Sparse.eval_collectBalanced, rawRowCheck14715]

theorem rawRowCheck14716 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form5 = rawRow14716 := by decide +kernel

theorem rowCheck14716 : row14716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14716 := by decide +kernel

theorem rowEval14716 (x : Key → ℝ) : Integer.Sparse.eval row14716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14716, Integer.Sparse.eval_collectBalanced, rawRowCheck14716]

theorem rawRowCheck14717 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14717 := by decide +kernel

theorem rowCheck14717 : row14717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14717 := by decide +kernel

theorem rowEval14717 (x : Key → ℝ) : Integer.Sparse.eval row14717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14717, Integer.Sparse.eval_collectBalanced, rawRowCheck14717]

theorem rawRowCheck14718 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form5 = rawRow14718 := by decide +kernel

theorem rowCheck14718 : row14718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14718 := by decide +kernel

theorem rowEval14718 (x : Key → ℝ) : Integer.Sparse.eval row14718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14718, Integer.Sparse.eval_collectBalanced, rawRowCheck14718]

theorem rawRowCheck14719 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form5 = rawRow14719 := by decide +kernel

theorem rowCheck14719 : row14719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14719 := by decide +kernel

theorem rowEval14719 (x : Key → ℝ) : Integer.Sparse.eval row14719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14719, Integer.Sparse.eval_collectBalanced, rawRowCheck14719]

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

theorem rawRowCheck14720 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form5 = rawRow14720 := by decide +kernel

theorem rowCheck14720 : row14720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14720 := by decide +kernel

theorem rowEval14720 (x : Key → ℝ) : Integer.Sparse.eval row14720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14720, Integer.Sparse.eval_collectBalanced, rawRowCheck14720]

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

theorem rawRowCheck14761 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form8 = rawRow14761 := by decide +kernel

theorem rowCheck14761 : row14761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14761 := by decide +kernel

theorem rowEval14761 (x : Key → ℝ) : Integer.Sparse.eval row14761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14761, Integer.Sparse.eval_collectBalanced, rawRowCheck14761]

theorem rawRowCheck14762 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form8 = rawRow14762 := by decide +kernel

theorem rowCheck14762 : row14762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14762 := by decide +kernel

theorem rowEval14762 (x : Key → ℝ) : Integer.Sparse.eval row14762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14762, Integer.Sparse.eval_collectBalanced, rawRowCheck14762]

theorem rawRowCheck14763 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form8 = rawRow14763 := by decide +kernel

theorem rowCheck14763 : row14763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14763 := by decide +kernel

theorem rowEval14763 (x : Key → ℝ) : Integer.Sparse.eval row14763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14763, Integer.Sparse.eval_collectBalanced, rawRowCheck14763]

theorem rawRowCheck14764 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14764 := by decide +kernel

theorem rowCheck14764 : row14764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14764 := by decide +kernel

theorem rowEval14764 (x : Key → ℝ) : Integer.Sparse.eval row14764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14764, Integer.Sparse.eval_collectBalanced, rawRowCheck14764]

theorem rawRowCheck14765 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form8 = rawRow14765 := by decide +kernel

theorem rowCheck14765 : row14765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14765 := by decide +kernel

theorem rowEval14765 (x : Key → ℝ) : Integer.Sparse.eval row14765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14765, Integer.Sparse.eval_collectBalanced, rawRowCheck14765]

theorem rawRowCheck14766 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form8 = rawRow14766 := by decide +kernel

theorem rowCheck14766 : row14766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14766 := by decide +kernel

theorem rowEval14766 (x : Key → ℝ) : Integer.Sparse.eval row14766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14766, Integer.Sparse.eval_collectBalanced, rawRowCheck14766]

theorem rawRowCheck14767 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form8 = rawRow14767 := by decide +kernel

theorem rowCheck14767 : row14767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14767 := by decide +kernel

theorem rowEval14767 (x : Key → ℝ) : Integer.Sparse.eval row14767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14767, Integer.Sparse.eval_collectBalanced, rawRowCheck14767]

theorem rawRowCheck14768 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form8 = rawRow14768 := by decide +kernel

theorem rowCheck14768 : row14768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14768 := by decide +kernel

theorem rowEval14768 (x : Key → ℝ) : Integer.Sparse.eval row14768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14768, Integer.Sparse.eval_collectBalanced, rawRowCheck14768]

theorem rawRowCheck14769 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form8 = rawRow14769 := by decide +kernel

theorem rowCheck14769 : row14769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14769 := by decide +kernel

theorem rowEval14769 (x : Key → ℝ) : Integer.Sparse.eval row14769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14769, Integer.Sparse.eval_collectBalanced, rawRowCheck14769]

theorem rawRowCheck14770 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form8 = rawRow14770 := by decide +kernel

theorem rowCheck14770 : row14770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14770 := by decide +kernel

theorem rowEval14770 (x : Key → ℝ) : Integer.Sparse.eval row14770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14770, Integer.Sparse.eval_collectBalanced, rawRowCheck14770]

theorem rawRowCheck14771 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form8 = rawRow14771 := by decide +kernel

theorem rowCheck14771 : row14771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14771 := by decide +kernel

theorem rowEval14771 (x : Key → ℝ) : Integer.Sparse.eval row14771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14771, Integer.Sparse.eval_collectBalanced, rawRowCheck14771]

theorem rawRowCheck14772 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form8 = rawRow14772 := by decide +kernel

theorem rowCheck14772 : row14772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14772 := by decide +kernel

theorem rowEval14772 (x : Key → ℝ) : Integer.Sparse.eval row14772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14772, Integer.Sparse.eval_collectBalanced, rawRowCheck14772]

theorem rawRowCheck14773 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form8 = rawRow14773 := by decide +kernel

theorem rowCheck14773 : row14773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14773 := by decide +kernel

theorem rowEval14773 (x : Key → ℝ) : Integer.Sparse.eval row14773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14773, Integer.Sparse.eval_collectBalanced, rawRowCheck14773]

theorem rawRowCheck14774 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form8 = rawRow14774 := by decide +kernel

theorem rowCheck14774 : row14774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14774 := by decide +kernel

theorem rowEval14774 (x : Key → ℝ) : Integer.Sparse.eval row14774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14774, Integer.Sparse.eval_collectBalanced, rawRowCheck14774]

theorem rawRowCheck14775 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form8 = rawRow14775 := by decide +kernel

theorem rowCheck14775 : row14775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14775 := by decide +kernel

theorem rowEval14775 (x : Key → ℝ) : Integer.Sparse.eval row14775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14775, Integer.Sparse.eval_collectBalanced, rawRowCheck14775]

theorem rawRowCheck14776 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form8 = rawRow14776 := by decide +kernel

theorem rowCheck14776 : row14776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14776 := by decide +kernel

theorem rowEval14776 (x : Key → ℝ) : Integer.Sparse.eval row14776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14776, Integer.Sparse.eval_collectBalanced, rawRowCheck14776]

theorem rawRowCheck14777 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14777 := by decide +kernel

theorem rowCheck14777 : row14777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14777 := by decide +kernel

theorem rowEval14777 (x : Key → ℝ) : Integer.Sparse.eval row14777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14777, Integer.Sparse.eval_collectBalanced, rawRowCheck14777]

theorem rawRowCheck14778 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form8 = rawRow14778 := by decide +kernel

theorem rowCheck14778 : row14778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14778 := by decide +kernel

theorem rowEval14778 (x : Key → ℝ) : Integer.Sparse.eval row14778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14778, Integer.Sparse.eval_collectBalanced, rawRowCheck14778]

theorem rawRowCheck14779 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form8 = rawRow14779 := by decide +kernel

theorem rowCheck14779 : row14779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14779 := by decide +kernel

theorem rowEval14779 (x : Key → ℝ) : Integer.Sparse.eval row14779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14779, Integer.Sparse.eval_collectBalanced, rawRowCheck14779]

theorem rawRowCheck14780 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form8 = rawRow14780 := by decide +kernel

theorem rowCheck14780 : row14780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14780 := by decide +kernel

theorem rowEval14780 (x : Key → ℝ) : Integer.Sparse.eval row14780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14780, Integer.Sparse.eval_collectBalanced, rawRowCheck14780]

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

theorem rawRowCheck14821 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form11 = rawRow14821 := by decide +kernel

theorem rowCheck14821 : row14821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14821 := by decide +kernel

theorem rowEval14821 (x : Key → ℝ) : Integer.Sparse.eval row14821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14821, Integer.Sparse.eval_collectBalanced, rawRowCheck14821]

theorem rawRowCheck14822 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form11 = rawRow14822 := by decide +kernel

theorem rowCheck14822 : row14822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14822 := by decide +kernel

theorem rowEval14822 (x : Key → ℝ) : Integer.Sparse.eval row14822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14822, Integer.Sparse.eval_collectBalanced, rawRowCheck14822]

theorem rawRowCheck14823 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form11 = rawRow14823 := by decide +kernel

theorem rowCheck14823 : row14823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14823 := by decide +kernel

theorem rowEval14823 (x : Key → ℝ) : Integer.Sparse.eval row14823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14823, Integer.Sparse.eval_collectBalanced, rawRowCheck14823]

theorem rawRowCheck14824 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form11 = rawRow14824 := by decide +kernel

theorem rowCheck14824 : row14824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14824 := by decide +kernel

theorem rowEval14824 (x : Key → ℝ) : Integer.Sparse.eval row14824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14824, Integer.Sparse.eval_collectBalanced, rawRowCheck14824]

theorem rawRowCheck14825 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form11 = rawRow14825 := by decide +kernel

theorem rowCheck14825 : row14825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14825 := by decide +kernel

theorem rowEval14825 (x : Key → ℝ) : Integer.Sparse.eval row14825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14825, Integer.Sparse.eval_collectBalanced, rawRowCheck14825]

theorem rawRowCheck14826 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form11 = rawRow14826 := by decide +kernel

theorem rowCheck14826 : row14826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14826 := by decide +kernel

theorem rowEval14826 (x : Key → ℝ) : Integer.Sparse.eval row14826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14826, Integer.Sparse.eval_collectBalanced, rawRowCheck14826]

theorem rawRowCheck14827 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form11 = rawRow14827 := by decide +kernel

theorem rowCheck14827 : row14827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14827 := by decide +kernel

theorem rowEval14827 (x : Key → ℝ) : Integer.Sparse.eval row14827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14827, Integer.Sparse.eval_collectBalanced, rawRowCheck14827]

theorem rawRowCheck14828 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form11 = rawRow14828 := by decide +kernel

theorem rowCheck14828 : row14828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14828 := by decide +kernel

theorem rowEval14828 (x : Key → ℝ) : Integer.Sparse.eval row14828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14828, Integer.Sparse.eval_collectBalanced, rawRowCheck14828]

theorem rawRowCheck14829 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form11 = rawRow14829 := by decide +kernel

theorem rowCheck14829 : row14829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14829 := by decide +kernel

theorem rowEval14829 (x : Key → ℝ) : Integer.Sparse.eval row14829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14829, Integer.Sparse.eval_collectBalanced, rawRowCheck14829]

theorem rawRowCheck14830 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form11 = rawRow14830 := by decide +kernel

theorem rowCheck14830 : row14830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14830 := by decide +kernel

theorem rowEval14830 (x : Key → ℝ) : Integer.Sparse.eval row14830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14830, Integer.Sparse.eval_collectBalanced, rawRowCheck14830]

theorem rawRowCheck14831 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form11 = rawRow14831 := by decide +kernel

theorem rowCheck14831 : row14831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14831 := by decide +kernel

theorem rowEval14831 (x : Key → ℝ) : Integer.Sparse.eval row14831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14831, Integer.Sparse.eval_collectBalanced, rawRowCheck14831]

theorem rawRowCheck14832 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form11 = rawRow14832 := by decide +kernel

theorem rowCheck14832 : row14832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14832 := by decide +kernel

theorem rowEval14832 (x : Key → ℝ) : Integer.Sparse.eval row14832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14832, Integer.Sparse.eval_collectBalanced, rawRowCheck14832]

theorem rawRowCheck14833 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form11 = rawRow14833 := by decide +kernel

theorem rowCheck14833 : row14833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14833 := by decide +kernel

theorem rowEval14833 (x : Key → ℝ) : Integer.Sparse.eval row14833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14833, Integer.Sparse.eval_collectBalanced, rawRowCheck14833]

theorem rawRowCheck14834 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form11 = rawRow14834 := by decide +kernel

theorem rowCheck14834 : row14834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14834 := by decide +kernel

theorem rowEval14834 (x : Key → ℝ) : Integer.Sparse.eval row14834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14834, Integer.Sparse.eval_collectBalanced, rawRowCheck14834]

theorem rawRowCheck14835 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form11 = rawRow14835 := by decide +kernel

theorem rowCheck14835 : row14835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14835 := by decide +kernel

theorem rowEval14835 (x : Key → ℝ) : Integer.Sparse.eval row14835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14835, Integer.Sparse.eval_collectBalanced, rawRowCheck14835]

theorem rawRowCheck14836 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form11 = rawRow14836 := by decide +kernel

theorem rowCheck14836 : row14836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14836 := by decide +kernel

theorem rowEval14836 (x : Key → ℝ) : Integer.Sparse.eval row14836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14836, Integer.Sparse.eval_collectBalanced, rawRowCheck14836]

theorem rawRowCheck14837 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form11 = rawRow14837 := by decide +kernel

theorem rowCheck14837 : row14837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14837 := by decide +kernel

theorem rowEval14837 (x : Key → ℝ) : Integer.Sparse.eval row14837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14837, Integer.Sparse.eval_collectBalanced, rawRowCheck14837]

theorem rawRowCheck14838 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form11 = rawRow14838 := by decide +kernel

theorem rowCheck14838 : row14838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14838 := by decide +kernel

theorem rowEval14838 (x : Key → ℝ) : Integer.Sparse.eval row14838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14838, Integer.Sparse.eval_collectBalanced, rawRowCheck14838]

theorem rawRowCheck14839 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form11 = rawRow14839 := by decide +kernel

theorem rowCheck14839 : row14839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14839 := by decide +kernel

theorem rowEval14839 (x : Key → ℝ) : Integer.Sparse.eval row14839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14839, Integer.Sparse.eval_collectBalanced, rawRowCheck14839]

theorem rawRowCheck14840 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form11 = rawRow14840 := by decide +kernel

theorem rowCheck14840 : row14840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14840 := by decide +kernel

theorem rowEval14840 (x : Key → ℝ) : Integer.Sparse.eval row14840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14840, Integer.Sparse.eval_collectBalanced, rawRowCheck14840]

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

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14601 x
  · exact rowEval14602 x
  · exact rowEval14603 x
  · exact rowEval14604 x
  · exact rowEval14605 x
  · exact rowEval14606 x
  · exact rowEval14607 x
  · exact rowEval14608 x
  · exact rowEval14609 x
  · exact rowEval14610 x
  · exact rowEval14611 x
  · exact rowEval14612 x
  · exact rowEval14613 x
  · exact rowEval14614 x
  · exact rowEval14615 x
  · exact rowEval14616 x
  · exact rowEval14617 x
  · exact rowEval14618 x
  · exact rowEval14619 x
  · exact rowEval14620 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval14621 x
  · exact rowEval14622 x
  · exact rowEval14623 x
  · exact rowEval14624 x
  · exact rowEval14625 x
  · exact rowEval14626 x
  · exact rowEval14627 x
  · exact rowEval14628 x
  · exact rowEval14629 x
  · exact rowEval14630 x
  · exact rowEval14631 x
  · exact rowEval14632 x
  · exact rowEval14633 x
  · exact rowEval14634 x
  · exact rowEval14635 x
  · exact rowEval14636 x
  · exact rowEval14637 x
  · exact rowEval14638 x
  · exact rowEval14639 x
  · exact rowEval14640 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

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

theorem entryCheck11_4 : entry11_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_4 k)) := by decide +kernel

theorem rowsSound11_4 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14681 x
  · exact rowEval14682 x
  · exact rowEval14683 x
  · exact rowEval14684 x
  · exact rowEval14685 x
  · exact rowEval14686 x
  · exact rowEval14687 x
  · exact rowEval14688 x
  · exact rowEval14689 x
  · exact rowEval14690 x
  · exact rowEval14691 x
  · exact rowEval14692 x
  · exact rowEval14693 x
  · exact rowEval14694 x
  · exact rowEval14695 x
  · exact rowEval14696 x
  · exact rowEval14697 x
  · exact rowEval14698 x
  · exact rowEval14699 x
  · exact rowEval14700 x

theorem entryEval11_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_4 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck11_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_4]

theorem entryCheck11_5 : entry11_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_5 k)) := by decide +kernel

theorem rowsSound11_5 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14701 x
  · exact rowEval14702 x
  · exact rowEval14703 x
  · exact rowEval14704 x
  · exact rowEval14705 x
  · exact rowEval14706 x
  · exact rowEval14707 x
  · exact rowEval14708 x
  · exact rowEval14709 x
  · exact rowEval14710 x
  · exact rowEval14711 x
  · exact rowEval14712 x
  · exact rowEval14713 x
  · exact rowEval14714 x
  · exact rowEval14715 x
  · exact rowEval14716 x
  · exact rowEval14717 x
  · exact rowEval14718 x
  · exact rowEval14719 x
  · exact rowEval14720 x

theorem entryEval11_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_5 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck11_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_5]

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

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14761 x
  · exact rowEval14762 x
  · exact rowEval14763 x
  · exact rowEval14764 x
  · exact rowEval14765 x
  · exact rowEval14766 x
  · exact rowEval14767 x
  · exact rowEval14768 x
  · exact rowEval14769 x
  · exact rowEval14770 x
  · exact rowEval14771 x
  · exact rowEval14772 x
  · exact rowEval14773 x
  · exact rowEval14774 x
  · exact rowEval14775 x
  · exact rowEval14776 x
  · exact rowEval14777 x
  · exact rowEval14778 x
  · exact rowEval14779 x
  · exact rowEval14780 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

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

theorem entryCheck11_11 : entry11_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_11 k)) := by decide +kernel

theorem rowsSound11_11 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval14821 x
  · exact rowEval14822 x
  · exact rowEval14823 x
  · exact rowEval14824 x
  · exact rowEval14825 x
  · exact rowEval14826 x
  · exact rowEval14827 x
  · exact rowEval14828 x
  · exact rowEval14829 x
  · exact rowEval14830 x
  · exact rowEval14831 x
  · exact rowEval14832 x
  · exact rowEval14833 x
  · exact rowEval14834 x
  · exact rowEval14835 x
  · exact rowEval14836 x
  · exact rowEval14837 x
  · exact rowEval14838 x
  · exact rowEval14839 x
  · exact rowEval14840 x

theorem entryEval11_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_11 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck11_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_11]

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

theorem rawRowCheck17251 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form11 = rawRow17251 := by decide +kernel

theorem rowCheck17251 : row17251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17251 := by decide +kernel

theorem rowEval17251 (x : Key → ℝ) : Integer.Sparse.eval row17251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17251, Integer.Sparse.eval_collectBalanced, rawRowCheck17251]

theorem rawRowCheck17252 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form11 = rawRow17252 := by decide +kernel

theorem rowCheck17252 : row17252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17252 := by decide +kernel

theorem rowEval17252 (x : Key → ℝ) : Integer.Sparse.eval row17252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17252, Integer.Sparse.eval_collectBalanced, rawRowCheck17252]

theorem rawRowCheck17253 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form11 = rawRow17253 := by decide +kernel

theorem rowCheck17253 : row17253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17253 := by decide +kernel

theorem rowEval17253 (x : Key → ℝ) : Integer.Sparse.eval row17253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17253, Integer.Sparse.eval_collectBalanced, rawRowCheck17253]

theorem rawRowCheck17254 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form11 = rawRow17254 := by decide +kernel

theorem rowCheck17254 : row17254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17254 := by decide +kernel

theorem rowEval17254 (x : Key → ℝ) : Integer.Sparse.eval row17254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17254, Integer.Sparse.eval_collectBalanced, rawRowCheck17254]

theorem rawRowCheck17255 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form11 = rawRow17255 := by decide +kernel

theorem rowCheck17255 : row17255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17255 := by decide +kernel

theorem rowEval17255 (x : Key → ℝ) : Integer.Sparse.eval row17255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17255, Integer.Sparse.eval_collectBalanced, rawRowCheck17255]

theorem rawRowCheck17256 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form11 = rawRow17256 := by decide +kernel

theorem rowCheck17256 : row17256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17256 := by decide +kernel

theorem rowEval17256 (x : Key → ℝ) : Integer.Sparse.eval row17256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17256, Integer.Sparse.eval_collectBalanced, rawRowCheck17256]

theorem rawRowCheck17257 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form11 = rawRow17257 := by decide +kernel

theorem rowCheck17257 : row17257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17257 := by decide +kernel

theorem rowEval17257 (x : Key → ℝ) : Integer.Sparse.eval row17257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17257, Integer.Sparse.eval_collectBalanced, rawRowCheck17257]

theorem rawRowCheck17258 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form11 = rawRow17258 := by decide +kernel

theorem rowCheck17258 : row17258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17258 := by decide +kernel

theorem rowEval17258 (x : Key → ℝ) : Integer.Sparse.eval row17258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17258, Integer.Sparse.eval_collectBalanced, rawRowCheck17258]

theorem rawRowCheck17259 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form11 = rawRow17259 := by decide +kernel

theorem rowCheck17259 : row17259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17259 := by decide +kernel

theorem rowEval17259 (x : Key → ℝ) : Integer.Sparse.eval row17259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17259, Integer.Sparse.eval_collectBalanced, rawRowCheck17259]

theorem rawRowCheck17260 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form11 = rawRow17260 := by decide +kernel

theorem rowCheck17260 : row17260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17260 := by decide +kernel

theorem rowEval17260 (x : Key → ℝ) : Integer.Sparse.eval row17260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17260, Integer.Sparse.eval_collectBalanced, rawRowCheck17260]

theorem rawRowCheck17261 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form11 = rawRow17261 := by decide +kernel

theorem rowCheck17261 : row17261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17261 := by decide +kernel

theorem rowEval17261 (x : Key → ℝ) : Integer.Sparse.eval row17261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17261, Integer.Sparse.eval_collectBalanced, rawRowCheck17261]

theorem rawRowCheck17262 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form11 = rawRow17262 := by decide +kernel

theorem rowCheck17262 : row17262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17262 := by decide +kernel

theorem rowEval17262 (x : Key → ℝ) : Integer.Sparse.eval row17262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17262, Integer.Sparse.eval_collectBalanced, rawRowCheck17262]

theorem rawRowCheck17263 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form11 = rawRow17263 := by decide +kernel

theorem rowCheck17263 : row17263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17263 := by decide +kernel

theorem rowEval17263 (x : Key → ℝ) : Integer.Sparse.eval row17263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17263, Integer.Sparse.eval_collectBalanced, rawRowCheck17263]

theorem rawRowCheck17264 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form11 = rawRow17264 := by decide +kernel

theorem rowCheck17264 : row17264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17264 := by decide +kernel

theorem rowEval17264 (x : Key → ℝ) : Integer.Sparse.eval row17264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17264, Integer.Sparse.eval_collectBalanced, rawRowCheck17264]

theorem rawRowCheck17265 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form11 = rawRow17265 := by decide +kernel

theorem rowCheck17265 : row17265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17265 := by decide +kernel

theorem rowEval17265 (x : Key → ℝ) : Integer.Sparse.eval row17265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17265, Integer.Sparse.eval_collectBalanced, rawRowCheck17265]

theorem rawRowCheck17266 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form11 = rawRow17266 := by decide +kernel

theorem rowCheck17266 : row17266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17266 := by decide +kernel

theorem rowEval17266 (x : Key → ℝ) : Integer.Sparse.eval row17266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17266, Integer.Sparse.eval_collectBalanced, rawRowCheck17266]

theorem rawRowCheck17267 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form11 = rawRow17267 := by decide +kernel

theorem rowCheck17267 : row17267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17267 := by decide +kernel

theorem rowEval17267 (x : Key → ℝ) : Integer.Sparse.eval row17267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17267, Integer.Sparse.eval_collectBalanced, rawRowCheck17267]

theorem rawRowCheck17268 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form11 = rawRow17268 := by decide +kernel

theorem rowCheck17268 : row17268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17268 := by decide +kernel

theorem rowEval17268 (x : Key → ℝ) : Integer.Sparse.eval row17268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17268, Integer.Sparse.eval_collectBalanced, rawRowCheck17268]

theorem rawRowCheck17269 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form11 = rawRow17269 := by decide +kernel

theorem rowCheck17269 : row17269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17269 := by decide +kernel

theorem rowEval17269 (x : Key → ℝ) : Integer.Sparse.eval row17269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17269, Integer.Sparse.eval_collectBalanced, rawRowCheck17269]

theorem rawRowCheck17270 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form11 = rawRow17270 := by decide +kernel

theorem rowCheck17270 : row17270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17270 := by decide +kernel

theorem rowEval17270 (x : Key → ℝ) : Integer.Sparse.eval row17270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17270, Integer.Sparse.eval_collectBalanced, rawRowCheck17270]

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

theorem rawRowCheck17521 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form11 = rawRow17521 := by decide +kernel

theorem rowCheck17521 : row17521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17521 := by decide +kernel

theorem rowEval17521 (x : Key → ℝ) : Integer.Sparse.eval row17521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17521, Integer.Sparse.eval_collectBalanced, rawRowCheck17521]

theorem rawRowCheck17522 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form11 = rawRow17522 := by decide +kernel

theorem rowCheck17522 : row17522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17522 := by decide +kernel

theorem rowEval17522 (x : Key → ℝ) : Integer.Sparse.eval row17522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17522, Integer.Sparse.eval_collectBalanced, rawRowCheck17522]

theorem rawRowCheck17523 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form11 = rawRow17523 := by decide +kernel

theorem rowCheck17523 : row17523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17523 := by decide +kernel

theorem rowEval17523 (x : Key → ℝ) : Integer.Sparse.eval row17523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17523, Integer.Sparse.eval_collectBalanced, rawRowCheck17523]

theorem rawRowCheck17524 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form11 = rawRow17524 := by decide +kernel

theorem rowCheck17524 : row17524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17524 := by decide +kernel

theorem rowEval17524 (x : Key → ℝ) : Integer.Sparse.eval row17524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17524, Integer.Sparse.eval_collectBalanced, rawRowCheck17524]

theorem rawRowCheck17525 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form11 = rawRow17525 := by decide +kernel

theorem rowCheck17525 : row17525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17525 := by decide +kernel

theorem rowEval17525 (x : Key → ℝ) : Integer.Sparse.eval row17525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17525, Integer.Sparse.eval_collectBalanced, rawRowCheck17525]

theorem rawRowCheck17526 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form11 = rawRow17526 := by decide +kernel

theorem rowCheck17526 : row17526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17526 := by decide +kernel

theorem rowEval17526 (x : Key → ℝ) : Integer.Sparse.eval row17526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17526, Integer.Sparse.eval_collectBalanced, rawRowCheck17526]

theorem rawRowCheck17527 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form11 = rawRow17527 := by decide +kernel

theorem rowCheck17527 : row17527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17527 := by decide +kernel

theorem rowEval17527 (x : Key → ℝ) : Integer.Sparse.eval row17527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17527, Integer.Sparse.eval_collectBalanced, rawRowCheck17527]

theorem rawRowCheck17528 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form11 = rawRow17528 := by decide +kernel

theorem rowCheck17528 : row17528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17528 := by decide +kernel

theorem rowEval17528 (x : Key → ℝ) : Integer.Sparse.eval row17528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17528, Integer.Sparse.eval_collectBalanced, rawRowCheck17528]

theorem rawRowCheck17529 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form11 = rawRow17529 := by decide +kernel

theorem rowCheck17529 : row17529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17529 := by decide +kernel

theorem rowEval17529 (x : Key → ℝ) : Integer.Sparse.eval row17529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17529, Integer.Sparse.eval_collectBalanced, rawRowCheck17529]

theorem rawRowCheck17530 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form11 = rawRow17530 := by decide +kernel

theorem rowCheck17530 : row17530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17530 := by decide +kernel

theorem rowEval17530 (x : Key → ℝ) : Integer.Sparse.eval row17530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17530, Integer.Sparse.eval_collectBalanced, rawRowCheck17530]

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

theorem entryCheck18_11 : entry18_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_11 k)) := by decide +kernel

theorem rowsSound18_11 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval17251 x
  · exact rowEval17252 x
  · exact rowEval17253 x
  · exact rowEval17254 x
  · exact rowEval17255 x
  · exact rowEval17256 x
  · exact rowEval17257 x
  · exact rowEval17258 x
  · exact rowEval17259 x
  · exact rowEval17260 x
  · exact rowEval17261 x
  · exact rowEval17262 x
  · exact rowEval17263 x
  · exact rowEval17264 x
  · exact rowEval17265 x
  · exact rowEval17266 x
  · exact rowEval17267 x
  · exact rowEval17268 x
  · exact rowEval17269 x
  · exact rowEval17270 x

theorem entryEval18_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_11 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck18_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_11]

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

theorem entryCheck19_11 : entry19_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_11 k)) := by decide +kernel

theorem rowsSound19_11 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval17521 x
  · exact rowEval17522 x
  · exact rowEval17523 x
  · exact rowEval17524 x
  · exact rowEval17525 x
  · exact rowEval17526 x
  · exact rowEval17527 x
  · exact rowEval17528 x
  · exact rowEval17529 x
  · exact rowEval17530 x

theorem entryEval19_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_11 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck19_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_11]

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

theorem entryEvalRow11_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 11 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 11).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval11_0 B hB
  · exact entryEval11_1 B hB
  · exact entryEval11_2 B hB
  · exact entryEval11_3 B hB
  · exact entryEval11_4 B hB
  · exact entryEval11_5 B hB
  · exact entryEval11_6_e B hB
  · exact entryEval11_7 B hB
  · exact entryEval11_8 B hB
  · exact entryEval11_9 B hB
  · exact entryEval11_10_e B hB
  · exact entryEval11_11 B hB
  · exact (entryEval12_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e_oai
