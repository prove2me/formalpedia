-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:26:02.541578+00:00
-- url     : https://prove2.me/submissions/cd3ecd08-8987-4a90-90d3-7b73703d49ff

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_21_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11126 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form12 = rawRow11126 := by decide +kernel

theorem rowCheck11126 : row11126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11126 := by decide +kernel

theorem rowEval11126 (x : Key → ℝ) : Integer.Sparse.eval row11126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11126, Integer.Sparse.eval_collectBalanced, rawRowCheck11126]

theorem rawRowCheck11127 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form12 = rawRow11127 := by decide +kernel

theorem rowCheck11127 : row11127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11127 := by decide +kernel

theorem rowEval11127 (x : Key → ℝ) : Integer.Sparse.eval row11127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11127, Integer.Sparse.eval_collectBalanced, rawRowCheck11127]

theorem rawRowCheck11128 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form12 = rawRow11128 := by decide +kernel

theorem rowCheck11128 : row11128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11128 := by decide +kernel

theorem rowEval11128 (x : Key → ℝ) : Integer.Sparse.eval row11128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11128, Integer.Sparse.eval_collectBalanced, rawRowCheck11128]

theorem rawRowCheck11129 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form12 = rawRow11129 := by decide +kernel

theorem rowCheck11129 : row11129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11129 := by decide +kernel

theorem rowEval11129 (x : Key → ℝ) : Integer.Sparse.eval row11129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11129, Integer.Sparse.eval_collectBalanced, rawRowCheck11129]

theorem rawRowCheck11130 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form12 = rawRow11130 := by decide +kernel

theorem rowCheck11130 : row11130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11130 := by decide +kernel

theorem rowEval11130 (x : Key → ℝ) : Integer.Sparse.eval row11130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11130, Integer.Sparse.eval_collectBalanced, rawRowCheck11130]

theorem rawRowCheck11131 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form12 = rawRow11131 := by decide +kernel

theorem rowCheck11131 : row11131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11131 := by decide +kernel

theorem rowEval11131 (x : Key → ℝ) : Integer.Sparse.eval row11131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11131, Integer.Sparse.eval_collectBalanced, rawRowCheck11131]

theorem rawRowCheck11132 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form12 = rawRow11132 := by decide +kernel

theorem rowCheck11132 : row11132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11132 := by decide +kernel

theorem rowEval11132 (x : Key → ℝ) : Integer.Sparse.eval row11132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11132, Integer.Sparse.eval_collectBalanced, rawRowCheck11132]

theorem rawRowCheck11133 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form12 = rawRow11133 := by decide +kernel

theorem rowCheck11133 : row11133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11133 := by decide +kernel

theorem rowEval11133 (x : Key → ℝ) : Integer.Sparse.eval row11133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11133, Integer.Sparse.eval_collectBalanced, rawRowCheck11133]

theorem rawRowCheck11134 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form12 = rawRow11134 := by decide +kernel

theorem rowCheck11134 : row11134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11134 := by decide +kernel

theorem rowEval11134 (x : Key → ℝ) : Integer.Sparse.eval row11134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11134, Integer.Sparse.eval_collectBalanced, rawRowCheck11134]

theorem rawRowCheck11135 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form12 = rawRow11135 := by decide +kernel

theorem rowCheck11135 : row11135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11135 := by decide +kernel

theorem rowEval11135 (x : Key → ℝ) : Integer.Sparse.eval row11135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11135, Integer.Sparse.eval_collectBalanced, rawRowCheck11135]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11136 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form12 = rawRow11136 := by decide +kernel

theorem rowCheck11136 : row11136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11136 := by decide +kernel

theorem rowEval11136 (x : Key → ℝ) : Integer.Sparse.eval row11136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11136, Integer.Sparse.eval_collectBalanced, rawRowCheck11136]

theorem rawRowCheck11137 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form12 = rawRow11137 := by decide +kernel

theorem rowCheck11137 : row11137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11137 := by decide +kernel

theorem rowEval11137 (x : Key → ℝ) : Integer.Sparse.eval row11137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11137, Integer.Sparse.eval_collectBalanced, rawRowCheck11137]

theorem rawRowCheck11138 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form12 = rawRow11138 := by decide +kernel

theorem rowCheck11138 : row11138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11138 := by decide +kernel

theorem rowEval11138 (x : Key → ℝ) : Integer.Sparse.eval row11138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11138, Integer.Sparse.eval_collectBalanced, rawRowCheck11138]

theorem rawRowCheck11139 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form12 = rawRow11139 := by decide +kernel

theorem rowCheck11139 : row11139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11139 := by decide +kernel

theorem rowEval11139 (x : Key → ℝ) : Integer.Sparse.eval row11139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11139, Integer.Sparse.eval_collectBalanced, rawRowCheck11139]

theorem rawRowCheck11140 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form12 = rawRow11140 := by decide +kernel

theorem rowCheck11140 : row11140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11140 := by decide +kernel

theorem rowEval11140 (x : Key → ℝ) : Integer.Sparse.eval row11140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11140, Integer.Sparse.eval_collectBalanced, rawRowCheck11140]

theorem rawRowCheck11141 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form12 = rawRow11141 := by decide +kernel

theorem rowCheck11141 : row11141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11141 := by decide +kernel

theorem rowEval11141 (x : Key → ℝ) : Integer.Sparse.eval row11141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11141, Integer.Sparse.eval_collectBalanced, rawRowCheck11141]

theorem rawRowCheck11142 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form12 = rawRow11142 := by decide +kernel

theorem rowCheck11142 : row11142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11142 := by decide +kernel

theorem rowEval11142 (x : Key → ℝ) : Integer.Sparse.eval row11142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11142, Integer.Sparse.eval_collectBalanced, rawRowCheck11142]

theorem rawRowCheck11143 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form12 = rawRow11143 := by decide +kernel

theorem rowCheck11143 : row11143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11143 := by decide +kernel

theorem rowEval11143 (x : Key → ℝ) : Integer.Sparse.eval row11143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11143, Integer.Sparse.eval_collectBalanced, rawRowCheck11143]

theorem rawRowCheck11144 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form12 = rawRow11144 := by decide +kernel

theorem rowCheck11144 : row11144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11144 := by decide +kernel

theorem rowEval11144 (x : Key → ℝ) : Integer.Sparse.eval row11144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11144, Integer.Sparse.eval_collectBalanced, rawRowCheck11144]

theorem rawRowCheck11145 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form12 = rawRow11145 := by decide +kernel

theorem rowCheck11145 : row11145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11145 := by decide +kernel

theorem rowEval11145 (x : Key → ℝ) : Integer.Sparse.eval row11145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11145, Integer.Sparse.eval_collectBalanced, rawRowCheck11145]

theorem rawRowCheck11146 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form12 = rawRow11146 := by decide +kernel

theorem rowCheck11146 : row11146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11146 := by decide +kernel

theorem rowEval11146 (x : Key → ℝ) : Integer.Sparse.eval row11146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11146, Integer.Sparse.eval_collectBalanced, rawRowCheck11146]

theorem rawRowCheck11147 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form12 = rawRow11147 := by decide +kernel

theorem rowCheck11147 : row11147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11147 := by decide +kernel

theorem rowEval11147 (x : Key → ℝ) : Integer.Sparse.eval row11147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11147, Integer.Sparse.eval_collectBalanced, rawRowCheck11147]

theorem rawRowCheck11148 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form12 = rawRow11148 := by decide +kernel

theorem rowCheck11148 : row11148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11148 := by decide +kernel

theorem rowEval11148 (x : Key → ℝ) : Integer.Sparse.eval row11148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11148, Integer.Sparse.eval_collectBalanced, rawRowCheck11148]

theorem rawRowCheck11149 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form12 = rawRow11149 := by decide +kernel

theorem rowCheck11149 : row11149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11149 := by decide +kernel

theorem rowEval11149 (x : Key → ℝ) : Integer.Sparse.eval row11149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11149, Integer.Sparse.eval_collectBalanced, rawRowCheck11149]

theorem rawRowCheck11150 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form12 = rawRow11150 := by decide +kernel

theorem rowCheck11150 : row11150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11150 := by decide +kernel

theorem rowEval11150 (x : Key → ℝ) : Integer.Sparse.eval row11150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11150, Integer.Sparse.eval_collectBalanced, rawRowCheck11150]

theorem rawRowCheck11151 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form12 = rawRow11151 := by decide +kernel

theorem rowCheck11151 : row11151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11151 := by decide +kernel

theorem rowEval11151 (x : Key → ℝ) : Integer.Sparse.eval row11151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11151, Integer.Sparse.eval_collectBalanced, rawRowCheck11151]

theorem rawRowCheck11152 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form12 = rawRow11152 := by decide +kernel

theorem rowCheck11152 : row11152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11152 := by decide +kernel

theorem rowEval11152 (x : Key → ℝ) : Integer.Sparse.eval row11152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11152, Integer.Sparse.eval_collectBalanced, rawRowCheck11152]

theorem rawRowCheck11153 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form12 = rawRow11153 := by decide +kernel

theorem rowCheck11153 : row11153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11153 := by decide +kernel

theorem rowEval11153 (x : Key → ℝ) : Integer.Sparse.eval row11153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11153, Integer.Sparse.eval_collectBalanced, rawRowCheck11153]

theorem rawRowCheck11154 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form12 = rawRow11154 := by decide +kernel

theorem rowCheck11154 : row11154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11154 := by decide +kernel

theorem rowEval11154 (x : Key → ℝ) : Integer.Sparse.eval row11154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11154, Integer.Sparse.eval_collectBalanced, rawRowCheck11154]

theorem rawRowCheck11155 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form12 = rawRow11155 := by decide +kernel

theorem rowCheck11155 : row11155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11155 := by decide +kernel

theorem rowEval11155 (x : Key → ℝ) : Integer.Sparse.eval row11155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11155, Integer.Sparse.eval_collectBalanced, rawRowCheck11155]

theorem rawRowCheck11156 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form12 = rawRow11156 := by decide +kernel

theorem rowCheck11156 : row11156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11156 := by decide +kernel

theorem rowEval11156 (x : Key → ℝ) : Integer.Sparse.eval row11156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11156, Integer.Sparse.eval_collectBalanced, rawRowCheck11156]

theorem rawRowCheck11157 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form12 = rawRow11157 := by decide +kernel

theorem rowCheck11157 : row11157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11157 := by decide +kernel

theorem rowEval11157 (x : Key → ℝ) : Integer.Sparse.eval row11157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11157, Integer.Sparse.eval_collectBalanced, rawRowCheck11157]

theorem rawRowCheck11158 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form12 = rawRow11158 := by decide +kernel

theorem rowCheck11158 : row11158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11158 := by decide +kernel

theorem rowEval11158 (x : Key → ℝ) : Integer.Sparse.eval row11158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11158, Integer.Sparse.eval_collectBalanced, rawRowCheck11158]

theorem rawRowCheck11159 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form12 = rawRow11159 := by decide +kernel

theorem rowCheck11159 : row11159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11159 := by decide +kernel

theorem rowEval11159 (x : Key → ℝ) : Integer.Sparse.eval row11159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11159, Integer.Sparse.eval_collectBalanced, rawRowCheck11159]

theorem rawRowCheck11160 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form12 = rawRow11160 := by decide +kernel

theorem rowCheck11160 : row11160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11160 := by decide +kernel

theorem rowEval11160 (x : Key → ℝ) : Integer.Sparse.eval row11160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11160, Integer.Sparse.eval_collectBalanced, rawRowCheck11160]

theorem rawRowCheck11161 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form12 = rawRow11161 := by decide +kernel

theorem rowCheck11161 : row11161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11161 := by decide +kernel

theorem rowEval11161 (x : Key → ℝ) : Integer.Sparse.eval row11161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11161, Integer.Sparse.eval_collectBalanced, rawRowCheck11161]

theorem rawRowCheck11198 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form14 = rawRow11198 := by decide +kernel

theorem rowCheck11198 : row11198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11198 := by decide +kernel

theorem rowEval11198 (x : Key → ℝ) : Integer.Sparse.eval row11198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11198, Integer.Sparse.eval_collectBalanced, rawRowCheck11198]

theorem rawRowCheck11199 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form14 = rawRow11199 := by decide +kernel

theorem rowCheck11199 : row11199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11199 := by decide +kernel

theorem rowEval11199 (x : Key → ℝ) : Integer.Sparse.eval row11199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11199, Integer.Sparse.eval_collectBalanced, rawRowCheck11199]

theorem rawRowCheck11200 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form14 = rawRow11200 := by decide +kernel

theorem rowCheck11200 : row11200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11200 := by decide +kernel

theorem rowEval11200 (x : Key → ℝ) : Integer.Sparse.eval row11200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11200, Integer.Sparse.eval_collectBalanced, rawRowCheck11200]

theorem rawRowCheck11201 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form14 = rawRow11201 := by decide +kernel

theorem rowCheck11201 : row11201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11201 := by decide +kernel

theorem rowEval11201 (x : Key → ℝ) : Integer.Sparse.eval row11201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11201, Integer.Sparse.eval_collectBalanced, rawRowCheck11201]

theorem rawRowCheck11202 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form14 = rawRow11202 := by decide +kernel

theorem rowCheck11202 : row11202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11202 := by decide +kernel

theorem rowEval11202 (x : Key → ℝ) : Integer.Sparse.eval row11202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11202, Integer.Sparse.eval_collectBalanced, rawRowCheck11202]

theorem rawRowCheck11203 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form14 = rawRow11203 := by decide +kernel

theorem rowCheck11203 : row11203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11203 := by decide +kernel

theorem rowEval11203 (x : Key → ℝ) : Integer.Sparse.eval row11203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11203, Integer.Sparse.eval_collectBalanced, rawRowCheck11203]

theorem rawRowCheck11204 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow11204 := by decide +kernel

theorem rowCheck11204 : row11204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11204 := by decide +kernel

theorem rowEval11204 (x : Key → ℝ) : Integer.Sparse.eval row11204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11204, Integer.Sparse.eval_collectBalanced, rawRowCheck11204]

theorem rawRowCheck11205 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow11205 := by decide +kernel

theorem rowCheck11205 : row11205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11205 := by decide +kernel

theorem rowEval11205 (x : Key → ℝ) : Integer.Sparse.eval row11205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11205, Integer.Sparse.eval_collectBalanced, rawRowCheck11205]

theorem rawRowCheck11206 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow11206 := by decide +kernel

theorem rowCheck11206 : row11206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11206 := by decide +kernel

theorem rowEval11206 (x : Key → ℝ) : Integer.Sparse.eval row11206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11206, Integer.Sparse.eval_collectBalanced, rawRowCheck11206]

theorem rawRowCheck11207 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow11207 := by decide +kernel

theorem rowCheck11207 : row11207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11207 := by decide +kernel

theorem rowEval11207 (x : Key → ℝ) : Integer.Sparse.eval row11207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11207, Integer.Sparse.eval_collectBalanced, rawRowCheck11207]

theorem rawRowCheck11208 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow11208 := by decide +kernel

theorem rowCheck11208 : row11208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11208 := by decide +kernel

theorem rowEval11208 (x : Key → ℝ) : Integer.Sparse.eval row11208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11208, Integer.Sparse.eval_collectBalanced, rawRowCheck11208]

theorem rawRowCheck11209 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow11209 := by decide +kernel

theorem rowCheck11209 : row11209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11209 := by decide +kernel

theorem rowEval11209 (x : Key → ℝ) : Integer.Sparse.eval row11209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11209, Integer.Sparse.eval_collectBalanced, rawRowCheck11209]

theorem rawRowCheck11210 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form14 = rawRow11210 := by decide +kernel

theorem rowCheck11210 : row11210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11210 := by decide +kernel

theorem rowEval11210 (x : Key → ℝ) : Integer.Sparse.eval row11210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11210, Integer.Sparse.eval_collectBalanced, rawRowCheck11210]

theorem rawRowCheck11211 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form14 = rawRow11211 := by decide +kernel

theorem rowCheck11211 : row11211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11211 := by decide +kernel

theorem rowEval11211 (x : Key → ℝ) : Integer.Sparse.eval row11211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11211, Integer.Sparse.eval_collectBalanced, rawRowCheck11211]

theorem rawRowCheck11212 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form14 = rawRow11212 := by decide +kernel

theorem rowCheck11212 : row11212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11212 := by decide +kernel

theorem rowEval11212 (x : Key → ℝ) : Integer.Sparse.eval row11212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11212, Integer.Sparse.eval_collectBalanced, rawRowCheck11212]

theorem rawRowCheck11213 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form14 = rawRow11213 := by decide +kernel

theorem rowCheck11213 : row11213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11213 := by decide +kernel

theorem rowEval11213 (x : Key → ℝ) : Integer.Sparse.eval row11213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11213, Integer.Sparse.eval_collectBalanced, rawRowCheck11213]

theorem rawRowCheck11214 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form14 = rawRow11214 := by decide +kernel

theorem rowCheck11214 : row11214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11214 := by decide +kernel

theorem rowEval11214 (x : Key → ℝ) : Integer.Sparse.eval row11214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11214, Integer.Sparse.eval_collectBalanced, rawRowCheck11214]

theorem rawRowCheck11215 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form14 = rawRow11215 := by decide +kernel

theorem rowCheck11215 : row11215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11215 := by decide +kernel

theorem rowEval11215 (x : Key → ℝ) : Integer.Sparse.eval row11215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11215, Integer.Sparse.eval_collectBalanced, rawRowCheck11215]

theorem rawRowCheck11216 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form14 = rawRow11216 := by decide +kernel

theorem rowCheck11216 : row11216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11216 := by decide +kernel

theorem rowEval11216 (x : Key → ℝ) : Integer.Sparse.eval row11216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11216, Integer.Sparse.eval_collectBalanced, rawRowCheck11216]

theorem rawRowCheck11217 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form14 = rawRow11217 := by decide +kernel

theorem rowCheck11217 : row11217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11217 := by decide +kernel

theorem rowEval11217 (x : Key → ℝ) : Integer.Sparse.eval row11217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11217, Integer.Sparse.eval_collectBalanced, rawRowCheck11217]

theorem rawRowCheck11218 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form14 = rawRow11218 := by decide +kernel

theorem rowCheck11218 : row11218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11218 := by decide +kernel

theorem rowEval11218 (x : Key → ℝ) : Integer.Sparse.eval row11218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11218, Integer.Sparse.eval_collectBalanced, rawRowCheck11218]

theorem rawRowCheck11219 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form14 = rawRow11219 := by decide +kernel

theorem rowCheck11219 : row11219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11219 := by decide +kernel

theorem rowEval11219 (x : Key → ℝ) : Integer.Sparse.eval row11219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11219, Integer.Sparse.eval_collectBalanced, rawRowCheck11219]

theorem rawRowCheck11220 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form14 = rawRow11220 := by decide +kernel

theorem rowCheck11220 : row11220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11220 := by decide +kernel

theorem rowEval11220 (x : Key → ℝ) : Integer.Sparse.eval row11220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11220, Integer.Sparse.eval_collectBalanced, rawRowCheck11220]

theorem rawRowCheck11221 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form14 = rawRow11221 := by decide +kernel

theorem rowCheck11221 : row11221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11221 := by decide +kernel

theorem rowEval11221 (x : Key → ℝ) : Integer.Sparse.eval row11221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11221, Integer.Sparse.eval_collectBalanced, rawRowCheck11221]

theorem rawRowCheck11222 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form14 = rawRow11222 := by decide +kernel

theorem rowCheck11222 : row11222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11222 := by decide +kernel

theorem rowEval11222 (x : Key → ℝ) : Integer.Sparse.eval row11222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11222, Integer.Sparse.eval_collectBalanced, rawRowCheck11222]

theorem rawRowCheck11223 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form14 = rawRow11223 := by decide +kernel

theorem rowCheck11223 : row11223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11223 := by decide +kernel

theorem rowEval11223 (x : Key → ℝ) : Integer.Sparse.eval row11223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11223, Integer.Sparse.eval_collectBalanced, rawRowCheck11223]

theorem rawRowCheck11224 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form14 = rawRow11224 := by decide +kernel

theorem rowCheck11224 : row11224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11224 := by decide +kernel

theorem rowEval11224 (x : Key → ℝ) : Integer.Sparse.eval row11224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11224, Integer.Sparse.eval_collectBalanced, rawRowCheck11224]

theorem rawRowCheck11225 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow11225 := by decide +kernel

theorem rowCheck11225 : row11225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11225 := by decide +kernel

theorem rowEval11225 (x : Key → ℝ) : Integer.Sparse.eval row11225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11225, Integer.Sparse.eval_collectBalanced, rawRowCheck11225]

theorem rawRowCheck11226 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow11226 := by decide +kernel

theorem rowCheck11226 : row11226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11226 := by decide +kernel

theorem rowEval11226 (x : Key → ℝ) : Integer.Sparse.eval row11226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11226, Integer.Sparse.eval_collectBalanced, rawRowCheck11226]

theorem rawRowCheck11227 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow11227 := by decide +kernel

theorem rowCheck11227 : row11227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11227 := by decide +kernel

theorem rowEval11227 (x : Key → ℝ) : Integer.Sparse.eval row11227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11227, Integer.Sparse.eval_collectBalanced, rawRowCheck11227]

theorem rawRowCheck11228 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form14 = rawRow11228 := by decide +kernel

theorem rowCheck11228 : row11228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11228 := by decide +kernel

theorem rowEval11228 (x : Key → ℝ) : Integer.Sparse.eval row11228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11228, Integer.Sparse.eval_collectBalanced, rawRowCheck11228]

theorem rawRowCheck11229 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form14 = rawRow11229 := by decide +kernel

theorem rowCheck11229 : row11229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11229 := by decide +kernel

theorem rowEval11229 (x : Key → ℝ) : Integer.Sparse.eval row11229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11229, Integer.Sparse.eval_collectBalanced, rawRowCheck11229]

theorem rawRowCheck11230 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form14 = rawRow11230 := by decide +kernel

theorem rowCheck11230 : row11230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11230 := by decide +kernel

theorem rowEval11230 (x : Key → ℝ) : Integer.Sparse.eval row11230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11230, Integer.Sparse.eval_collectBalanced, rawRowCheck11230]

theorem rawRowCheck11231 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form14 = rawRow11231 := by decide +kernel

theorem rowCheck11231 : row11231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11231 := by decide +kernel

theorem rowEval11231 (x : Key → ℝ) : Integer.Sparse.eval row11231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11231, Integer.Sparse.eval_collectBalanced, rawRowCheck11231]

theorem rawRowCheck11232 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form14 = rawRow11232 := by decide +kernel

theorem rowCheck11232 : row11232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11232 := by decide +kernel

theorem rowEval11232 (x : Key → ℝ) : Integer.Sparse.eval row11232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11232, Integer.Sparse.eval_collectBalanced, rawRowCheck11232]

theorem rawRowCheck11233 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form14 = rawRow11233 := by decide +kernel

theorem rowCheck11233 : row11233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11233 := by decide +kernel

theorem rowEval11233 (x : Key → ℝ) : Integer.Sparse.eval row11233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11233, Integer.Sparse.eval_collectBalanced, rawRowCheck11233]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11270 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form16 = rawRow11270 := by decide +kernel

theorem rowCheck11270 : row11270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11270 := by decide +kernel

theorem rowEval11270 (x : Key → ℝ) : Integer.Sparse.eval row11270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11270, Integer.Sparse.eval_collectBalanced, rawRowCheck11270]

theorem rawRowCheck11271 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form16 = rawRow11271 := by decide +kernel

theorem rowCheck11271 : row11271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11271 := by decide +kernel

theorem rowEval11271 (x : Key → ℝ) : Integer.Sparse.eval row11271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11271, Integer.Sparse.eval_collectBalanced, rawRowCheck11271]

theorem rawRowCheck11272 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form16 = rawRow11272 := by decide +kernel

theorem rowCheck11272 : row11272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11272 := by decide +kernel

theorem rowEval11272 (x : Key → ℝ) : Integer.Sparse.eval row11272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11272, Integer.Sparse.eval_collectBalanced, rawRowCheck11272]

theorem rawRowCheck11273 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form16 = rawRow11273 := by decide +kernel

theorem rowCheck11273 : row11273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11273 := by decide +kernel

theorem rowEval11273 (x : Key → ℝ) : Integer.Sparse.eval row11273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11273, Integer.Sparse.eval_collectBalanced, rawRowCheck11273]

theorem rawRowCheck11274 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form16 = rawRow11274 := by decide +kernel

theorem rowCheck11274 : row11274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11274 := by decide +kernel

theorem rowEval11274 (x : Key → ℝ) : Integer.Sparse.eval row11274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11274, Integer.Sparse.eval_collectBalanced, rawRowCheck11274]

theorem rawRowCheck11275 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form16 = rawRow11275 := by decide +kernel

theorem rowCheck11275 : row11275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11275 := by decide +kernel

theorem rowEval11275 (x : Key → ℝ) : Integer.Sparse.eval row11275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11275, Integer.Sparse.eval_collectBalanced, rawRowCheck11275]

theorem rawRowCheck11276 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form16 = rawRow11276 := by decide +kernel

theorem rowCheck11276 : row11276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11276 := by decide +kernel

theorem rowEval11276 (x : Key → ℝ) : Integer.Sparse.eval row11276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11276, Integer.Sparse.eval_collectBalanced, rawRowCheck11276]

theorem rawRowCheck11277 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form16 = rawRow11277 := by decide +kernel

theorem rowCheck11277 : row11277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11277 := by decide +kernel

theorem rowEval11277 (x : Key → ℝ) : Integer.Sparse.eval row11277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11277, Integer.Sparse.eval_collectBalanced, rawRowCheck11277]

theorem rawRowCheck11278 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form16 = rawRow11278 := by decide +kernel

theorem rowCheck11278 : row11278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11278 := by decide +kernel

theorem rowEval11278 (x : Key → ℝ) : Integer.Sparse.eval row11278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11278, Integer.Sparse.eval_collectBalanced, rawRowCheck11278]

theorem rawRowCheck11279 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form16 = rawRow11279 := by decide +kernel

theorem rowCheck11279 : row11279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11279 := by decide +kernel

theorem rowEval11279 (x : Key → ℝ) : Integer.Sparse.eval row11279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11279, Integer.Sparse.eval_collectBalanced, rawRowCheck11279]

theorem rawRowCheck11280 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form16 = rawRow11280 := by decide +kernel

theorem rowCheck11280 : row11280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11280 := by decide +kernel

theorem rowEval11280 (x : Key → ℝ) : Integer.Sparse.eval row11280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11280, Integer.Sparse.eval_collectBalanced, rawRowCheck11280]

theorem rawRowCheck11281 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form16 = rawRow11281 := by decide +kernel

theorem rowCheck11281 : row11281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11281 := by decide +kernel

theorem rowEval11281 (x : Key → ℝ) : Integer.Sparse.eval row11281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11281, Integer.Sparse.eval_collectBalanced, rawRowCheck11281]

theorem rawRowCheck11282 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form16 = rawRow11282 := by decide +kernel

theorem rowCheck11282 : row11282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11282 := by decide +kernel

theorem rowEval11282 (x : Key → ℝ) : Integer.Sparse.eval row11282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11282, Integer.Sparse.eval_collectBalanced, rawRowCheck11282]

theorem rawRowCheck11283 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form16 = rawRow11283 := by decide +kernel

theorem rowCheck11283 : row11283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11283 := by decide +kernel

theorem rowEval11283 (x : Key → ℝ) : Integer.Sparse.eval row11283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11283, Integer.Sparse.eval_collectBalanced, rawRowCheck11283]

theorem rawRowCheck11284 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form16 = rawRow11284 := by decide +kernel

theorem rowCheck11284 : row11284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11284 := by decide +kernel

theorem rowEval11284 (x : Key → ℝ) : Integer.Sparse.eval row11284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11284, Integer.Sparse.eval_collectBalanced, rawRowCheck11284]

theorem rawRowCheck11285 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form16 = rawRow11285 := by decide +kernel

theorem rowCheck11285 : row11285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11285 := by decide +kernel

theorem rowEval11285 (x : Key → ℝ) : Integer.Sparse.eval row11285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11285, Integer.Sparse.eval_collectBalanced, rawRowCheck11285]

theorem rawRowCheck11286 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form16 = rawRow11286 := by decide +kernel

theorem rowCheck11286 : row11286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11286 := by decide +kernel

theorem rowEval11286 (x : Key → ℝ) : Integer.Sparse.eval row11286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11286, Integer.Sparse.eval_collectBalanced, rawRowCheck11286]

theorem rawRowCheck11287 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form16 = rawRow11287 := by decide +kernel

theorem rowCheck11287 : row11287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11287 := by decide +kernel

theorem rowEval11287 (x : Key → ℝ) : Integer.Sparse.eval row11287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11287, Integer.Sparse.eval_collectBalanced, rawRowCheck11287]

theorem rawRowCheck11288 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form16 = rawRow11288 := by decide +kernel

theorem rowCheck11288 : row11288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11288 := by decide +kernel

theorem rowEval11288 (x : Key → ℝ) : Integer.Sparse.eval row11288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11288, Integer.Sparse.eval_collectBalanced, rawRowCheck11288]

theorem rawRowCheck11289 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form16 = rawRow11289 := by decide +kernel

theorem rowCheck11289 : row11289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11289 := by decide +kernel

theorem rowEval11289 (x : Key → ℝ) : Integer.Sparse.eval row11289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11289, Integer.Sparse.eval_collectBalanced, rawRowCheck11289]

theorem rawRowCheck11290 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form16 = rawRow11290 := by decide +kernel

theorem rowCheck11290 : row11290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11290 := by decide +kernel

theorem rowEval11290 (x : Key → ℝ) : Integer.Sparse.eval row11290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11290, Integer.Sparse.eval_collectBalanced, rawRowCheck11290]

theorem rawRowCheck11291 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form16 = rawRow11291 := by decide +kernel

theorem rowCheck11291 : row11291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11291 := by decide +kernel

theorem rowEval11291 (x : Key → ℝ) : Integer.Sparse.eval row11291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11291, Integer.Sparse.eval_collectBalanced, rawRowCheck11291]

theorem rawRowCheck11292 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form16 = rawRow11292 := by decide +kernel

theorem rowCheck11292 : row11292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11292 := by decide +kernel

theorem rowEval11292 (x : Key → ℝ) : Integer.Sparse.eval row11292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11292, Integer.Sparse.eval_collectBalanced, rawRowCheck11292]

theorem rawRowCheck11293 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form16 = rawRow11293 := by decide +kernel

theorem rowCheck11293 : row11293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11293 := by decide +kernel

theorem rowEval11293 (x : Key → ℝ) : Integer.Sparse.eval row11293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11293, Integer.Sparse.eval_collectBalanced, rawRowCheck11293]

theorem rawRowCheck11294 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form16 = rawRow11294 := by decide +kernel

theorem rowCheck11294 : row11294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11294 := by decide +kernel

theorem rowEval11294 (x : Key → ℝ) : Integer.Sparse.eval row11294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11294, Integer.Sparse.eval_collectBalanced, rawRowCheck11294]

theorem rawRowCheck11295 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form16 = rawRow11295 := by decide +kernel

theorem rowCheck11295 : row11295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11295 := by decide +kernel

theorem rowEval11295 (x : Key → ℝ) : Integer.Sparse.eval row11295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11295, Integer.Sparse.eval_collectBalanced, rawRowCheck11295]

theorem rawRowCheck11296 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form16 = rawRow11296 := by decide +kernel

theorem rowCheck11296 : row11296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11296 := by decide +kernel

theorem rowEval11296 (x : Key → ℝ) : Integer.Sparse.eval row11296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11296, Integer.Sparse.eval_collectBalanced, rawRowCheck11296]

theorem rawRowCheck11297 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow11297 := by decide +kernel

theorem rowCheck11297 : row11297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11297 := by decide +kernel

theorem rowEval11297 (x : Key → ℝ) : Integer.Sparse.eval row11297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11297, Integer.Sparse.eval_collectBalanced, rawRowCheck11297]

theorem rawRowCheck11298 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow11298 := by decide +kernel

theorem rowCheck11298 : row11298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11298 := by decide +kernel

theorem rowEval11298 (x : Key → ℝ) : Integer.Sparse.eval row11298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11298, Integer.Sparse.eval_collectBalanced, rawRowCheck11298]

theorem rawRowCheck11299 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow11299 := by decide +kernel

theorem rowCheck11299 : row11299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11299 := by decide +kernel

theorem rowEval11299 (x : Key → ℝ) : Integer.Sparse.eval row11299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11299, Integer.Sparse.eval_collectBalanced, rawRowCheck11299]

theorem rawRowCheck11300 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form16 = rawRow11300 := by decide +kernel

theorem rowCheck11300 : row11300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11300 := by decide +kernel

theorem rowEval11300 (x : Key → ℝ) : Integer.Sparse.eval row11300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11300, Integer.Sparse.eval_collectBalanced, rawRowCheck11300]

theorem rawRowCheck11301 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form16 = rawRow11301 := by decide +kernel

theorem rowCheck11301 : row11301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11301 := by decide +kernel

theorem rowEval11301 (x : Key → ℝ) : Integer.Sparse.eval row11301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11301, Integer.Sparse.eval_collectBalanced, rawRowCheck11301]

theorem rawRowCheck11302 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form16 = rawRow11302 := by decide +kernel

theorem rowCheck11302 : row11302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11302 := by decide +kernel

theorem rowEval11302 (x : Key → ℝ) : Integer.Sparse.eval row11302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11302, Integer.Sparse.eval_collectBalanced, rawRowCheck11302]

theorem rawRowCheck11303 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form16 = rawRow11303 := by decide +kernel

theorem rowCheck11303 : row11303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11303 := by decide +kernel

theorem rowEval11303 (x : Key → ℝ) : Integer.Sparse.eval row11303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11303, Integer.Sparse.eval_collectBalanced, rawRowCheck11303]

theorem rawRowCheck11304 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form16 = rawRow11304 := by decide +kernel

theorem rowCheck11304 : row11304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11304 := by decide +kernel

theorem rowEval11304 (x : Key → ℝ) : Integer.Sparse.eval row11304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11304, Integer.Sparse.eval_collectBalanced, rawRowCheck11304]

theorem rawRowCheck11305 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form16 = rawRow11305 := by decide +kernel

theorem rowCheck11305 : row11305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11305 := by decide +kernel

theorem rowEval11305 (x : Key → ℝ) : Integer.Sparse.eval row11305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11305, Integer.Sparse.eval_collectBalanced, rawRowCheck11305]

theorem rawRowCheck11378 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form19 = rawRow11378 := by decide +kernel

theorem rowCheck11378 : row11378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11378 := by decide +kernel

theorem rowEval11378 (x : Key → ℝ) : Integer.Sparse.eval row11378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11378, Integer.Sparse.eval_collectBalanced, rawRowCheck11378]

theorem rawRowCheck11379 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form19 = rawRow11379 := by decide +kernel

theorem rowCheck11379 : row11379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11379 := by decide +kernel

theorem rowEval11379 (x : Key → ℝ) : Integer.Sparse.eval row11379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11379, Integer.Sparse.eval_collectBalanced, rawRowCheck11379]

theorem rawRowCheck11380 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form19 = rawRow11380 := by decide +kernel

theorem rowCheck11380 : row11380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11380 := by decide +kernel

theorem rowEval11380 (x : Key → ℝ) : Integer.Sparse.eval row11380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11380, Integer.Sparse.eval_collectBalanced, rawRowCheck11380]

theorem rawRowCheck11381 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form19 = rawRow11381 := by decide +kernel

theorem rowCheck11381 : row11381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11381 := by decide +kernel

theorem rowEval11381 (x : Key → ℝ) : Integer.Sparse.eval row11381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11381, Integer.Sparse.eval_collectBalanced, rawRowCheck11381]

theorem rawRowCheck11382 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form19 = rawRow11382 := by decide +kernel

theorem rowCheck11382 : row11382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11382 := by decide +kernel

theorem rowEval11382 (x : Key → ℝ) : Integer.Sparse.eval row11382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11382, Integer.Sparse.eval_collectBalanced, rawRowCheck11382]

theorem rawRowCheck11383 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form19 = rawRow11383 := by decide +kernel

theorem rowCheck11383 : row11383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11383 := by decide +kernel

theorem rowEval11383 (x : Key → ℝ) : Integer.Sparse.eval row11383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11383, Integer.Sparse.eval_collectBalanced, rawRowCheck11383]

theorem rawRowCheck11384 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form19 = rawRow11384 := by decide +kernel

theorem rowCheck11384 : row11384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11384 := by decide +kernel

theorem rowEval11384 (x : Key → ℝ) : Integer.Sparse.eval row11384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11384, Integer.Sparse.eval_collectBalanced, rawRowCheck11384]

theorem rawRowCheck11385 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form19 = rawRow11385 := by decide +kernel

theorem rowCheck11385 : row11385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11385 := by decide +kernel

theorem rowEval11385 (x : Key → ℝ) : Integer.Sparse.eval row11385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11385, Integer.Sparse.eval_collectBalanced, rawRowCheck11385]

theorem rawRowCheck11386 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form19 = rawRow11386 := by decide +kernel

theorem rowCheck11386 : row11386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11386 := by decide +kernel

theorem rowEval11386 (x : Key → ℝ) : Integer.Sparse.eval row11386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11386, Integer.Sparse.eval_collectBalanced, rawRowCheck11386]

theorem rawRowCheck11387 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form19 = rawRow11387 := by decide +kernel

theorem rowCheck11387 : row11387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11387 := by decide +kernel

theorem rowEval11387 (x : Key → ℝ) : Integer.Sparse.eval row11387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11387, Integer.Sparse.eval_collectBalanced, rawRowCheck11387]

theorem rawRowCheck11388 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form19 = rawRow11388 := by decide +kernel

theorem rowCheck11388 : row11388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11388 := by decide +kernel

theorem rowEval11388 (x : Key → ℝ) : Integer.Sparse.eval row11388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11388, Integer.Sparse.eval_collectBalanced, rawRowCheck11388]

theorem rawRowCheck11389 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form19 = rawRow11389 := by decide +kernel

theorem rowCheck11389 : row11389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11389 := by decide +kernel

theorem rowEval11389 (x : Key → ℝ) : Integer.Sparse.eval row11389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11389, Integer.Sparse.eval_collectBalanced, rawRowCheck11389]

theorem rawRowCheck11390 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form19 = rawRow11390 := by decide +kernel

theorem rowCheck11390 : row11390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11390 := by decide +kernel

theorem rowEval11390 (x : Key → ℝ) : Integer.Sparse.eval row11390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11390, Integer.Sparse.eval_collectBalanced, rawRowCheck11390]

theorem rawRowCheck11391 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form19 = rawRow11391 := by decide +kernel

theorem rowCheck11391 : row11391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11391 := by decide +kernel

theorem rowEval11391 (x : Key → ℝ) : Integer.Sparse.eval row11391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11391, Integer.Sparse.eval_collectBalanced, rawRowCheck11391]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11392 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form19 = rawRow11392 := by decide +kernel

theorem rowCheck11392 : row11392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11392 := by decide +kernel

theorem rowEval11392 (x : Key → ℝ) : Integer.Sparse.eval row11392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11392, Integer.Sparse.eval_collectBalanced, rawRowCheck11392]

theorem rawRowCheck11393 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form19 = rawRow11393 := by decide +kernel

theorem rowCheck11393 : row11393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11393 := by decide +kernel

theorem rowEval11393 (x : Key → ℝ) : Integer.Sparse.eval row11393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11393, Integer.Sparse.eval_collectBalanced, rawRowCheck11393]

theorem rawRowCheck11394 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form19 = rawRow11394 := by decide +kernel

theorem rowCheck11394 : row11394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11394 := by decide +kernel

theorem rowEval11394 (x : Key → ℝ) : Integer.Sparse.eval row11394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11394, Integer.Sparse.eval_collectBalanced, rawRowCheck11394]

theorem rawRowCheck11395 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form19 = rawRow11395 := by decide +kernel

theorem rowCheck11395 : row11395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11395 := by decide +kernel

theorem rowEval11395 (x : Key → ℝ) : Integer.Sparse.eval row11395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11395, Integer.Sparse.eval_collectBalanced, rawRowCheck11395]

theorem rawRowCheck11396 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form19 = rawRow11396 := by decide +kernel

theorem rowCheck11396 : row11396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11396 := by decide +kernel

theorem rowEval11396 (x : Key → ℝ) : Integer.Sparse.eval row11396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11396, Integer.Sparse.eval_collectBalanced, rawRowCheck11396]

theorem rawRowCheck11397 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form19 = rawRow11397 := by decide +kernel

theorem rowCheck11397 : row11397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11397 := by decide +kernel

theorem rowEval11397 (x : Key → ℝ) : Integer.Sparse.eval row11397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11397, Integer.Sparse.eval_collectBalanced, rawRowCheck11397]

theorem rawRowCheck11398 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form19 = rawRow11398 := by decide +kernel

theorem rowCheck11398 : row11398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11398 := by decide +kernel

theorem rowEval11398 (x : Key → ℝ) : Integer.Sparse.eval row11398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11398, Integer.Sparse.eval_collectBalanced, rawRowCheck11398]

theorem rawRowCheck11399 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form19 = rawRow11399 := by decide +kernel

theorem rowCheck11399 : row11399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11399 := by decide +kernel

theorem rowEval11399 (x : Key → ℝ) : Integer.Sparse.eval row11399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11399, Integer.Sparse.eval_collectBalanced, rawRowCheck11399]

theorem rawRowCheck11400 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form19 = rawRow11400 := by decide +kernel

theorem rowCheck11400 : row11400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11400 := by decide +kernel

theorem rowEval11400 (x : Key → ℝ) : Integer.Sparse.eval row11400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11400, Integer.Sparse.eval_collectBalanced, rawRowCheck11400]

theorem rawRowCheck11401 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form19 = rawRow11401 := by decide +kernel

theorem rowCheck11401 : row11401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11401 := by decide +kernel

theorem rowEval11401 (x : Key → ℝ) : Integer.Sparse.eval row11401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11401, Integer.Sparse.eval_collectBalanced, rawRowCheck11401]

theorem rawRowCheck11402 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form19 = rawRow11402 := by decide +kernel

theorem rowCheck11402 : row11402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11402 := by decide +kernel

theorem rowEval11402 (x : Key → ℝ) : Integer.Sparse.eval row11402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11402, Integer.Sparse.eval_collectBalanced, rawRowCheck11402]

theorem rawRowCheck11403 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form19 = rawRow11403 := by decide +kernel

theorem rowCheck11403 : row11403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11403 := by decide +kernel

theorem rowEval11403 (x : Key → ℝ) : Integer.Sparse.eval row11403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11403, Integer.Sparse.eval_collectBalanced, rawRowCheck11403]

theorem rawRowCheck11404 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form19 = rawRow11404 := by decide +kernel

theorem rowCheck11404 : row11404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11404 := by decide +kernel

theorem rowEval11404 (x : Key → ℝ) : Integer.Sparse.eval row11404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11404, Integer.Sparse.eval_collectBalanced, rawRowCheck11404]

theorem rawRowCheck11405 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form19 = rawRow11405 := by decide +kernel

theorem rowCheck11405 : row11405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11405 := by decide +kernel

theorem rowEval11405 (x : Key → ℝ) : Integer.Sparse.eval row11405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11405, Integer.Sparse.eval_collectBalanced, rawRowCheck11405]

theorem rawRowCheck11406 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form19 = rawRow11406 := by decide +kernel

theorem rowCheck11406 : row11406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11406 := by decide +kernel

theorem rowEval11406 (x : Key → ℝ) : Integer.Sparse.eval row11406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11406, Integer.Sparse.eval_collectBalanced, rawRowCheck11406]

theorem rawRowCheck11407 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form19 = rawRow11407 := by decide +kernel

theorem rowCheck11407 : row11407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11407 := by decide +kernel

theorem rowEval11407 (x : Key → ℝ) : Integer.Sparse.eval row11407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11407, Integer.Sparse.eval_collectBalanced, rawRowCheck11407]

theorem rawRowCheck11408 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form19 = rawRow11408 := by decide +kernel

theorem rowCheck11408 : row11408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11408 := by decide +kernel

theorem rowEval11408 (x : Key → ℝ) : Integer.Sparse.eval row11408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11408, Integer.Sparse.eval_collectBalanced, rawRowCheck11408]

theorem rawRowCheck11409 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form19 = rawRow11409 := by decide +kernel

theorem rowCheck11409 : row11409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11409 := by decide +kernel

theorem rowEval11409 (x : Key → ℝ) : Integer.Sparse.eval row11409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11409, Integer.Sparse.eval_collectBalanced, rawRowCheck11409]

theorem rawRowCheck11410 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form19 = rawRow11410 := by decide +kernel

theorem rowCheck11410 : row11410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11410 := by decide +kernel

theorem rowEval11410 (x : Key → ℝ) : Integer.Sparse.eval row11410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11410, Integer.Sparse.eval_collectBalanced, rawRowCheck11410]

theorem rawRowCheck11411 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form19 = rawRow11411 := by decide +kernel

theorem rowCheck11411 : row11411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11411 := by decide +kernel

theorem rowEval11411 (x : Key → ℝ) : Integer.Sparse.eval row11411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11411, Integer.Sparse.eval_collectBalanced, rawRowCheck11411]

theorem rawRowCheck11412 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form19 = rawRow11412 := by decide +kernel

theorem rowCheck11412 : row11412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11412 := by decide +kernel

theorem rowEval11412 (x : Key → ℝ) : Integer.Sparse.eval row11412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11412, Integer.Sparse.eval_collectBalanced, rawRowCheck11412]

theorem rawRowCheck11413 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form19 = rawRow11413 := by decide +kernel

theorem rowCheck11413 : row11413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11413 := by decide +kernel

theorem rowEval11413 (x : Key → ℝ) : Integer.Sparse.eval row11413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11413, Integer.Sparse.eval_collectBalanced, rawRowCheck11413]

theorem rawRowCheck11414 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form20 = rawRow11414 := by decide +kernel

theorem rowCheck11414 : row11414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11414 := by decide +kernel

theorem rowEval11414 (x : Key → ℝ) : Integer.Sparse.eval row11414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11414, Integer.Sparse.eval_collectBalanced, rawRowCheck11414]

theorem rawRowCheck11415 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form20 = rawRow11415 := by decide +kernel

theorem rowCheck11415 : row11415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11415 := by decide +kernel

theorem rowEval11415 (x : Key → ℝ) : Integer.Sparse.eval row11415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11415, Integer.Sparse.eval_collectBalanced, rawRowCheck11415]

theorem rawRowCheck11416 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form20 = rawRow11416 := by decide +kernel

theorem rowCheck11416 : row11416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11416 := by decide +kernel

theorem rowEval11416 (x : Key → ℝ) : Integer.Sparse.eval row11416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11416, Integer.Sparse.eval_collectBalanced, rawRowCheck11416]

theorem rawRowCheck11417 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form20 = rawRow11417 := by decide +kernel

theorem rowCheck11417 : row11417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11417 := by decide +kernel

theorem rowEval11417 (x : Key → ℝ) : Integer.Sparse.eval row11417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11417, Integer.Sparse.eval_collectBalanced, rawRowCheck11417]

theorem rawRowCheck11418 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form20 = rawRow11418 := by decide +kernel

theorem rowCheck11418 : row11418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11418 := by decide +kernel

theorem rowEval11418 (x : Key → ℝ) : Integer.Sparse.eval row11418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11418, Integer.Sparse.eval_collectBalanced, rawRowCheck11418]

theorem rawRowCheck11419 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form20 = rawRow11419 := by decide +kernel

theorem rowCheck11419 : row11419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11419 := by decide +kernel

theorem rowEval11419 (x : Key → ℝ) : Integer.Sparse.eval row11419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11419, Integer.Sparse.eval_collectBalanced, rawRowCheck11419]

theorem rawRowCheck11420 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form20 = rawRow11420 := by decide +kernel

theorem rowCheck11420 : row11420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11420 := by decide +kernel

theorem rowEval11420 (x : Key → ℝ) : Integer.Sparse.eval row11420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11420, Integer.Sparse.eval_collectBalanced, rawRowCheck11420]

theorem rawRowCheck11421 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form20 = rawRow11421 := by decide +kernel

theorem rowCheck11421 : row11421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11421 := by decide +kernel

theorem rowEval11421 (x : Key → ℝ) : Integer.Sparse.eval row11421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11421, Integer.Sparse.eval_collectBalanced, rawRowCheck11421]

theorem rawRowCheck11422 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form20 = rawRow11422 := by decide +kernel

theorem rowCheck11422 : row11422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11422 := by decide +kernel

theorem rowEval11422 (x : Key → ℝ) : Integer.Sparse.eval row11422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11422, Integer.Sparse.eval_collectBalanced, rawRowCheck11422]

theorem rawRowCheck11423 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form20 = rawRow11423 := by decide +kernel

theorem rowCheck11423 : row11423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11423 := by decide +kernel

theorem rowEval11423 (x : Key → ℝ) : Integer.Sparse.eval row11423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11423, Integer.Sparse.eval_collectBalanced, rawRowCheck11423]

theorem rawRowCheck11424 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form20 = rawRow11424 := by decide +kernel

theorem rowCheck11424 : row11424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11424 := by decide +kernel

theorem rowEval11424 (x : Key → ℝ) : Integer.Sparse.eval row11424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11424, Integer.Sparse.eval_collectBalanced, rawRowCheck11424]

theorem rawRowCheck11425 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form20 = rawRow11425 := by decide +kernel

theorem rowCheck11425 : row11425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11425 := by decide +kernel

theorem rowEval11425 (x : Key → ℝ) : Integer.Sparse.eval row11425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11425, Integer.Sparse.eval_collectBalanced, rawRowCheck11425]

theorem rawRowCheck11426 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form20 = rawRow11426 := by decide +kernel

theorem rowCheck11426 : row11426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11426 := by decide +kernel

theorem rowEval11426 (x : Key → ℝ) : Integer.Sparse.eval row11426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11426, Integer.Sparse.eval_collectBalanced, rawRowCheck11426]

theorem rawRowCheck11427 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form20 = rawRow11427 := by decide +kernel

theorem rowCheck11427 : row11427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11427 := by decide +kernel

theorem rowEval11427 (x : Key → ℝ) : Integer.Sparse.eval row11427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11427, Integer.Sparse.eval_collectBalanced, rawRowCheck11427]

theorem rawRowCheck11428 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form20 = rawRow11428 := by decide +kernel

theorem rowCheck11428 : row11428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11428 := by decide +kernel

theorem rowEval11428 (x : Key → ℝ) : Integer.Sparse.eval row11428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11428, Integer.Sparse.eval_collectBalanced, rawRowCheck11428]

theorem rawRowCheck11429 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form20 = rawRow11429 := by decide +kernel

theorem rowCheck11429 : row11429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11429 := by decide +kernel

theorem rowEval11429 (x : Key → ℝ) : Integer.Sparse.eval row11429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11429, Integer.Sparse.eval_collectBalanced, rawRowCheck11429]

theorem rawRowCheck11430 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form20 = rawRow11430 := by decide +kernel

theorem rowCheck11430 : row11430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11430 := by decide +kernel

theorem rowEval11430 (x : Key → ℝ) : Integer.Sparse.eval row11430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11430, Integer.Sparse.eval_collectBalanced, rawRowCheck11430]

theorem rawRowCheck11431 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form20 = rawRow11431 := by decide +kernel

theorem rowCheck11431 : row11431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11431 := by decide +kernel

theorem rowEval11431 (x : Key → ℝ) : Integer.Sparse.eval row11431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11431, Integer.Sparse.eval_collectBalanced, rawRowCheck11431]

theorem rawRowCheck11432 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form20 = rawRow11432 := by decide +kernel

theorem rowCheck11432 : row11432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11432 := by decide +kernel

theorem rowEval11432 (x : Key → ℝ) : Integer.Sparse.eval row11432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11432, Integer.Sparse.eval_collectBalanced, rawRowCheck11432]

theorem rawRowCheck11433 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form20 = rawRow11433 := by decide +kernel

theorem rowCheck11433 : row11433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11433 := by decide +kernel

theorem rowEval11433 (x : Key → ℝ) : Integer.Sparse.eval row11433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11433, Integer.Sparse.eval_collectBalanced, rawRowCheck11433]

theorem rawRowCheck11434 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form20 = rawRow11434 := by decide +kernel

theorem rowCheck11434 : row11434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11434 := by decide +kernel

theorem rowEval11434 (x : Key → ℝ) : Integer.Sparse.eval row11434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11434, Integer.Sparse.eval_collectBalanced, rawRowCheck11434]

theorem rawRowCheck11435 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form20 = rawRow11435 := by decide +kernel

theorem rowCheck11435 : row11435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11435 := by decide +kernel

theorem rowEval11435 (x : Key → ℝ) : Integer.Sparse.eval row11435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11435, Integer.Sparse.eval_collectBalanced, rawRowCheck11435]

theorem rawRowCheck11436 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form20 = rawRow11436 := by decide +kernel

theorem rowCheck11436 : row11436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11436 := by decide +kernel

theorem rowEval11436 (x : Key → ℝ) : Integer.Sparse.eval row11436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11436, Integer.Sparse.eval_collectBalanced, rawRowCheck11436]

theorem rawRowCheck11437 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form20 = rawRow11437 := by decide +kernel

theorem rowCheck11437 : row11437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11437 := by decide +kernel

theorem rowEval11437 (x : Key → ℝ) : Integer.Sparse.eval row11437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11437, Integer.Sparse.eval_collectBalanced, rawRowCheck11437]

theorem rawRowCheck11438 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form20 = rawRow11438 := by decide +kernel

theorem rowCheck11438 : row11438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11438 := by decide +kernel

theorem rowEval11438 (x : Key → ℝ) : Integer.Sparse.eval row11438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11438, Integer.Sparse.eval_collectBalanced, rawRowCheck11438]

theorem rawRowCheck11439 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form20 = rawRow11439 := by decide +kernel

theorem rowCheck11439 : row11439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11439 := by decide +kernel

theorem rowEval11439 (x : Key → ℝ) : Integer.Sparse.eval row11439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11439, Integer.Sparse.eval_collectBalanced, rawRowCheck11439]

theorem rawRowCheck11440 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form20 = rawRow11440 := by decide +kernel

theorem rowCheck11440 : row11440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11440 := by decide +kernel

theorem rowEval11440 (x : Key → ℝ) : Integer.Sparse.eval row11440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11440, Integer.Sparse.eval_collectBalanced, rawRowCheck11440]

theorem rawRowCheck11441 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form20 = rawRow11441 := by decide +kernel

theorem rowCheck11441 : row11441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11441 := by decide +kernel

theorem rowEval11441 (x : Key → ℝ) : Integer.Sparse.eval row11441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11441, Integer.Sparse.eval_collectBalanced, rawRowCheck11441]

theorem rawRowCheck11442 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form20 = rawRow11442 := by decide +kernel

theorem rowCheck11442 : row11442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11442 := by decide +kernel

theorem rowEval11442 (x : Key → ℝ) : Integer.Sparse.eval row11442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11442, Integer.Sparse.eval_collectBalanced, rawRowCheck11442]

theorem rawRowCheck11443 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form20 = rawRow11443 := by decide +kernel

theorem rowCheck11443 : row11443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11443 := by decide +kernel

theorem rowEval11443 (x : Key → ℝ) : Integer.Sparse.eval row11443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11443, Integer.Sparse.eval_collectBalanced, rawRowCheck11443]

theorem rawRowCheck11444 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form20 = rawRow11444 := by decide +kernel

theorem rowCheck11444 : row11444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11444 := by decide +kernel

theorem rowEval11444 (x : Key → ℝ) : Integer.Sparse.eval row11444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11444, Integer.Sparse.eval_collectBalanced, rawRowCheck11444]

theorem rawRowCheck11445 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form20 = rawRow11445 := by decide +kernel

theorem rowCheck11445 : row11445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11445 := by decide +kernel

theorem rowEval11445 (x : Key → ℝ) : Integer.Sparse.eval row11445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11445, Integer.Sparse.eval_collectBalanced, rawRowCheck11445]

theorem rawRowCheck11446 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form20 = rawRow11446 := by decide +kernel

theorem rowCheck11446 : row11446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11446 := by decide +kernel

theorem rowEval11446 (x : Key → ℝ) : Integer.Sparse.eval row11446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11446, Integer.Sparse.eval_collectBalanced, rawRowCheck11446]

theorem rawRowCheck11447 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form20 = rawRow11447 := by decide +kernel

theorem rowCheck11447 : row11447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11447 := by decide +kernel

theorem rowEval11447 (x : Key → ℝ) : Integer.Sparse.eval row11447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11447, Integer.Sparse.eval_collectBalanced, rawRowCheck11447]

theorem rawRowCheck11448 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form20 = rawRow11448 := by decide +kernel

theorem rowCheck11448 : row11448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11448 := by decide +kernel

theorem rowEval11448 (x : Key → ℝ) : Integer.Sparse.eval row11448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11448, Integer.Sparse.eval_collectBalanced, rawRowCheck11448]

theorem rawRowCheck11449 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form20 = rawRow11449 := by decide +kernel

theorem rowCheck11449 : row11449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11449 := by decide +kernel

theorem rowEval11449 (x : Key → ℝ) : Integer.Sparse.eval row11449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11449, Integer.Sparse.eval_collectBalanced, rawRowCheck11449]

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

theorem entryCheck21_12 : entry21_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_12 k)) := by decide +kernel

theorem rowsSound21_12 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval11126 x
  · exact rowEval11127 x
  · exact rowEval11128 x
  · exact rowEval11129 x
  · exact rowEval11130 x
  · exact rowEval11131 x
  · exact rowEval11132 x
  · exact rowEval11133 x
  · exact rowEval11134 x
  · exact rowEval11135 x
  · exact rowEval11136 x
  · exact rowEval11137 x
  · exact rowEval11138 x
  · exact rowEval11139 x
  · exact rowEval11140 x
  · exact rowEval11141 x
  · exact rowEval11142 x
  · exact rowEval11143 x
  · exact rowEval11144 x
  · exact rowEval11145 x
  · exact rowEval11146 x
  · exact rowEval11147 x
  · exact rowEval11148 x
  · exact rowEval11149 x
  · exact rowEval11150 x
  · exact rowEval11151 x
  · exact rowEval11152 x
  · exact rowEval11153 x
  · exact rowEval11154 x
  · exact rowEval11155 x
  · exact rowEval11156 x
  · exact rowEval11157 x
  · exact rowEval11158 x
  · exact rowEval11159 x
  · exact rowEval11160 x
  · exact rowEval11161 x

theorem entryEval21_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_12 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck21_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_12]

theorem entryCheck21_14 : entry21_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_14 k)) := by decide +kernel

theorem rowsSound21_14 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval11198 x
  · exact rowEval11199 x
  · exact rowEval11200 x
  · exact rowEval11201 x
  · exact rowEval11202 x
  · exact rowEval11203 x
  · exact rowEval11204 x
  · exact rowEval11205 x
  · exact rowEval11206 x
  · exact rowEval11207 x
  · exact rowEval11208 x
  · exact rowEval11209 x
  · exact rowEval11210 x
  · exact rowEval11211 x
  · exact rowEval11212 x
  · exact rowEval11213 x
  · exact rowEval11214 x
  · exact rowEval11215 x
  · exact rowEval11216 x
  · exact rowEval11217 x
  · exact rowEval11218 x
  · exact rowEval11219 x
  · exact rowEval11220 x
  · exact rowEval11221 x
  · exact rowEval11222 x
  · exact rowEval11223 x
  · exact rowEval11224 x
  · exact rowEval11225 x
  · exact rowEval11226 x
  · exact rowEval11227 x
  · exact rowEval11228 x
  · exact rowEval11229 x
  · exact rowEval11230 x
  · exact rowEval11231 x
  · exact rowEval11232 x
  · exact rowEval11233 x

theorem entryEval21_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_14 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck21_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_14]

theorem entryCheck21_16 : entry21_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_16 k)) := by decide +kernel

theorem rowsSound21_16 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval11270 x
  · exact rowEval11271 x
  · exact rowEval11272 x
  · exact rowEval11273 x
  · exact rowEval11274 x
  · exact rowEval11275 x
  · exact rowEval11276 x
  · exact rowEval11277 x
  · exact rowEval11278 x
  · exact rowEval11279 x
  · exact rowEval11280 x
  · exact rowEval11281 x
  · exact rowEval11282 x
  · exact rowEval11283 x
  · exact rowEval11284 x
  · exact rowEval11285 x
  · exact rowEval11286 x
  · exact rowEval11287 x
  · exact rowEval11288 x
  · exact rowEval11289 x
  · exact rowEval11290 x
  · exact rowEval11291 x
  · exact rowEval11292 x
  · exact rowEval11293 x
  · exact rowEval11294 x
  · exact rowEval11295 x
  · exact rowEval11296 x
  · exact rowEval11297 x
  · exact rowEval11298 x
  · exact rowEval11299 x
  · exact rowEval11300 x
  · exact rowEval11301 x
  · exact rowEval11302 x
  · exact rowEval11303 x
  · exact rowEval11304 x
  · exact rowEval11305 x

theorem entryEval21_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_16 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck21_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_16]

theorem entryCheck21_19 : entry21_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_19 k)) := by decide +kernel

theorem rowsSound21_19 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval11378 x
  · exact rowEval11379 x
  · exact rowEval11380 x
  · exact rowEval11381 x
  · exact rowEval11382 x
  · exact rowEval11383 x
  · exact rowEval11384 x
  · exact rowEval11385 x
  · exact rowEval11386 x
  · exact rowEval11387 x
  · exact rowEval11388 x
  · exact rowEval11389 x
  · exact rowEval11390 x
  · exact rowEval11391 x
  · exact rowEval11392 x
  · exact rowEval11393 x
  · exact rowEval11394 x
  · exact rowEval11395 x
  · exact rowEval11396 x
  · exact rowEval11397 x
  · exact rowEval11398 x
  · exact rowEval11399 x
  · exact rowEval11400 x
  · exact rowEval11401 x
  · exact rowEval11402 x
  · exact rowEval11403 x
  · exact rowEval11404 x
  · exact rowEval11405 x
  · exact rowEval11406 x
  · exact rowEval11407 x
  · exact rowEval11408 x
  · exact rowEval11409 x
  · exact rowEval11410 x
  · exact rowEval11411 x
  · exact rowEval11412 x
  · exact rowEval11413 x

theorem entryEval21_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_19 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck21_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_19]

theorem entryCheck21_20 : entry21_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_20 k)) := by decide +kernel

theorem rowsSound21_20 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval11414 x
  · exact rowEval11415 x
  · exact rowEval11416 x
  · exact rowEval11417 x
  · exact rowEval11418 x
  · exact rowEval11419 x
  · exact rowEval11420 x
  · exact rowEval11421 x
  · exact rowEval11422 x
  · exact rowEval11423 x
  · exact rowEval11424 x
  · exact rowEval11425 x
  · exact rowEval11426 x
  · exact rowEval11427 x
  · exact rowEval11428 x
  · exact rowEval11429 x
  · exact rowEval11430 x
  · exact rowEval11431 x
  · exact rowEval11432 x
  · exact rowEval11433 x
  · exact rowEval11434 x
  · exact rowEval11435 x
  · exact rowEval11436 x
  · exact rowEval11437 x
  · exact rowEval11438 x
  · exact rowEval11439 x
  · exact rowEval11440 x
  · exact rowEval11441 x
  · exact rowEval11442 x
  · exact rowEval11443 x
  · exact rowEval11444 x
  · exact rowEval11445 x
  · exact rowEval11446 x
  · exact rowEval11447 x
  · exact rowEval11448 x
  · exact rowEval11449 x

theorem entryEval21_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_20 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck21_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_20]

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

theorem rawRowCheck12311 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form21 = rawRow12311 := by decide +kernel

theorem rowCheck12311 : row12311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12311 := by decide +kernel

theorem rowEval12311 (x : Key → ℝ) : Integer.Sparse.eval row12311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12311, Integer.Sparse.eval_collectBalanced, rawRowCheck12311]

theorem rawRowCheck12312 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form21 = rawRow12312 := by decide +kernel

theorem rowCheck12312 : row12312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12312 := by decide +kernel

theorem rowEval12312 (x : Key → ℝ) : Integer.Sparse.eval row12312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12312, Integer.Sparse.eval_collectBalanced, rawRowCheck12312]

theorem rawRowCheck12313 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form21 = rawRow12313 := by decide +kernel

theorem rowCheck12313 : row12313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12313 := by decide +kernel

theorem rowEval12313 (x : Key → ℝ) : Integer.Sparse.eval row12313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12313, Integer.Sparse.eval_collectBalanced, rawRowCheck12313]

theorem rawRowCheck12314 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form21 = rawRow12314 := by decide +kernel

theorem rowCheck12314 : row12314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12314 := by decide +kernel

theorem rowEval12314 (x : Key → ℝ) : Integer.Sparse.eval row12314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12314, Integer.Sparse.eval_collectBalanced, rawRowCheck12314]

theorem rawRowCheck12315 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form21 = rawRow12315 := by decide +kernel

theorem rowCheck12315 : row12315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12315 := by decide +kernel

theorem rowEval12315 (x : Key → ℝ) : Integer.Sparse.eval row12315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck12315, Integer.Sparse.eval_collectBalanced, rawRowCheck12315]

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

theorem entryCheck24_21 : entry24_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_21 k)) := by decide +kernel

theorem rowsSound24_21 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval12311 x
  · exact rowEval12312 x
  · exact rowEval12313 x
  · exact rowEval12314 x
  · exact rowEval12315 x

theorem entryEval24_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_21 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck24_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_21]

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

theorem rawRowCheck12499 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form21 = rawRow12499 := by decide +kernel

theorem rowCheck12499 : row12499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12499 := by decide +kernel

theorem rowEval12499 (x : Key → ℝ) : Integer.Sparse.eval row12499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12499, Integer.Sparse.eval_collectBalanced, rawRowCheck12499]

theorem rawRowCheck12500 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form21 = rawRow12500 := by decide +kernel

theorem rowCheck12500 : row12500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12500 := by decide +kernel

theorem rowEval12500 (x : Key → ℝ) : Integer.Sparse.eval row12500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12500, Integer.Sparse.eval_collectBalanced, rawRowCheck12500]

theorem rawRowCheck12501 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form21 = rawRow12501 := by decide +kernel

theorem rowCheck12501 : row12501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12501 := by decide +kernel

theorem rowEval12501 (x : Key → ℝ) : Integer.Sparse.eval row12501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12501, Integer.Sparse.eval_collectBalanced, rawRowCheck12501]

theorem rawRowCheck12502 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form21 = rawRow12502 := by decide +kernel

theorem rowCheck12502 : row12502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12502 := by decide +kernel

theorem rowEval12502 (x : Key → ℝ) : Integer.Sparse.eval row12502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12502, Integer.Sparse.eval_collectBalanced, rawRowCheck12502]

theorem rawRowCheck12503 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form21 = rawRow12503 := by decide +kernel

theorem rowCheck12503 : row12503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12503 := by decide +kernel

theorem rowEval12503 (x : Key → ℝ) : Integer.Sparse.eval row12503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12503, Integer.Sparse.eval_collectBalanced, rawRowCheck12503]

theorem rawRowCheck12504 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form21 = rawRow12504 := by decide +kernel

theorem rowCheck12504 : row12504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12504 := by decide +kernel

theorem rowEval12504 (x : Key → ℝ) : Integer.Sparse.eval row12504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12504, Integer.Sparse.eval_collectBalanced, rawRowCheck12504]

theorem rawRowCheck12505 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form21 = rawRow12505 := by decide +kernel

theorem rowCheck12505 : row12505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12505 := by decide +kernel

theorem rowEval12505 (x : Key → ℝ) : Integer.Sparse.eval row12505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12505, Integer.Sparse.eval_collectBalanced, rawRowCheck12505]

theorem rawRowCheck12506 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form21 = rawRow12506 := by decide +kernel

theorem rowCheck12506 : row12506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12506 := by decide +kernel

theorem rowEval12506 (x : Key → ℝ) : Integer.Sparse.eval row12506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12506, Integer.Sparse.eval_collectBalanced, rawRowCheck12506]

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

theorem entryCheck25_21 : entry25_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_21 k)) := by decide +kernel

theorem rowsSound25_21 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval12499 x
  · exact rowEval12500 x
  · exact rowEval12501 x
  · exact rowEval12502 x
  · exact rowEval12503 x
  · exact rowEval12504 x
  · exact rowEval12505 x
  · exact rowEval12506 x

theorem entryEval25_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_21 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck25_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_21]

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

theorem entryEvalRow21_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 21 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 21).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval21_0_e B hB
  · exact entryEval21_1 B hB
  · exact entryEval21_2_e B hB
  · exact entryEval21_3 B hB
  · exact entryEval21_4_e B hB
  · exact entryEval21_5_e B hB
  · exact entryEval21_6_e B hB
  · exact entryEval21_7_e B hB
  · exact entryEval21_8_e B hB
  · exact entryEval21_9_e B hB
  · exact entryEval21_10_e B hB
  · exact entryEval21_11_e B hB
  · exact entryEval21_12 B hB
  · exact entryEval21_13_e B hB
  · exact entryEval21_14 B hB
  · exact entryEval21_15_e B hB
  · exact entryEval21_16 B hB
  · exact entryEval21_17_e B hB
  · exact entryEval21_18_e B hB
  · exact entryEval21_19 B hB
  · exact entryEval21_20 B hB
  · exact entryEval21_21_e B hB
  · exact (entryEval22_21_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_21_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_21 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_21 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_21_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e_oai
