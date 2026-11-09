-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:15:42.125021+00:00
-- url     : https://prove2.me/submissions/7027d14e-72cf-45d8-b2a1-cf15dde61692

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_22_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10910 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form6 = rawRow10910 := by decide +kernel

theorem rowCheck10910 : row10910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10910 := by decide +kernel

theorem rowEval10910 (x : Key → ℝ) : Integer.Sparse.eval row10910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10910, Integer.Sparse.eval_collectBalanced, rawRowCheck10910]

theorem rawRowCheck10911 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form6 = rawRow10911 := by decide +kernel

theorem rowCheck10911 : row10911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10911 := by decide +kernel

theorem rowEval10911 (x : Key → ℝ) : Integer.Sparse.eval row10911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10911, Integer.Sparse.eval_collectBalanced, rawRowCheck10911]

theorem rawRowCheck10912 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form6 = rawRow10912 := by decide +kernel

theorem rowCheck10912 : row10912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10912 := by decide +kernel

theorem rowEval10912 (x : Key → ℝ) : Integer.Sparse.eval row10912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10912, Integer.Sparse.eval_collectBalanced, rawRowCheck10912]

theorem rawRowCheck10913 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form6 = rawRow10913 := by decide +kernel

theorem rowCheck10913 : row10913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10913 := by decide +kernel

theorem rowEval10913 (x : Key → ℝ) : Integer.Sparse.eval row10913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10913, Integer.Sparse.eval_collectBalanced, rawRowCheck10913]

theorem rawRowCheck10914 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form6 = rawRow10914 := by decide +kernel

theorem rowCheck10914 : row10914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10914 := by decide +kernel

theorem rowEval10914 (x : Key → ℝ) : Integer.Sparse.eval row10914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10914, Integer.Sparse.eval_collectBalanced, rawRowCheck10914]

theorem rawRowCheck10915 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form6 = rawRow10915 := by decide +kernel

theorem rowCheck10915 : row10915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10915 := by decide +kernel

theorem rowEval10915 (x : Key → ℝ) : Integer.Sparse.eval row10915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10915, Integer.Sparse.eval_collectBalanced, rawRowCheck10915]

theorem rawRowCheck10916 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form6 = rawRow10916 := by decide +kernel

theorem rowCheck10916 : row10916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10916 := by decide +kernel

theorem rowEval10916 (x : Key → ℝ) : Integer.Sparse.eval row10916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10916, Integer.Sparse.eval_collectBalanced, rawRowCheck10916]

theorem rawRowCheck10917 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form6 = rawRow10917 := by decide +kernel

theorem rowCheck10917 : row10917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10917 := by decide +kernel

theorem rowEval10917 (x : Key → ℝ) : Integer.Sparse.eval row10917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10917, Integer.Sparse.eval_collectBalanced, rawRowCheck10917]

theorem rawRowCheck10918 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form6 = rawRow10918 := by decide +kernel

theorem rowCheck10918 : row10918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10918 := by decide +kernel

theorem rowEval10918 (x : Key → ℝ) : Integer.Sparse.eval row10918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10918, Integer.Sparse.eval_collectBalanced, rawRowCheck10918]

theorem rawRowCheck10919 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form6 = rawRow10919 := by decide +kernel

theorem rowCheck10919 : row10919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10919 := by decide +kernel

theorem rowEval10919 (x : Key → ℝ) : Integer.Sparse.eval row10919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10919, Integer.Sparse.eval_collectBalanced, rawRowCheck10919]

theorem rawRowCheck10920 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form6 = rawRow10920 := by decide +kernel

theorem rowCheck10920 : row10920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10920 := by decide +kernel

theorem rowEval10920 (x : Key → ℝ) : Integer.Sparse.eval row10920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10920, Integer.Sparse.eval_collectBalanced, rawRowCheck10920]

theorem rawRowCheck10921 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form6 = rawRow10921 := by decide +kernel

theorem rowCheck10921 : row10921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10921 := by decide +kernel

theorem rowEval10921 (x : Key → ℝ) : Integer.Sparse.eval row10921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10921, Integer.Sparse.eval_collectBalanced, rawRowCheck10921]

theorem rawRowCheck10922 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form6 = rawRow10922 := by decide +kernel

theorem rowCheck10922 : row10922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10922 := by decide +kernel

theorem rowEval10922 (x : Key → ℝ) : Integer.Sparse.eval row10922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10922, Integer.Sparse.eval_collectBalanced, rawRowCheck10922]

theorem rawRowCheck10923 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form6 = rawRow10923 := by decide +kernel

theorem rowCheck10923 : row10923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10923 := by decide +kernel

theorem rowEval10923 (x : Key → ℝ) : Integer.Sparse.eval row10923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10923, Integer.Sparse.eval_collectBalanced, rawRowCheck10923]

theorem rawRowCheck10924 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form6 = rawRow10924 := by decide +kernel

theorem rowCheck10924 : row10924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10924 := by decide +kernel

theorem rowEval10924 (x : Key → ℝ) : Integer.Sparse.eval row10924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10924, Integer.Sparse.eval_collectBalanced, rawRowCheck10924]

theorem rawRowCheck10925 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form6 = rawRow10925 := by decide +kernel

theorem rowCheck10925 : row10925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10925 := by decide +kernel

theorem rowEval10925 (x : Key → ℝ) : Integer.Sparse.eval row10925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10925, Integer.Sparse.eval_collectBalanced, rawRowCheck10925]

theorem rawRowCheck10926 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form6 = rawRow10926 := by decide +kernel

theorem rowCheck10926 : row10926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10926 := by decide +kernel

theorem rowEval10926 (x : Key → ℝ) : Integer.Sparse.eval row10926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10926, Integer.Sparse.eval_collectBalanced, rawRowCheck10926]

theorem rawRowCheck10927 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form6 = rawRow10927 := by decide +kernel

theorem rowCheck10927 : row10927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10927 := by decide +kernel

theorem rowEval10927 (x : Key → ℝ) : Integer.Sparse.eval row10927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10927, Integer.Sparse.eval_collectBalanced, rawRowCheck10927]

theorem rawRowCheck10928 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form6 = rawRow10928 := by decide +kernel

theorem rowCheck10928 : row10928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10928 := by decide +kernel

theorem rowEval10928 (x : Key → ℝ) : Integer.Sparse.eval row10928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10928, Integer.Sparse.eval_collectBalanced, rawRowCheck10928]

theorem rawRowCheck10929 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form6 = rawRow10929 := by decide +kernel

theorem rowCheck10929 : row10929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10929 := by decide +kernel

theorem rowEval10929 (x : Key → ℝ) : Integer.Sparse.eval row10929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10929, Integer.Sparse.eval_collectBalanced, rawRowCheck10929]

theorem rawRowCheck10930 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form6 = rawRow10930 := by decide +kernel

theorem rowCheck10930 : row10930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10930 := by decide +kernel

theorem rowEval10930 (x : Key → ℝ) : Integer.Sparse.eval row10930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10930, Integer.Sparse.eval_collectBalanced, rawRowCheck10930]

theorem rawRowCheck10931 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form6 = rawRow10931 := by decide +kernel

theorem rowCheck10931 : row10931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10931 := by decide +kernel

theorem rowEval10931 (x : Key → ℝ) : Integer.Sparse.eval row10931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10931, Integer.Sparse.eval_collectBalanced, rawRowCheck10931]

theorem rawRowCheck10932 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form6 = rawRow10932 := by decide +kernel

theorem rowCheck10932 : row10932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10932 := by decide +kernel

theorem rowEval10932 (x : Key → ℝ) : Integer.Sparse.eval row10932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10932, Integer.Sparse.eval_collectBalanced, rawRowCheck10932]

theorem rawRowCheck10933 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form6 = rawRow10933 := by decide +kernel

theorem rowCheck10933 : row10933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10933 := by decide +kernel

theorem rowEval10933 (x : Key → ℝ) : Integer.Sparse.eval row10933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10933, Integer.Sparse.eval_collectBalanced, rawRowCheck10933]

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

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11558 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form6 = rawRow11558 := by decide +kernel

theorem rowCheck11558 : row11558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11558 := by decide +kernel

theorem rowEval11558 (x : Key → ℝ) : Integer.Sparse.eval row11558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11558, Integer.Sparse.eval_collectBalanced, rawRowCheck11558]

theorem rawRowCheck11559 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form6 = rawRow11559 := by decide +kernel

theorem rowCheck11559 : row11559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11559 := by decide +kernel

theorem rowEval11559 (x : Key → ℝ) : Integer.Sparse.eval row11559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11559, Integer.Sparse.eval_collectBalanced, rawRowCheck11559]

theorem rawRowCheck11560 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form6 = rawRow11560 := by decide +kernel

theorem rowCheck11560 : row11560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11560 := by decide +kernel

theorem rowEval11560 (x : Key → ℝ) : Integer.Sparse.eval row11560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11560, Integer.Sparse.eval_collectBalanced, rawRowCheck11560]

theorem rawRowCheck11561 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form6 = rawRow11561 := by decide +kernel

theorem rowCheck11561 : row11561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11561 := by decide +kernel

theorem rowEval11561 (x : Key → ℝ) : Integer.Sparse.eval row11561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11561, Integer.Sparse.eval_collectBalanced, rawRowCheck11561]

theorem rawRowCheck11562 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form6 = rawRow11562 := by decide +kernel

theorem rowCheck11562 : row11562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11562 := by decide +kernel

theorem rowEval11562 (x : Key → ℝ) : Integer.Sparse.eval row11562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11562, Integer.Sparse.eval_collectBalanced, rawRowCheck11562]

theorem rawRowCheck11563 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form6 = rawRow11563 := by decide +kernel

theorem rowCheck11563 : row11563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11563 := by decide +kernel

theorem rowEval11563 (x : Key → ℝ) : Integer.Sparse.eval row11563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11563, Integer.Sparse.eval_collectBalanced, rawRowCheck11563]

theorem rawRowCheck11564 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form6 = rawRow11564 := by decide +kernel

theorem rowCheck11564 : row11564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11564 := by decide +kernel

theorem rowEval11564 (x : Key → ℝ) : Integer.Sparse.eval row11564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11564, Integer.Sparse.eval_collectBalanced, rawRowCheck11564]

theorem rawRowCheck11565 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form6 = rawRow11565 := by decide +kernel

theorem rowCheck11565 : row11565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11565 := by decide +kernel

theorem rowEval11565 (x : Key → ℝ) : Integer.Sparse.eval row11565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11565, Integer.Sparse.eval_collectBalanced, rawRowCheck11565]

theorem rawRowCheck11566 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form6 = rawRow11566 := by decide +kernel

theorem rowCheck11566 : row11566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11566 := by decide +kernel

theorem rowEval11566 (x : Key → ℝ) : Integer.Sparse.eval row11566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11566, Integer.Sparse.eval_collectBalanced, rawRowCheck11566]

theorem rawRowCheck11567 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow11567 := by decide +kernel

theorem rowCheck11567 : row11567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11567 := by decide +kernel

theorem rowEval11567 (x : Key → ℝ) : Integer.Sparse.eval row11567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11567, Integer.Sparse.eval_collectBalanced, rawRowCheck11567]

theorem rawRowCheck11568 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow11568 := by decide +kernel

theorem rowCheck11568 : row11568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11568 := by decide +kernel

theorem rowEval11568 (x : Key → ℝ) : Integer.Sparse.eval row11568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11568, Integer.Sparse.eval_collectBalanced, rawRowCheck11568]

theorem rawRowCheck11569 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow11569 := by decide +kernel

theorem rowCheck11569 : row11569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11569 := by decide +kernel

theorem rowEval11569 (x : Key → ℝ) : Integer.Sparse.eval row11569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11569, Integer.Sparse.eval_collectBalanced, rawRowCheck11569]

theorem rawRowCheck11630 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form12 = rawRow11630 := by decide +kernel

theorem rowCheck11630 : row11630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11630 := by decide +kernel

theorem rowEval11630 (x : Key → ℝ) : Integer.Sparse.eval row11630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11630, Integer.Sparse.eval_collectBalanced, rawRowCheck11630]

theorem rawRowCheck11631 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form12 = rawRow11631 := by decide +kernel

theorem rowCheck11631 : row11631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11631 := by decide +kernel

theorem rowEval11631 (x : Key → ℝ) : Integer.Sparse.eval row11631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11631, Integer.Sparse.eval_collectBalanced, rawRowCheck11631]

theorem rawRowCheck11632 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form12 = rawRow11632 := by decide +kernel

theorem rowCheck11632 : row11632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11632 := by decide +kernel

theorem rowEval11632 (x : Key → ℝ) : Integer.Sparse.eval row11632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11632, Integer.Sparse.eval_collectBalanced, rawRowCheck11632]

theorem rawRowCheck11633 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form12 = rawRow11633 := by decide +kernel

theorem rowCheck11633 : row11633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11633 := by decide +kernel

theorem rowEval11633 (x : Key → ℝ) : Integer.Sparse.eval row11633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11633, Integer.Sparse.eval_collectBalanced, rawRowCheck11633]

theorem rawRowCheck11634 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form12 = rawRow11634 := by decide +kernel

theorem rowCheck11634 : row11634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11634 := by decide +kernel

theorem rowEval11634 (x : Key → ℝ) : Integer.Sparse.eval row11634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11634, Integer.Sparse.eval_collectBalanced, rawRowCheck11634]

theorem rawRowCheck11635 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form12 = rawRow11635 := by decide +kernel

theorem rowCheck11635 : row11635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11635 := by decide +kernel

theorem rowEval11635 (x : Key → ℝ) : Integer.Sparse.eval row11635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11635, Integer.Sparse.eval_collectBalanced, rawRowCheck11635]

theorem rawRowCheck11636 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form12 = rawRow11636 := by decide +kernel

theorem rowCheck11636 : row11636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11636 := by decide +kernel

theorem rowEval11636 (x : Key → ℝ) : Integer.Sparse.eval row11636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11636, Integer.Sparse.eval_collectBalanced, rawRowCheck11636]

theorem rawRowCheck11637 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form12 = rawRow11637 := by decide +kernel

theorem rowCheck11637 : row11637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11637 := by decide +kernel

theorem rowEval11637 (x : Key → ℝ) : Integer.Sparse.eval row11637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11637, Integer.Sparse.eval_collectBalanced, rawRowCheck11637]

theorem rawRowCheck11638 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form12 = rawRow11638 := by decide +kernel

theorem rowCheck11638 : row11638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11638 := by decide +kernel

theorem rowEval11638 (x : Key → ℝ) : Integer.Sparse.eval row11638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11638, Integer.Sparse.eval_collectBalanced, rawRowCheck11638]

theorem rawRowCheck11639 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form12 = rawRow11639 := by decide +kernel

theorem rowCheck11639 : row11639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11639 := by decide +kernel

theorem rowEval11639 (x : Key → ℝ) : Integer.Sparse.eval row11639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11639, Integer.Sparse.eval_collectBalanced, rawRowCheck11639]

theorem rawRowCheck11640 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form12 = rawRow11640 := by decide +kernel

theorem rowCheck11640 : row11640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11640 := by decide +kernel

theorem rowEval11640 (x : Key → ℝ) : Integer.Sparse.eval row11640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11640, Integer.Sparse.eval_collectBalanced, rawRowCheck11640]

theorem rawRowCheck11641 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form12 = rawRow11641 := by decide +kernel

theorem rowCheck11641 : row11641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11641 := by decide +kernel

theorem rowEval11641 (x : Key → ℝ) : Integer.Sparse.eval row11641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11641, Integer.Sparse.eval_collectBalanced, rawRowCheck11641]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11654 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form14 = rawRow11654 := by decide +kernel

theorem rowCheck11654 : row11654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11654 := by decide +kernel

theorem rowEval11654 (x : Key → ℝ) : Integer.Sparse.eval row11654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11654, Integer.Sparse.eval_collectBalanced, rawRowCheck11654]

theorem rawRowCheck11655 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form14 = rawRow11655 := by decide +kernel

theorem rowCheck11655 : row11655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11655 := by decide +kernel

theorem rowEval11655 (x : Key → ℝ) : Integer.Sparse.eval row11655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11655, Integer.Sparse.eval_collectBalanced, rawRowCheck11655]

theorem rawRowCheck11656 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form14 = rawRow11656 := by decide +kernel

theorem rowCheck11656 : row11656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11656 := by decide +kernel

theorem rowEval11656 (x : Key → ℝ) : Integer.Sparse.eval row11656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11656, Integer.Sparse.eval_collectBalanced, rawRowCheck11656]

theorem rawRowCheck11657 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form14 = rawRow11657 := by decide +kernel

theorem rowCheck11657 : row11657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11657 := by decide +kernel

theorem rowEval11657 (x : Key → ℝ) : Integer.Sparse.eval row11657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11657, Integer.Sparse.eval_collectBalanced, rawRowCheck11657]

theorem rawRowCheck11658 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form14 = rawRow11658 := by decide +kernel

theorem rowCheck11658 : row11658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11658 := by decide +kernel

theorem rowEval11658 (x : Key → ℝ) : Integer.Sparse.eval row11658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11658, Integer.Sparse.eval_collectBalanced, rawRowCheck11658]

theorem rawRowCheck11659 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form14 = rawRow11659 := by decide +kernel

theorem rowCheck11659 : row11659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11659 := by decide +kernel

theorem rowEval11659 (x : Key → ℝ) : Integer.Sparse.eval row11659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11659, Integer.Sparse.eval_collectBalanced, rawRowCheck11659]

theorem rawRowCheck11660 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form14 = rawRow11660 := by decide +kernel

theorem rowCheck11660 : row11660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11660 := by decide +kernel

theorem rowEval11660 (x : Key → ℝ) : Integer.Sparse.eval row11660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11660, Integer.Sparse.eval_collectBalanced, rawRowCheck11660]

theorem rawRowCheck11661 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form14 = rawRow11661 := by decide +kernel

theorem rowCheck11661 : row11661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11661 := by decide +kernel

theorem rowEval11661 (x : Key → ℝ) : Integer.Sparse.eval row11661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11661, Integer.Sparse.eval_collectBalanced, rawRowCheck11661]

theorem rawRowCheck11662 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form14 = rawRow11662 := by decide +kernel

theorem rowCheck11662 : row11662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11662 := by decide +kernel

theorem rowEval11662 (x : Key → ℝ) : Integer.Sparse.eval row11662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11662, Integer.Sparse.eval_collectBalanced, rawRowCheck11662]

theorem rawRowCheck11663 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow11663 := by decide +kernel

theorem rowCheck11663 : row11663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11663 := by decide +kernel

theorem rowEval11663 (x : Key → ℝ) : Integer.Sparse.eval row11663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11663, Integer.Sparse.eval_collectBalanced, rawRowCheck11663]

theorem rawRowCheck11664 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow11664 := by decide +kernel

theorem rowCheck11664 : row11664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11664 := by decide +kernel

theorem rowEval11664 (x : Key → ℝ) : Integer.Sparse.eval row11664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11664, Integer.Sparse.eval_collectBalanced, rawRowCheck11664]

theorem rawRowCheck11665 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow11665 := by decide +kernel

theorem rowCheck11665 : row11665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11665 := by decide +kernel

theorem rowEval11665 (x : Key → ℝ) : Integer.Sparse.eval row11665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11665, Integer.Sparse.eval_collectBalanced, rawRowCheck11665]

theorem rawRowCheck11678 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form16 = rawRow11678 := by decide +kernel

theorem rowCheck11678 : row11678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11678 := by decide +kernel

theorem rowEval11678 (x : Key → ℝ) : Integer.Sparse.eval row11678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11678, Integer.Sparse.eval_collectBalanced, rawRowCheck11678]

theorem rawRowCheck11679 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form16 = rawRow11679 := by decide +kernel

theorem rowCheck11679 : row11679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11679 := by decide +kernel

theorem rowEval11679 (x : Key → ℝ) : Integer.Sparse.eval row11679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11679, Integer.Sparse.eval_collectBalanced, rawRowCheck11679]

theorem rawRowCheck11680 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form16 = rawRow11680 := by decide +kernel

theorem rowCheck11680 : row11680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11680 := by decide +kernel

theorem rowEval11680 (x : Key → ℝ) : Integer.Sparse.eval row11680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11680, Integer.Sparse.eval_collectBalanced, rawRowCheck11680]

theorem rawRowCheck11681 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form16 = rawRow11681 := by decide +kernel

theorem rowCheck11681 : row11681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11681 := by decide +kernel

theorem rowEval11681 (x : Key → ℝ) : Integer.Sparse.eval row11681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11681, Integer.Sparse.eval_collectBalanced, rawRowCheck11681]

theorem rawRowCheck11682 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form16 = rawRow11682 := by decide +kernel

theorem rowCheck11682 : row11682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11682 := by decide +kernel

theorem rowEval11682 (x : Key → ℝ) : Integer.Sparse.eval row11682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11682, Integer.Sparse.eval_collectBalanced, rawRowCheck11682]

theorem rawRowCheck11683 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form16 = rawRow11683 := by decide +kernel

theorem rowCheck11683 : row11683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11683 := by decide +kernel

theorem rowEval11683 (x : Key → ℝ) : Integer.Sparse.eval row11683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11683, Integer.Sparse.eval_collectBalanced, rawRowCheck11683]

theorem rawRowCheck11684 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form16 = rawRow11684 := by decide +kernel

theorem rowCheck11684 : row11684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11684 := by decide +kernel

theorem rowEval11684 (x : Key → ℝ) : Integer.Sparse.eval row11684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11684, Integer.Sparse.eval_collectBalanced, rawRowCheck11684]

theorem rawRowCheck11685 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form16 = rawRow11685 := by decide +kernel

theorem rowCheck11685 : row11685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11685 := by decide +kernel

theorem rowEval11685 (x : Key → ℝ) : Integer.Sparse.eval row11685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11685, Integer.Sparse.eval_collectBalanced, rawRowCheck11685]

theorem rawRowCheck11686 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form16 = rawRow11686 := by decide +kernel

theorem rowCheck11686 : row11686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11686 := by decide +kernel

theorem rowEval11686 (x : Key → ℝ) : Integer.Sparse.eval row11686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11686, Integer.Sparse.eval_collectBalanced, rawRowCheck11686]

theorem rawRowCheck11687 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow11687 := by decide +kernel

theorem rowCheck11687 : row11687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11687 := by decide +kernel

theorem rowEval11687 (x : Key → ℝ) : Integer.Sparse.eval row11687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11687, Integer.Sparse.eval_collectBalanced, rawRowCheck11687]

theorem rawRowCheck11688 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow11688 := by decide +kernel

theorem rowCheck11688 : row11688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11688 := by decide +kernel

theorem rowEval11688 (x : Key → ℝ) : Integer.Sparse.eval row11688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11688, Integer.Sparse.eval_collectBalanced, rawRowCheck11688]

theorem rawRowCheck11689 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow11689 := by decide +kernel

theorem rowCheck11689 : row11689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11689 := by decide +kernel

theorem rowEval11689 (x : Key → ℝ) : Integer.Sparse.eval row11689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11689, Integer.Sparse.eval_collectBalanced, rawRowCheck11689]

theorem rawRowCheck11714 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form19 = rawRow11714 := by decide +kernel

theorem rowCheck11714 : row11714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11714 := by decide +kernel

theorem rowEval11714 (x : Key → ℝ) : Integer.Sparse.eval row11714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11714, Integer.Sparse.eval_collectBalanced, rawRowCheck11714]

theorem rawRowCheck11715 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form19 = rawRow11715 := by decide +kernel

theorem rowCheck11715 : row11715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11715 := by decide +kernel

theorem rowEval11715 (x : Key → ℝ) : Integer.Sparse.eval row11715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11715, Integer.Sparse.eval_collectBalanced, rawRowCheck11715]

theorem rawRowCheck11716 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form19 = rawRow11716 := by decide +kernel

theorem rowCheck11716 : row11716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11716 := by decide +kernel

theorem rowEval11716 (x : Key → ℝ) : Integer.Sparse.eval row11716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11716, Integer.Sparse.eval_collectBalanced, rawRowCheck11716]

theorem rawRowCheck11717 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form19 = rawRow11717 := by decide +kernel

theorem rowCheck11717 : row11717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11717 := by decide +kernel

theorem rowEval11717 (x : Key → ℝ) : Integer.Sparse.eval row11717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11717, Integer.Sparse.eval_collectBalanced, rawRowCheck11717]

theorem rawRowCheck11718 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form19 = rawRow11718 := by decide +kernel

theorem rowCheck11718 : row11718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11718 := by decide +kernel

theorem rowEval11718 (x : Key → ℝ) : Integer.Sparse.eval row11718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11718, Integer.Sparse.eval_collectBalanced, rawRowCheck11718]

theorem rawRowCheck11719 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form19 = rawRow11719 := by decide +kernel

theorem rowCheck11719 : row11719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11719 := by decide +kernel

theorem rowEval11719 (x : Key → ℝ) : Integer.Sparse.eval row11719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11719, Integer.Sparse.eval_collectBalanced, rawRowCheck11719]

theorem rawRowCheck11720 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form19 = rawRow11720 := by decide +kernel

theorem rowCheck11720 : row11720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11720 := by decide +kernel

theorem rowEval11720 (x : Key → ℝ) : Integer.Sparse.eval row11720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11720, Integer.Sparse.eval_collectBalanced, rawRowCheck11720]

theorem rawRowCheck11721 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form19 = rawRow11721 := by decide +kernel

theorem rowCheck11721 : row11721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11721 := by decide +kernel

theorem rowEval11721 (x : Key → ℝ) : Integer.Sparse.eval row11721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11721, Integer.Sparse.eval_collectBalanced, rawRowCheck11721]

theorem rawRowCheck11722 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form19 = rawRow11722 := by decide +kernel

theorem rowCheck11722 : row11722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11722 := by decide +kernel

theorem rowEval11722 (x : Key → ℝ) : Integer.Sparse.eval row11722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11722, Integer.Sparse.eval_collectBalanced, rawRowCheck11722]

theorem rawRowCheck11723 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form19 = rawRow11723 := by decide +kernel

theorem rowCheck11723 : row11723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11723 := by decide +kernel

theorem rowEval11723 (x : Key → ℝ) : Integer.Sparse.eval row11723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11723, Integer.Sparse.eval_collectBalanced, rawRowCheck11723]

theorem rawRowCheck11724 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form19 = rawRow11724 := by decide +kernel

theorem rowCheck11724 : row11724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11724 := by decide +kernel

theorem rowEval11724 (x : Key → ℝ) : Integer.Sparse.eval row11724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11724, Integer.Sparse.eval_collectBalanced, rawRowCheck11724]

theorem rawRowCheck11725 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form19 = rawRow11725 := by decide +kernel

theorem rowCheck11725 : row11725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11725 := by decide +kernel

theorem rowEval11725 (x : Key → ℝ) : Integer.Sparse.eval row11725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11725, Integer.Sparse.eval_collectBalanced, rawRowCheck11725]

theorem rawRowCheck11726 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form20 = rawRow11726 := by decide +kernel

theorem rowCheck11726 : row11726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11726 := by decide +kernel

theorem rowEval11726 (x : Key → ℝ) : Integer.Sparse.eval row11726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11726, Integer.Sparse.eval_collectBalanced, rawRowCheck11726]

theorem rawRowCheck11727 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form20 = rawRow11727 := by decide +kernel

theorem rowCheck11727 : row11727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11727 := by decide +kernel

theorem rowEval11727 (x : Key → ℝ) : Integer.Sparse.eval row11727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11727, Integer.Sparse.eval_collectBalanced, rawRowCheck11727]

theorem rawRowCheck11728 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form20 = rawRow11728 := by decide +kernel

theorem rowCheck11728 : row11728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11728 := by decide +kernel

theorem rowEval11728 (x : Key → ℝ) : Integer.Sparse.eval row11728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11728, Integer.Sparse.eval_collectBalanced, rawRowCheck11728]

theorem rawRowCheck11729 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form20 = rawRow11729 := by decide +kernel

theorem rowCheck11729 : row11729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11729 := by decide +kernel

theorem rowEval11729 (x : Key → ℝ) : Integer.Sparse.eval row11729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11729, Integer.Sparse.eval_collectBalanced, rawRowCheck11729]

theorem rawRowCheck11730 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form20 = rawRow11730 := by decide +kernel

theorem rowCheck11730 : row11730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11730 := by decide +kernel

theorem rowEval11730 (x : Key → ℝ) : Integer.Sparse.eval row11730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11730, Integer.Sparse.eval_collectBalanced, rawRowCheck11730]

theorem rawRowCheck11731 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form20 = rawRow11731 := by decide +kernel

theorem rowCheck11731 : row11731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11731 := by decide +kernel

theorem rowEval11731 (x : Key → ℝ) : Integer.Sparse.eval row11731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11731, Integer.Sparse.eval_collectBalanced, rawRowCheck11731]

theorem rawRowCheck11732 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form20 = rawRow11732 := by decide +kernel

theorem rowCheck11732 : row11732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11732 := by decide +kernel

theorem rowEval11732 (x : Key → ℝ) : Integer.Sparse.eval row11732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11732, Integer.Sparse.eval_collectBalanced, rawRowCheck11732]

theorem rawRowCheck11733 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form20 = rawRow11733 := by decide +kernel

theorem rowCheck11733 : row11733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11733 := by decide +kernel

theorem rowEval11733 (x : Key → ℝ) : Integer.Sparse.eval row11733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11733, Integer.Sparse.eval_collectBalanced, rawRowCheck11733]

theorem rawRowCheck11734 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form20 = rawRow11734 := by decide +kernel

theorem rowCheck11734 : row11734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11734 := by decide +kernel

theorem rowEval11734 (x : Key → ℝ) : Integer.Sparse.eval row11734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11734, Integer.Sparse.eval_collectBalanced, rawRowCheck11734]

theorem rawRowCheck11735 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form20 = rawRow11735 := by decide +kernel

theorem rowCheck11735 : row11735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11735 := by decide +kernel

theorem rowEval11735 (x : Key → ℝ) : Integer.Sparse.eval row11735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11735, Integer.Sparse.eval_collectBalanced, rawRowCheck11735]

theorem rawRowCheck11736 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form20 = rawRow11736 := by decide +kernel

theorem rowCheck11736 : row11736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11736 := by decide +kernel

theorem rowEval11736 (x : Key → ℝ) : Integer.Sparse.eval row11736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11736, Integer.Sparse.eval_collectBalanced, rawRowCheck11736]

theorem rawRowCheck11737 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form20 = rawRow11737 := by decide +kernel

theorem rowCheck11737 : row11737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11737 := by decide +kernel

theorem rowEval11737 (x : Key → ℝ) : Integer.Sparse.eval row11737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11737, Integer.Sparse.eval_collectBalanced, rawRowCheck11737]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck22_6 : entry22_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_6 k)) := by decide +kernel

theorem rowsSound22_6 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval11558 x
  · exact rowEval11559 x
  · exact rowEval11560 x
  · exact rowEval11561 x
  · exact rowEval11562 x
  · exact rowEval11563 x
  · exact rowEval11564 x
  · exact rowEval11565 x
  · exact rowEval11566 x
  · exact rowEval11567 x
  · exact rowEval11568 x
  · exact rowEval11569 x
  · exact rowEval10910 x
  · exact rowEval10911 x
  · exact rowEval10912 x
  · exact rowEval10913 x
  · exact rowEval10914 x
  · exact rowEval10915 x
  · exact rowEval10916 x
  · exact rowEval10917 x
  · exact rowEval10918 x
  · exact rowEval10919 x
  · exact rowEval10920 x
  · exact rowEval10921 x
  · exact rowEval10922 x
  · exact rowEval10923 x
  · exact rowEval10924 x
  · exact rowEval10925 x
  · exact rowEval10926 x
  · exact rowEval10927 x
  · exact rowEval10928 x
  · exact rowEval10929 x
  · exact rowEval10930 x
  · exact rowEval10931 x
  · exact rowEval10932 x
  · exact rowEval10933 x

theorem entryEval22_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_6 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck22_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_6]

theorem entryCheck22_12 : entry22_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_12 k)) := by decide +kernel

theorem rowsSound22_12 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval11630 x
  · exact rowEval11631 x
  · exact rowEval11632 x
  · exact rowEval11633 x
  · exact rowEval11634 x
  · exact rowEval11635 x
  · exact rowEval11636 x
  · exact rowEval11637 x
  · exact rowEval11638 x
  · exact rowEval11639 x
  · exact rowEval11640 x
  · exact rowEval11641 x
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

theorem entryEval22_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_12 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck22_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_12]

theorem entryCheck22_14 : entry22_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_14 k)) := by decide +kernel

theorem rowsSound22_14 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval11654 x
  · exact rowEval11655 x
  · exact rowEval11656 x
  · exact rowEval11657 x
  · exact rowEval11658 x
  · exact rowEval11659 x
  · exact rowEval11660 x
  · exact rowEval11661 x
  · exact rowEval11662 x
  · exact rowEval11663 x
  · exact rowEval11664 x
  · exact rowEval11665 x
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

theorem entryEval22_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_14 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck22_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_14]

theorem entryCheck22_16 : entry22_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_16 k)) := by decide +kernel

theorem rowsSound22_16 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval11678 x
  · exact rowEval11679 x
  · exact rowEval11680 x
  · exact rowEval11681 x
  · exact rowEval11682 x
  · exact rowEval11683 x
  · exact rowEval11684 x
  · exact rowEval11685 x
  · exact rowEval11686 x
  · exact rowEval11687 x
  · exact rowEval11688 x
  · exact rowEval11689 x
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

theorem entryEval22_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_16 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck22_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_16]

theorem entryCheck22_19 : entry22_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_19 k)) := by decide +kernel

theorem rowsSound22_19 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval11714 x
  · exact rowEval11715 x
  · exact rowEval11716 x
  · exact rowEval11717 x
  · exact rowEval11718 x
  · exact rowEval11719 x
  · exact rowEval11720 x
  · exact rowEval11721 x
  · exact rowEval11722 x
  · exact rowEval11723 x
  · exact rowEval11724 x
  · exact rowEval11725 x
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

theorem entryEval22_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_19 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck22_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_19]

theorem entryCheck22_20 : entry22_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_20 k)) := by decide +kernel

theorem rowsSound22_20 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval11726 x
  · exact rowEval11727 x
  · exact rowEval11728 x
  · exact rowEval11729 x
  · exact rowEval11730 x
  · exact rowEval11731 x
  · exact rowEval11732 x
  · exact rowEval11733 x
  · exact rowEval11734 x
  · exact rowEval11735 x
  · exact rowEval11736 x
  · exact rowEval11737 x
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

theorem entryEval22_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_20 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck22_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_20]

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

theorem rawRowCheck12316 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form22 = rawRow12316 := by decide +kernel

theorem rowCheck12316 : row12316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12316 := by decide +kernel

theorem rowEval12316 (x : Key → ℝ) : Integer.Sparse.eval row12316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12316, Integer.Sparse.eval_collectBalanced, rawRowCheck12316]

theorem rawRowCheck12317 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form22 = rawRow12317 := by decide +kernel

theorem rowCheck12317 : row12317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12317 := by decide +kernel

theorem rowEval12317 (x : Key → ℝ) : Integer.Sparse.eval row12317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12317, Integer.Sparse.eval_collectBalanced, rawRowCheck12317]

theorem rawRowCheck12318 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form22 = rawRow12318 := by decide +kernel

theorem rowCheck12318 : row12318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12318 := by decide +kernel

theorem rowEval12318 (x : Key → ℝ) : Integer.Sparse.eval row12318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12318, Integer.Sparse.eval_collectBalanced, rawRowCheck12318]

theorem rawRowCheck12319 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form22 = rawRow12319 := by decide +kernel

theorem rowCheck12319 : row12319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12319 := by decide +kernel

theorem rowEval12319 (x : Key → ℝ) : Integer.Sparse.eval row12319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12319, Integer.Sparse.eval_collectBalanced, rawRowCheck12319]

theorem rawRowCheck12320 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form22 = rawRow12320 := by decide +kernel

theorem rowCheck12320 : row12320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12320 := by decide +kernel

theorem rowEval12320 (x : Key → ℝ) : Integer.Sparse.eval row12320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck12320, Integer.Sparse.eval_collectBalanced, rawRowCheck12320]

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

theorem entryCheck24_22 : entry24_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_22 k)) := by decide +kernel

theorem rowsSound24_22 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval12316 x
  · exact rowEval12317 x
  · exact rowEval12318 x
  · exact rowEval12319 x
  · exact rowEval12320 x

theorem entryEval24_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_22 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck24_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_22]

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

theorem rawRowCheck12507 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form22 = rawRow12507 := by decide +kernel

theorem rowCheck12507 : row12507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12507 := by decide +kernel

theorem rowEval12507 (x : Key → ℝ) : Integer.Sparse.eval row12507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12507, Integer.Sparse.eval_collectBalanced, rawRowCheck12507]

theorem rawRowCheck12508 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form22 = rawRow12508 := by decide +kernel

theorem rowCheck12508 : row12508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12508 := by decide +kernel

theorem rowEval12508 (x : Key → ℝ) : Integer.Sparse.eval row12508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12508, Integer.Sparse.eval_collectBalanced, rawRowCheck12508]

theorem rawRowCheck12509 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form22 = rawRow12509 := by decide +kernel

theorem rowCheck12509 : row12509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12509 := by decide +kernel

theorem rowEval12509 (x : Key → ℝ) : Integer.Sparse.eval row12509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12509, Integer.Sparse.eval_collectBalanced, rawRowCheck12509]

theorem rawRowCheck12510 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form22 = rawRow12510 := by decide +kernel

theorem rowCheck12510 : row12510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12510 := by decide +kernel

theorem rowEval12510 (x : Key → ℝ) : Integer.Sparse.eval row12510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12510, Integer.Sparse.eval_collectBalanced, rawRowCheck12510]

theorem rawRowCheck12511 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form22 = rawRow12511 := by decide +kernel

theorem rowCheck12511 : row12511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12511 := by decide +kernel

theorem rowEval12511 (x : Key → ℝ) : Integer.Sparse.eval row12511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12511, Integer.Sparse.eval_collectBalanced, rawRowCheck12511]

theorem rawRowCheck12512 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form22 = rawRow12512 := by decide +kernel

theorem rowCheck12512 : row12512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12512 := by decide +kernel

theorem rowEval12512 (x : Key → ℝ) : Integer.Sparse.eval row12512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12512, Integer.Sparse.eval_collectBalanced, rawRowCheck12512]

theorem rawRowCheck12513 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form22 = rawRow12513 := by decide +kernel

theorem rowCheck12513 : row12513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12513 := by decide +kernel

theorem rowEval12513 (x : Key → ℝ) : Integer.Sparse.eval row12513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12513, Integer.Sparse.eval_collectBalanced, rawRowCheck12513]

theorem rawRowCheck12514 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form22 = rawRow12514 := by decide +kernel

theorem rowCheck12514 : row12514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12514 := by decide +kernel

theorem rowEval12514 (x : Key → ℝ) : Integer.Sparse.eval row12514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12514, Integer.Sparse.eval_collectBalanced, rawRowCheck12514]

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

theorem entryCheck25_22 : entry25_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_22 k)) := by decide +kernel

theorem rowsSound25_22 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval12507 x
  · exact rowEval12508 x
  · exact rowEval12509 x
  · exact rowEval12510 x
  · exact rowEval12511 x
  · exact rowEval12512 x
  · exact rowEval12513 x
  · exact rowEval12514 x

theorem entryEval25_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_22 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck25_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_22]

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

theorem entryEvalRow22_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 22 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 22).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval22_0_e B hB
  · exact entryEval22_1_e B hB
  · exact entryEval22_2_e B hB
  · exact entryEval22_3_e B hB
  · exact entryEval22_4_e B hB
  · exact entryEval22_5_e B hB
  · exact entryEval22_6 B hB
  · exact entryEval22_7_e B hB
  · exact entryEval22_8_e B hB
  · exact entryEval22_9_e B hB
  · exact entryEval22_10_e B hB
  · exact entryEval22_11_e B hB
  · exact entryEval22_12 B hB
  · exact entryEval22_13_e B hB
  · exact entryEval22_14 B hB
  · exact entryEval22_15_e B hB
  · exact entryEval22_16 B hB
  · exact entryEval22_17_e B hB
  · exact entryEval22_18_e B hB
  · exact entryEval22_19 B hB
  · exact entryEval22_20 B hB
  · exact entryEval22_21_e B hB
  · exact entryEval22_22_e B hB
  · exact (entryEval23_22_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_22 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_22 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_22_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e_oai
