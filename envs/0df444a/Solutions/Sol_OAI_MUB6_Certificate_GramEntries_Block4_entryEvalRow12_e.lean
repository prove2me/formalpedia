-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:44:56.059832+00:00
-- url     : https://prove2.me/submissions/2e895962-6e6b-4daf-a365-ea17ec209b8b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E034
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval12_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval17_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval18_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_12_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13190 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13190 := by decide +kernel

theorem rowCheck13190 : row13190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13190 := by decide +kernel

theorem rowEval13190 (x : Key → ℝ) : Integer.Sparse.eval row13190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13190, Integer.Sparse.eval_collectBalanced, rawRowCheck13190]

theorem rawRowCheck13191 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13191 := by decide +kernel

theorem rowCheck13191 : row13191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13191 := by decide +kernel

theorem rowEval13191 (x : Key → ℝ) : Integer.Sparse.eval row13191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13191, Integer.Sparse.eval_collectBalanced, rawRowCheck13191]

theorem rawRowCheck13192 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13192 := by decide +kernel

theorem rowCheck13192 : row13192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13192 := by decide +kernel

theorem rowEval13192 (x : Key → ℝ) : Integer.Sparse.eval row13192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13192, Integer.Sparse.eval_collectBalanced, rawRowCheck13192]

theorem rawRowCheck13193 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13193 := by decide +kernel

theorem rowCheck13193 : row13193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13193 := by decide +kernel

theorem rowEval13193 (x : Key → ℝ) : Integer.Sparse.eval row13193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13193, Integer.Sparse.eval_collectBalanced, rawRowCheck13193]

theorem rawRowCheck13194 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13194 := by decide +kernel

theorem rowCheck13194 : row13194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13194 := by decide +kernel

theorem rowEval13194 (x : Key → ℝ) : Integer.Sparse.eval row13194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13194, Integer.Sparse.eval_collectBalanced, rawRowCheck13194]

theorem rawRowCheck13195 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13195 := by decide +kernel

theorem rowCheck13195 : row13195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13195 := by decide +kernel

theorem rowEval13195 (x : Key → ℝ) : Integer.Sparse.eval row13195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13195, Integer.Sparse.eval_collectBalanced, rawRowCheck13195]

theorem rawRowCheck13196 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13196 := by decide +kernel

theorem rowCheck13196 : row13196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13196 := by decide +kernel

theorem rowEval13196 (x : Key → ℝ) : Integer.Sparse.eval row13196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13196, Integer.Sparse.eval_collectBalanced, rawRowCheck13196]

theorem rawRowCheck13197 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13197 := by decide +kernel

theorem rowCheck13197 : row13197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13197 := by decide +kernel

theorem rowEval13197 (x : Key → ℝ) : Integer.Sparse.eval row13197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13197, Integer.Sparse.eval_collectBalanced, rawRowCheck13197]

theorem rawRowCheck13198 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13198 := by decide +kernel

theorem rowCheck13198 : row13198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13198 := by decide +kernel

theorem rowEval13198 (x : Key → ℝ) : Integer.Sparse.eval row13198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13198, Integer.Sparse.eval_collectBalanced, rawRowCheck13198]

theorem rawRowCheck13199 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13199 := by decide +kernel

theorem rowCheck13199 : row13199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13199 := by decide +kernel

theorem rowEval13199 (x : Key → ℝ) : Integer.Sparse.eval row13199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13199, Integer.Sparse.eval_collectBalanced, rawRowCheck13199]

theorem rawRowCheck13200 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13200 := by decide +kernel

theorem rowCheck13200 : row13200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13200 := by decide +kernel

theorem rowEval13200 (x : Key → ℝ) : Integer.Sparse.eval row13200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13200, Integer.Sparse.eval_collectBalanced, rawRowCheck13200]

theorem rawRowCheck13201 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13201 := by decide +kernel

theorem rowCheck13201 : row13201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13201 := by decide +kernel

theorem rowEval13201 (x : Key → ℝ) : Integer.Sparse.eval row13201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13201, Integer.Sparse.eval_collectBalanced, rawRowCheck13201]

theorem rawRowCheck13202 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13202 := by decide +kernel

theorem rowCheck13202 : row13202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13202 := by decide +kernel

theorem rowEval13202 (x : Key → ℝ) : Integer.Sparse.eval row13202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13202, Integer.Sparse.eval_collectBalanced, rawRowCheck13202]

theorem rawRowCheck13203 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13203 := by decide +kernel

theorem rowCheck13203 : row13203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13203 := by decide +kernel

theorem rowEval13203 (x : Key → ℝ) : Integer.Sparse.eval row13203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13203, Integer.Sparse.eval_collectBalanced, rawRowCheck13203]

theorem rawRowCheck13204 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13204 := by decide +kernel

theorem rowCheck13204 : row13204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13204 := by decide +kernel

theorem rowEval13204 (x : Key → ℝ) : Integer.Sparse.eval row13204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13204, Integer.Sparse.eval_collectBalanced, rawRowCheck13204]

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

theorem rawRowCheck14841 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form0 = rawRow14841 := by decide +kernel

theorem rowCheck14841 : row14841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14841 := by decide +kernel

theorem rowEval14841 (x : Key → ℝ) : Integer.Sparse.eval row14841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14841, Integer.Sparse.eval_collectBalanced, rawRowCheck14841]

theorem rawRowCheck14842 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form0 = rawRow14842 := by decide +kernel

theorem rowCheck14842 : row14842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14842 := by decide +kernel

theorem rowEval14842 (x : Key → ℝ) : Integer.Sparse.eval row14842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14842, Integer.Sparse.eval_collectBalanced, rawRowCheck14842]

theorem rawRowCheck14843 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form0 = rawRow14843 := by decide +kernel

theorem rowCheck14843 : row14843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14843 := by decide +kernel

theorem rowEval14843 (x : Key → ℝ) : Integer.Sparse.eval row14843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14843, Integer.Sparse.eval_collectBalanced, rawRowCheck14843]

theorem rawRowCheck14844 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form0 = rawRow14844 := by decide +kernel

theorem rowCheck14844 : row14844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14844 := by decide +kernel

theorem rowEval14844 (x : Key → ℝ) : Integer.Sparse.eval row14844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14844, Integer.Sparse.eval_collectBalanced, rawRowCheck14844]

theorem rawRowCheck14845 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form0 = rawRow14845 := by decide +kernel

theorem rowCheck14845 : row14845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14845 := by decide +kernel

theorem rowEval14845 (x : Key → ℝ) : Integer.Sparse.eval row14845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14845, Integer.Sparse.eval_collectBalanced, rawRowCheck14845]

theorem rawRowCheck14846 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form0 = rawRow14846 := by decide +kernel

theorem rowCheck14846 : row14846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14846 := by decide +kernel

theorem rowEval14846 (x : Key → ℝ) : Integer.Sparse.eval row14846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14846, Integer.Sparse.eval_collectBalanced, rawRowCheck14846]

theorem rawRowCheck14847 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form0 = rawRow14847 := by decide +kernel

theorem rowCheck14847 : row14847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14847 := by decide +kernel

theorem rowEval14847 (x : Key → ℝ) : Integer.Sparse.eval row14847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14847, Integer.Sparse.eval_collectBalanced, rawRowCheck14847]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14848 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form0 = rawRow14848 := by decide +kernel

theorem rowCheck14848 : row14848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14848 := by decide +kernel

theorem rowEval14848 (x : Key → ℝ) : Integer.Sparse.eval row14848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14848, Integer.Sparse.eval_collectBalanced, rawRowCheck14848]

theorem rawRowCheck14849 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form0 = rawRow14849 := by decide +kernel

theorem rowCheck14849 : row14849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14849 := by decide +kernel

theorem rowEval14849 (x : Key → ℝ) : Integer.Sparse.eval row14849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14849, Integer.Sparse.eval_collectBalanced, rawRowCheck14849]

theorem rawRowCheck14850 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form0 = rawRow14850 := by decide +kernel

theorem rowCheck14850 : row14850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14850 := by decide +kernel

theorem rowEval14850 (x : Key → ℝ) : Integer.Sparse.eval row14850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14850, Integer.Sparse.eval_collectBalanced, rawRowCheck14850]

theorem rawRowCheck14851 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form0 = rawRow14851 := by decide +kernel

theorem rowCheck14851 : row14851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14851 := by decide +kernel

theorem rowEval14851 (x : Key → ℝ) : Integer.Sparse.eval row14851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14851, Integer.Sparse.eval_collectBalanced, rawRowCheck14851]

theorem rawRowCheck14852 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form0 = rawRow14852 := by decide +kernel

theorem rowCheck14852 : row14852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14852 := by decide +kernel

theorem rowEval14852 (x : Key → ℝ) : Integer.Sparse.eval row14852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14852, Integer.Sparse.eval_collectBalanced, rawRowCheck14852]

theorem rawRowCheck14934 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form4 = rawRow14934 := by decide +kernel

theorem rowCheck14934 : row14934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14934 := by decide +kernel

theorem rowEval14934 (x : Key → ℝ) : Integer.Sparse.eval row14934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14934, Integer.Sparse.eval_collectBalanced, rawRowCheck14934]

theorem rawRowCheck14935 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form4 = rawRow14935 := by decide +kernel

theorem rowCheck14935 : row14935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14935 := by decide +kernel

theorem rowEval14935 (x : Key → ℝ) : Integer.Sparse.eval row14935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14935, Integer.Sparse.eval_collectBalanced, rawRowCheck14935]

theorem rawRowCheck14936 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form4 = rawRow14936 := by decide +kernel

theorem rowCheck14936 : row14936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14936 := by decide +kernel

theorem rowEval14936 (x : Key → ℝ) : Integer.Sparse.eval row14936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14936, Integer.Sparse.eval_collectBalanced, rawRowCheck14936]

theorem rawRowCheck14937 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14937 := by decide +kernel

theorem rowCheck14937 : row14937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14937 := by decide +kernel

theorem rowEval14937 (x : Key → ℝ) : Integer.Sparse.eval row14937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14937, Integer.Sparse.eval_collectBalanced, rawRowCheck14937]

theorem rawRowCheck14938 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14938 := by decide +kernel

theorem rowCheck14938 : row14938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14938 := by decide +kernel

theorem rowEval14938 (x : Key → ℝ) : Integer.Sparse.eval row14938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14938, Integer.Sparse.eval_collectBalanced, rawRowCheck14938]

theorem rawRowCheck14939 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14939 := by decide +kernel

theorem rowCheck14939 : row14939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14939 := by decide +kernel

theorem rowEval14939 (x : Key → ℝ) : Integer.Sparse.eval row14939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14939, Integer.Sparse.eval_collectBalanced, rawRowCheck14939]

theorem rawRowCheck14940 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form4 = rawRow14940 := by decide +kernel

theorem rowCheck14940 : row14940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14940 := by decide +kernel

theorem rowEval14940 (x : Key → ℝ) : Integer.Sparse.eval row14940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14940, Integer.Sparse.eval_collectBalanced, rawRowCheck14940]

theorem rawRowCheck14941 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form4 = rawRow14941 := by decide +kernel

theorem rowCheck14941 : row14941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14941 := by decide +kernel

theorem rowEval14941 (x : Key → ℝ) : Integer.Sparse.eval row14941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14941, Integer.Sparse.eval_collectBalanced, rawRowCheck14941]

theorem rawRowCheck14942 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form4 = rawRow14942 := by decide +kernel

theorem rowCheck14942 : row14942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14942 := by decide +kernel

theorem rowEval14942 (x : Key → ℝ) : Integer.Sparse.eval row14942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14942, Integer.Sparse.eval_collectBalanced, rawRowCheck14942]

theorem rawRowCheck14943 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14943 := by decide +kernel

theorem rowCheck14943 : row14943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14943 := by decide +kernel

theorem rowEval14943 (x : Key → ℝ) : Integer.Sparse.eval row14943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14943, Integer.Sparse.eval_collectBalanced, rawRowCheck14943]

theorem rawRowCheck14944 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14944 := by decide +kernel

theorem rowCheck14944 : row14944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14944 := by decide +kernel

theorem rowEval14944 (x : Key → ℝ) : Integer.Sparse.eval row14944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14944, Integer.Sparse.eval_collectBalanced, rawRowCheck14944]

theorem rawRowCheck14945 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14945 := by decide +kernel

theorem rowCheck14945 : row14945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14945 := by decide +kernel

theorem rowEval14945 (x : Key → ℝ) : Integer.Sparse.eval row14945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14945, Integer.Sparse.eval_collectBalanced, rawRowCheck14945]

theorem rawRowCheck14946 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14946 := by decide +kernel

theorem rowCheck14946 : row14946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14946 := by decide +kernel

theorem rowEval14946 (x : Key → ℝ) : Integer.Sparse.eval row14946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14946, Integer.Sparse.eval_collectBalanced, rawRowCheck14946]

theorem rawRowCheck14947 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14947 := by decide +kernel

theorem rowCheck14947 : row14947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14947 := by decide +kernel

theorem rowEval14947 (x : Key → ℝ) : Integer.Sparse.eval row14947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14947, Integer.Sparse.eval_collectBalanced, rawRowCheck14947]

theorem rawRowCheck14948 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14948 := by decide +kernel

theorem rowCheck14948 : row14948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14948 := by decide +kernel

theorem rowEval14948 (x : Key → ℝ) : Integer.Sparse.eval row14948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14948, Integer.Sparse.eval_collectBalanced, rawRowCheck14948]

theorem rawRowCheck14949 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14949 := by decide +kernel

theorem rowCheck14949 : row14949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14949 := by decide +kernel

theorem rowEval14949 (x : Key → ℝ) : Integer.Sparse.eval row14949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14949, Integer.Sparse.eval_collectBalanced, rawRowCheck14949]

theorem rawRowCheck14950 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14950 := by decide +kernel

theorem rowCheck14950 : row14950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14950 := by decide +kernel

theorem rowEval14950 (x : Key → ℝ) : Integer.Sparse.eval row14950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14950, Integer.Sparse.eval_collectBalanced, rawRowCheck14950]

theorem rawRowCheck14951 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14951 := by decide +kernel

theorem rowCheck14951 : row14951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14951 := by decide +kernel

theorem rowEval14951 (x : Key → ℝ) : Integer.Sparse.eval row14951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14951, Integer.Sparse.eval_collectBalanced, rawRowCheck14951]

theorem rawRowCheck14952 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14952 := by decide +kernel

theorem rowCheck14952 : row14952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14952 := by decide +kernel

theorem rowEval14952 (x : Key → ℝ) : Integer.Sparse.eval row14952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14952, Integer.Sparse.eval_collectBalanced, rawRowCheck14952]

theorem rawRowCheck14953 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14953 := by decide +kernel

theorem rowCheck14953 : row14953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14953 := by decide +kernel

theorem rowEval14953 (x : Key → ℝ) : Integer.Sparse.eval row14953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14953, Integer.Sparse.eval_collectBalanced, rawRowCheck14953]

theorem rawRowCheck14954 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14954 := by decide +kernel

theorem rowCheck14954 : row14954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14954 := by decide +kernel

theorem rowEval14954 (x : Key → ℝ) : Integer.Sparse.eval row14954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14954, Integer.Sparse.eval_collectBalanced, rawRowCheck14954]

theorem rawRowCheck14955 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14955 := by decide +kernel

theorem rowCheck14955 : row14955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14955 := by decide +kernel

theorem rowEval14955 (x : Key → ℝ) : Integer.Sparse.eval row14955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14955, Integer.Sparse.eval_collectBalanced, rawRowCheck14955]

theorem rawRowCheck14956 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14956 := by decide +kernel

theorem rowCheck14956 : row14956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14956 := by decide +kernel

theorem rowEval14956 (x : Key → ℝ) : Integer.Sparse.eval row14956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14956, Integer.Sparse.eval_collectBalanced, rawRowCheck14956]

theorem rawRowCheck14957 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14957 := by decide +kernel

theorem rowCheck14957 : row14957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14957 := by decide +kernel

theorem rowEval14957 (x : Key → ℝ) : Integer.Sparse.eval row14957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14957, Integer.Sparse.eval_collectBalanced, rawRowCheck14957]

theorem rawRowCheck14958 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14958 := by decide +kernel

theorem rowCheck14958 : row14958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14958 := by decide +kernel

theorem rowEval14958 (x : Key → ℝ) : Integer.Sparse.eval row14958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14958, Integer.Sparse.eval_collectBalanced, rawRowCheck14958]

theorem rawRowCheck14959 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14959 := by decide +kernel

theorem rowCheck14959 : row14959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14959 := by decide +kernel

theorem rowEval14959 (x : Key → ℝ) : Integer.Sparse.eval row14959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14959, Integer.Sparse.eval_collectBalanced, rawRowCheck14959]

theorem rawRowCheck14960 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14960 := by decide +kernel

theorem rowCheck14960 : row14960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14960 := by decide +kernel

theorem rowEval14960 (x : Key → ℝ) : Integer.Sparse.eval row14960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14960, Integer.Sparse.eval_collectBalanced, rawRowCheck14960]

theorem rawRowCheck14961 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form5 = rawRow14961 := by decide +kernel

theorem rowCheck14961 : row14961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14961 := by decide +kernel

theorem rowEval14961 (x : Key → ℝ) : Integer.Sparse.eval row14961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14961, Integer.Sparse.eval_collectBalanced, rawRowCheck14961]

theorem rawRowCheck14962 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form5 = rawRow14962 := by decide +kernel

theorem rowCheck14962 : row14962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14962 := by decide +kernel

theorem rowEval14962 (x : Key → ℝ) : Integer.Sparse.eval row14962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14962, Integer.Sparse.eval_collectBalanced, rawRowCheck14962]

theorem rawRowCheck14963 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form5 = rawRow14963 := by decide +kernel

theorem rowCheck14963 : row14963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14963 := by decide +kernel

theorem rowEval14963 (x : Key → ℝ) : Integer.Sparse.eval row14963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14963, Integer.Sparse.eval_collectBalanced, rawRowCheck14963]

theorem rawRowCheck14964 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14964 := by decide +kernel

theorem rowCheck14964 : row14964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14964 := by decide +kernel

theorem rowEval14964 (x : Key → ℝ) : Integer.Sparse.eval row14964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14964, Integer.Sparse.eval_collectBalanced, rawRowCheck14964]

theorem rawRowCheck14965 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14965 := by decide +kernel

theorem rowCheck14965 : row14965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14965 := by decide +kernel

theorem rowEval14965 (x : Key → ℝ) : Integer.Sparse.eval row14965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14965, Integer.Sparse.eval_collectBalanced, rawRowCheck14965]

theorem rawRowCheck14966 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14966 := by decide +kernel

theorem rowCheck14966 : row14966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14966 := by decide +kernel

theorem rowEval14966 (x : Key → ℝ) : Integer.Sparse.eval row14966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14966, Integer.Sparse.eval_collectBalanced, rawRowCheck14966]

theorem rawRowCheck14967 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form5 = rawRow14967 := by decide +kernel

theorem rowCheck14967 : row14967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14967 := by decide +kernel

theorem rowEval14967 (x : Key → ℝ) : Integer.Sparse.eval row14967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14967, Integer.Sparse.eval_collectBalanced, rawRowCheck14967]

theorem rawRowCheck14968 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form5 = rawRow14968 := by decide +kernel

theorem rowCheck14968 : row14968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14968 := by decide +kernel

theorem rowEval14968 (x : Key → ℝ) : Integer.Sparse.eval row14968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14968, Integer.Sparse.eval_collectBalanced, rawRowCheck14968]

theorem rawRowCheck14969 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form5 = rawRow14969 := by decide +kernel

theorem rowCheck14969 : row14969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14969 := by decide +kernel

theorem rowEval14969 (x : Key → ℝ) : Integer.Sparse.eval row14969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14969, Integer.Sparse.eval_collectBalanced, rawRowCheck14969]

theorem rawRowCheck14970 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14970 := by decide +kernel

theorem rowCheck14970 : row14970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14970 := by decide +kernel

theorem rowEval14970 (x : Key → ℝ) : Integer.Sparse.eval row14970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14970, Integer.Sparse.eval_collectBalanced, rawRowCheck14970]

theorem rawRowCheck14971 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14971 := by decide +kernel

theorem rowCheck14971 : row14971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14971 := by decide +kernel

theorem rowEval14971 (x : Key → ℝ) : Integer.Sparse.eval row14971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14971, Integer.Sparse.eval_collectBalanced, rawRowCheck14971]

theorem rawRowCheck14972 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14972 := by decide +kernel

theorem rowCheck14972 : row14972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14972 := by decide +kernel

theorem rowEval14972 (x : Key → ℝ) : Integer.Sparse.eval row14972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14972, Integer.Sparse.eval_collectBalanced, rawRowCheck14972]

theorem rawRowCheck14973 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14973 := by decide +kernel

theorem rowCheck14973 : row14973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14973 := by decide +kernel

theorem rowEval14973 (x : Key → ℝ) : Integer.Sparse.eval row14973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14973, Integer.Sparse.eval_collectBalanced, rawRowCheck14973]

theorem rawRowCheck14974 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14974 := by decide +kernel

theorem rowCheck14974 : row14974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14974 := by decide +kernel

theorem rowEval14974 (x : Key → ℝ) : Integer.Sparse.eval row14974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14974, Integer.Sparse.eval_collectBalanced, rawRowCheck14974]

theorem rawRowCheck14975 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14975 := by decide +kernel

theorem rowCheck14975 : row14975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14975 := by decide +kernel

theorem rowEval14975 (x : Key → ℝ) : Integer.Sparse.eval row14975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14975, Integer.Sparse.eval_collectBalanced, rawRowCheck14975]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck14976 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14976 := by decide +kernel

theorem rowCheck14976 : row14976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14976 := by decide +kernel

theorem rowEval14976 (x : Key → ℝ) : Integer.Sparse.eval row14976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14976, Integer.Sparse.eval_collectBalanced, rawRowCheck14976]

theorem rawRowCheck14977 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14977 := by decide +kernel

theorem rowCheck14977 : row14977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14977 := by decide +kernel

theorem rowEval14977 (x : Key → ℝ) : Integer.Sparse.eval row14977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14977, Integer.Sparse.eval_collectBalanced, rawRowCheck14977]

theorem rawRowCheck14978 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14978 := by decide +kernel

theorem rowCheck14978 : row14978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14978 := by decide +kernel

theorem rowEval14978 (x : Key → ℝ) : Integer.Sparse.eval row14978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14978, Integer.Sparse.eval_collectBalanced, rawRowCheck14978]

theorem rawRowCheck14979 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14979 := by decide +kernel

theorem rowCheck14979 : row14979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14979 := by decide +kernel

theorem rowEval14979 (x : Key → ℝ) : Integer.Sparse.eval row14979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14979, Integer.Sparse.eval_collectBalanced, rawRowCheck14979]

theorem rawRowCheck14980 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14980 := by decide +kernel

theorem rowCheck14980 : row14980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14980 := by decide +kernel

theorem rowEval14980 (x : Key → ℝ) : Integer.Sparse.eval row14980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14980, Integer.Sparse.eval_collectBalanced, rawRowCheck14980]

theorem rawRowCheck14981 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14981 := by decide +kernel

theorem rowCheck14981 : row14981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14981 := by decide +kernel

theorem rowEval14981 (x : Key → ℝ) : Integer.Sparse.eval row14981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14981, Integer.Sparse.eval_collectBalanced, rawRowCheck14981]

theorem rawRowCheck14982 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14982 := by decide +kernel

theorem rowCheck14982 : row14982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14982 := by decide +kernel

theorem rowEval14982 (x : Key → ℝ) : Integer.Sparse.eval row14982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14982, Integer.Sparse.eval_collectBalanced, rawRowCheck14982]

theorem rawRowCheck14983 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14983 := by decide +kernel

theorem rowCheck14983 : row14983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14983 := by decide +kernel

theorem rowEval14983 (x : Key → ℝ) : Integer.Sparse.eval row14983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14983, Integer.Sparse.eval_collectBalanced, rawRowCheck14983]

theorem rawRowCheck14984 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14984 := by decide +kernel

theorem rowCheck14984 : row14984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14984 := by decide +kernel

theorem rowEval14984 (x : Key → ℝ) : Integer.Sparse.eval row14984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14984, Integer.Sparse.eval_collectBalanced, rawRowCheck14984]

theorem rawRowCheck14985 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14985 := by decide +kernel

theorem rowCheck14985 : row14985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14985 := by decide +kernel

theorem rowEval14985 (x : Key → ℝ) : Integer.Sparse.eval row14985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14985, Integer.Sparse.eval_collectBalanced, rawRowCheck14985]

theorem rawRowCheck14986 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14986 := by decide +kernel

theorem rowCheck14986 : row14986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14986 := by decide +kernel

theorem rowEval14986 (x : Key → ℝ) : Integer.Sparse.eval row14986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14986, Integer.Sparse.eval_collectBalanced, rawRowCheck14986]

theorem rawRowCheck14987 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14987 := by decide +kernel

theorem rowCheck14987 : row14987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14987 := by decide +kernel

theorem rowEval14987 (x : Key → ℝ) : Integer.Sparse.eval row14987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14987, Integer.Sparse.eval_collectBalanced, rawRowCheck14987]

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

theorem entryCheck12_0 : entry12_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_0 k)) := by decide +kernel

theorem rowsSound12_0 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14841 x
  · exact rowEval14842 x
  · exact rowEval14843 x
  · exact rowEval14844 x
  · exact rowEval14845 x
  · exact rowEval14846 x
  · exact rowEval14847 x
  · exact rowEval14848 x
  · exact rowEval14849 x
  · exact rowEval13190 x
  · exact rowEval13191 x
  · exact rowEval13192 x
  · exact rowEval13193 x
  · exact rowEval13194 x
  · exact rowEval13195 x
  · exact rowEval14850 x
  · exact rowEval14851 x
  · exact rowEval14852 x
  · exact rowEval13196 x
  · exact rowEval13197 x
  · exact rowEval13198 x
  · exact rowEval13199 x
  · exact rowEval13200 x
  · exact rowEval13201 x
  · exact rowEval13202 x
  · exact rowEval13203 x
  · exact rowEval13204 x

theorem entryEval12_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_0 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck12_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_0]

theorem entryCheck12_4 : entry12_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_4 k)) := by decide +kernel

theorem rowsSound12_4 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14934 x
  · exact rowEval14935 x
  · exact rowEval14936 x
  · exact rowEval14937 x
  · exact rowEval14938 x
  · exact rowEval14939 x
  · exact rowEval14940 x
  · exact rowEval14941 x
  · exact rowEval14942 x
  · exact rowEval14943 x
  · exact rowEval14944 x
  · exact rowEval14945 x
  · exact rowEval14946 x
  · exact rowEval14947 x
  · exact rowEval14948 x
  · exact rowEval14949 x
  · exact rowEval14950 x
  · exact rowEval14951 x
  · exact rowEval14952 x
  · exact rowEval14953 x
  · exact rowEval14954 x
  · exact rowEval14955 x
  · exact rowEval14956 x
  · exact rowEval14957 x
  · exact rowEval14958 x
  · exact rowEval14959 x
  · exact rowEval14960 x

theorem entryEval12_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_4 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck12_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_4]

theorem entryCheck12_5 : entry12_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_5 k)) := by decide +kernel

theorem rowsSound12_5 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14961 x
  · exact rowEval14962 x
  · exact rowEval14963 x
  · exact rowEval14964 x
  · exact rowEval14965 x
  · exact rowEval14966 x
  · exact rowEval14967 x
  · exact rowEval14968 x
  · exact rowEval14969 x
  · exact rowEval14970 x
  · exact rowEval14971 x
  · exact rowEval14972 x
  · exact rowEval14973 x
  · exact rowEval14974 x
  · exact rowEval14975 x
  · exact rowEval14976 x
  · exact rowEval14977 x
  · exact rowEval14978 x
  · exact rowEval14979 x
  · exact rowEval14980 x
  · exact rowEval14981 x
  · exact rowEval14982 x
  · exact rowEval14983 x
  · exact rowEval14984 x
  · exact rowEval14985 x
  · exact rowEval14986 x
  · exact rowEval14987 x

theorem entryEval12_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_5 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck12_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_5]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17531 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form12 = rawRow17531 := by decide +kernel

theorem rowCheck17531 : row17531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17531 := by decide +kernel

theorem rowEval17531 (x : Key → ℝ) : Integer.Sparse.eval row17531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17531, Integer.Sparse.eval_collectBalanced, rawRowCheck17531]

theorem rawRowCheck17532 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form12 = rawRow17532 := by decide +kernel

theorem rowCheck17532 : row17532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17532 := by decide +kernel

theorem rowEval17532 (x : Key → ℝ) : Integer.Sparse.eval row17532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17532, Integer.Sparse.eval_collectBalanced, rawRowCheck17532]

theorem rawRowCheck17533 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form12 = rawRow17533 := by decide +kernel

theorem rowCheck17533 : row17533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17533 := by decide +kernel

theorem rowEval17533 (x : Key → ℝ) : Integer.Sparse.eval row17533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17533, Integer.Sparse.eval_collectBalanced, rawRowCheck17533]

theorem rawRowCheck17534 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form12 = rawRow17534 := by decide +kernel

theorem rowCheck17534 : row17534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17534 := by decide +kernel

theorem rowEval17534 (x : Key → ℝ) : Integer.Sparse.eval row17534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17534, Integer.Sparse.eval_collectBalanced, rawRowCheck17534]

theorem rawRowCheck17535 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form12 = rawRow17535 := by decide +kernel

theorem rowCheck17535 : row17535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17535 := by decide +kernel

theorem rowEval17535 (x : Key → ℝ) : Integer.Sparse.eval row17535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17535, Integer.Sparse.eval_collectBalanced, rawRowCheck17535]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17536 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form12 = rawRow17536 := by decide +kernel

theorem rowCheck17536 : row17536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17536 := by decide +kernel

theorem rowEval17536 (x : Key → ℝ) : Integer.Sparse.eval row17536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17536, Integer.Sparse.eval_collectBalanced, rawRowCheck17536]

theorem rawRowCheck17537 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form12 = rawRow17537 := by decide +kernel

theorem rowCheck17537 : row17537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17537 := by decide +kernel

theorem rowEval17537 (x : Key → ℝ) : Integer.Sparse.eval row17537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17537, Integer.Sparse.eval_collectBalanced, rawRowCheck17537]

theorem rawRowCheck17538 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form12 = rawRow17538 := by decide +kernel

theorem rowCheck17538 : row17538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17538 := by decide +kernel

theorem rowEval17538 (x : Key → ℝ) : Integer.Sparse.eval row17538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17538, Integer.Sparse.eval_collectBalanced, rawRowCheck17538]

theorem rawRowCheck17539 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form12 = rawRow17539 := by decide +kernel

theorem rowCheck17539 : row17539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17539 := by decide +kernel

theorem rowEval17539 (x : Key → ℝ) : Integer.Sparse.eval row17539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17539, Integer.Sparse.eval_collectBalanced, rawRowCheck17539]

theorem rawRowCheck17540 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form12 = rawRow17540 := by decide +kernel

theorem rowCheck17540 : row17540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17540 := by decide +kernel

theorem rowEval17540 (x : Key → ℝ) : Integer.Sparse.eval row17540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17540, Integer.Sparse.eval_collectBalanced, rawRowCheck17540]

end MUB6.Certificate.GramRows

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

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

theorem rowsSound19_12 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval17531 x
  · exact rowEval17532 x
  · exact rowEval17533 x
  · exact rowEval17534 x
  · exact rowEval17535 x
  · exact rowEval17536 x
  · exact rowEval17537 x
  · exact rowEval17538 x
  · exact rowEval17539 x
  · exact rowEval17540 x

theorem entryEval19_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_12 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck19_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_12]

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

theorem entryEvalRow12_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 12 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 12).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval12_0 B hB
  · exact entryEval12_1_e B hB
  · exact entryEval12_2_e B hB
  · exact entryEval12_3_e B hB
  · exact entryEval12_4 B hB
  · exact entryEval12_5 B hB
  · exact entryEval12_6_e B hB
  · exact entryEval12_7 B hB
  · exact entryEval12_8_e B hB
  · exact entryEval12_9 B hB
  · exact entryEval12_10_e B hB
  · exact entryEval12_11_e B hB
  · exact entryEval12_12_e B hB
  · exact (entryEval13_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e_oai
