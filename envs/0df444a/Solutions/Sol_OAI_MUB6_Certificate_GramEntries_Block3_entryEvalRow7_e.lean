-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:19:24.705727+00:00
-- url     : https://prove2.me/submissions/defced18-1930-4144-9316-849f160ae18f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E028
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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval7_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval8_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval9_7_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8597 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8597 := by decide +kernel

theorem rowCheck8597 : row8597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8597 := by decide +kernel

theorem rowEval8597 (x : Key → ℝ) : Integer.Sparse.eval row8597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8597, Integer.Sparse.eval_collectBalanced, rawRowCheck8597]

theorem rawRowCheck8598 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7 = rawRow8598 := by decide +kernel

theorem rowCheck8598 : row8598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8598 := by decide +kernel

theorem rowEval8598 (x : Key → ℝ) : Integer.Sparse.eval row8598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8598, Integer.Sparse.eval_collectBalanced, rawRowCheck8598]

theorem rawRowCheck8599 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7 = rawRow8599 := by decide +kernel

theorem rowCheck8599 : row8599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8599 := by decide +kernel

theorem rowEval8599 (x : Key → ℝ) : Integer.Sparse.eval row8599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8599, Integer.Sparse.eval_collectBalanced, rawRowCheck8599]

theorem rawRowCheck8600 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7 = rawRow8600 := by decide +kernel

theorem rowCheck8600 : row8600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8600 := by decide +kernel

theorem rowEval8600 (x : Key → ℝ) : Integer.Sparse.eval row8600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8600, Integer.Sparse.eval_collectBalanced, rawRowCheck8600]

theorem rawRowCheck8601 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow8601 := by decide +kernel

theorem rowCheck8601 : row8601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8601 := by decide +kernel

theorem rowEval8601 (x : Key → ℝ) : Integer.Sparse.eval row8601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8601, Integer.Sparse.eval_collectBalanced, rawRowCheck8601]

theorem rawRowCheck8602 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow8602 := by decide +kernel

theorem rowCheck8602 : row8602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8602 := by decide +kernel

theorem rowEval8602 (x : Key → ℝ) : Integer.Sparse.eval row8602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8602, Integer.Sparse.eval_collectBalanced, rawRowCheck8602]

theorem rawRowCheck8603 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow8603 := by decide +kernel

theorem rowCheck8603 : row8603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8603 := by decide +kernel

theorem rowEval8603 (x : Key → ℝ) : Integer.Sparse.eval row8603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8603, Integer.Sparse.eval_collectBalanced, rawRowCheck8603]

theorem rawRowCheck8604 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form7 = rawRow8604 := by decide +kernel

theorem rowCheck8604 : row8604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8604 := by decide +kernel

theorem rowEval8604 (x : Key → ℝ) : Integer.Sparse.eval row8604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8604, Integer.Sparse.eval_collectBalanced, rawRowCheck8604]

theorem rawRowCheck8605 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form7 = rawRow8605 := by decide +kernel

theorem rowCheck8605 : row8605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8605 := by decide +kernel

theorem rowEval8605 (x : Key → ℝ) : Integer.Sparse.eval row8605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8605, Integer.Sparse.eval_collectBalanced, rawRowCheck8605]

theorem rawRowCheck8606 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form7 = rawRow8606 := by decide +kernel

theorem rowCheck8606 : row8606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8606 := by decide +kernel

theorem rowEval8606 (x : Key → ℝ) : Integer.Sparse.eval row8606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8606, Integer.Sparse.eval_collectBalanced, rawRowCheck8606]

theorem rawRowCheck8607 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form7 = rawRow8607 := by decide +kernel

theorem rowCheck8607 : row8607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8607 := by decide +kernel

theorem rowEval8607 (x : Key → ℝ) : Integer.Sparse.eval row8607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8607, Integer.Sparse.eval_collectBalanced, rawRowCheck8607]

theorem rawRowCheck8608 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form7 = rawRow8608 := by decide +kernel

theorem rowCheck8608 : row8608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8608 := by decide +kernel

theorem rowEval8608 (x : Key → ℝ) : Integer.Sparse.eval row8608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8608, Integer.Sparse.eval_collectBalanced, rawRowCheck8608]

theorem rawRowCheck8609 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form7 = rawRow8609 := by decide +kernel

theorem rowCheck8609 : row8609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8609 := by decide +kernel

theorem rowEval8609 (x : Key → ℝ) : Integer.Sparse.eval row8609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8609, Integer.Sparse.eval_collectBalanced, rawRowCheck8609]

theorem rawRowCheck8610 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form7 = rawRow8610 := by decide +kernel

theorem rowCheck8610 : row8610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8610 := by decide +kernel

theorem rowEval8610 (x : Key → ℝ) : Integer.Sparse.eval row8610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8610, Integer.Sparse.eval_collectBalanced, rawRowCheck8610]

theorem rawRowCheck8611 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form7 = rawRow8611 := by decide +kernel

theorem rowCheck8611 : row8611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8611 := by decide +kernel

theorem rowEval8611 (x : Key → ℝ) : Integer.Sparse.eval row8611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8611, Integer.Sparse.eval_collectBalanced, rawRowCheck8611]

theorem rawRowCheck8612 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form7 = rawRow8612 := by decide +kernel

theorem rowCheck8612 : row8612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8612 := by decide +kernel

theorem rowEval8612 (x : Key → ℝ) : Integer.Sparse.eval row8612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8612, Integer.Sparse.eval_collectBalanced, rawRowCheck8612]

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

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8597 x
  · exact rowEval8598 x
  · exact rowEval8599 x
  · exact rowEval8600 x
  · exact rowEval8601 x
  · exact rowEval8602 x
  · exact rowEval8603 x
  · exact rowEval8604 x
  · exact rowEval8605 x
  · exact rowEval8606 x
  · exact rowEval8607 x
  · exact rowEval8608 x
  · exact rowEval8609 x
  · exact rowEval8610 x
  · exact rowEval8611 x
  · exact rowEval8612 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

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

theorem rawRowCheck8717 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form7 = rawRow8717 := by decide +kernel

theorem rowCheck8717 : row8717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8717 := by decide +kernel

theorem rowEval8717 (x : Key → ℝ) : Integer.Sparse.eval row8717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8717, Integer.Sparse.eval_collectBalanced, rawRowCheck8717]

theorem rawRowCheck8718 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form7 = rawRow8718 := by decide +kernel

theorem rowCheck8718 : row8718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8718 := by decide +kernel

theorem rowEval8718 (x : Key → ℝ) : Integer.Sparse.eval row8718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8718, Integer.Sparse.eval_collectBalanced, rawRowCheck8718]

theorem rawRowCheck8719 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form7 = rawRow8719 := by decide +kernel

theorem rowCheck8719 : row8719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8719 := by decide +kernel

theorem rowEval8719 (x : Key → ℝ) : Integer.Sparse.eval row8719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8719, Integer.Sparse.eval_collectBalanced, rawRowCheck8719]

theorem rawRowCheck8720 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8720 := by decide +kernel

theorem rowCheck8720 : row8720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8720 := by decide +kernel

theorem rowEval8720 (x : Key → ℝ) : Integer.Sparse.eval row8720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8720, Integer.Sparse.eval_collectBalanced, rawRowCheck8720]

theorem rawRowCheck8721 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8721 := by decide +kernel

theorem rowCheck8721 : row8721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8721 := by decide +kernel

theorem rowEval8721 (x : Key → ℝ) : Integer.Sparse.eval row8721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8721, Integer.Sparse.eval_collectBalanced, rawRowCheck8721]

theorem rawRowCheck8722 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form7 = rawRow8722 := by decide +kernel

theorem rowCheck8722 : row8722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8722 := by decide +kernel

theorem rowEval8722 (x : Key → ℝ) : Integer.Sparse.eval row8722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8722, Integer.Sparse.eval_collectBalanced, rawRowCheck8722]

theorem rawRowCheck8723 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form7 = rawRow8723 := by decide +kernel

theorem rowCheck8723 : row8723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8723 := by decide +kernel

theorem rowEval8723 (x : Key → ℝ) : Integer.Sparse.eval row8723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8723, Integer.Sparse.eval_collectBalanced, rawRowCheck8723]

theorem rawRowCheck8724 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form7 = rawRow8724 := by decide +kernel

theorem rowCheck8724 : row8724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8724 := by decide +kernel

theorem rowEval8724 (x : Key → ℝ) : Integer.Sparse.eval row8724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck8724, Integer.Sparse.eval_collectBalanced, rawRowCheck8724]

theorem rawRowCheck8793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8793 := by decide +kernel

theorem rowCheck8793 : row8793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8793 := by decide +kernel

theorem rowEval8793 (x : Key → ℝ) : Integer.Sparse.eval row8793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8793, Integer.Sparse.eval_collectBalanced, rawRowCheck8793]

theorem rawRowCheck8794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8794 := by decide +kernel

theorem rowCheck8794 : row8794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8794 := by decide +kernel

theorem rowEval8794 (x : Key → ℝ) : Integer.Sparse.eval row8794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8794, Integer.Sparse.eval_collectBalanced, rawRowCheck8794]

theorem rawRowCheck8795 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8795 := by decide +kernel

theorem rowCheck8795 : row8795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8795 := by decide +kernel

theorem rowEval8795 (x : Key → ℝ) : Integer.Sparse.eval row8795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8795, Integer.Sparse.eval_collectBalanced, rawRowCheck8795]

theorem rawRowCheck8796 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8796 := by decide +kernel

theorem rowCheck8796 : row8796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8796 := by decide +kernel

theorem rowEval8796 (x : Key → ℝ) : Integer.Sparse.eval row8796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8796, Integer.Sparse.eval_collectBalanced, rawRowCheck8796]

theorem rawRowCheck8797 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8797 := by decide +kernel

theorem rowCheck8797 : row8797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8797 := by decide +kernel

theorem rowEval8797 (x : Key → ℝ) : Integer.Sparse.eval row8797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8797, Integer.Sparse.eval_collectBalanced, rawRowCheck8797]

theorem rawRowCheck8798 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7 = rawRow8798 := by decide +kernel

theorem rowCheck8798 : row8798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8798 := by decide +kernel

theorem rowEval8798 (x : Key → ℝ) : Integer.Sparse.eval row8798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8798, Integer.Sparse.eval_collectBalanced, rawRowCheck8798]

theorem rawRowCheck8799 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7 = rawRow8799 := by decide +kernel

theorem rowCheck8799 : row8799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8799 := by decide +kernel

theorem rowEval8799 (x : Key → ℝ) : Integer.Sparse.eval row8799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8799, Integer.Sparse.eval_collectBalanced, rawRowCheck8799]

theorem rawRowCheck8800 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7 = rawRow8800 := by decide +kernel

theorem rowCheck8800 : row8800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8800 := by decide +kernel

theorem rowEval8800 (x : Key → ℝ) : Integer.Sparse.eval row8800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck8800, Integer.Sparse.eval_collectBalanced, rawRowCheck8800]

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

theorem entryCheck11_7 : entry11_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_7 k)) := by decide +kernel

theorem rowsSound11_7 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8717 x
  · exact rowEval8718 x
  · exact rowEval8719 x
  · exact rowEval8720 x
  · exact rowEval8721 x
  · exact rowEval8722 x
  · exact rowEval8723 x
  · exact rowEval8724 x

theorem entryEval11_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_7 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck11_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_7]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck7574 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7574 := by decide +kernel

theorem rowCheck7574 : row7574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7574 := by decide +kernel

theorem rowEval7574 (x : Key → ℝ) : Integer.Sparse.eval row7574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7574, Integer.Sparse.eval_collectBalanced, rawRowCheck7574]

theorem rawRowCheck7575 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7575 := by decide +kernel

theorem rowCheck7575 : row7575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7575 := by decide +kernel

theorem rowEval7575 (x : Key → ℝ) : Integer.Sparse.eval row7575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7575, Integer.Sparse.eval_collectBalanced, rawRowCheck7575]

theorem rawRowCheck7576 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7576 := by decide +kernel

theorem rowCheck7576 : row7576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7576 := by decide +kernel

theorem rowEval7576 (x : Key → ℝ) : Integer.Sparse.eval row7576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7576, Integer.Sparse.eval_collectBalanced, rawRowCheck7576]

theorem rawRowCheck7577 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form0 = rawRow7577 := by decide +kernel

theorem rowCheck7577 : row7577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7577 := by decide +kernel

theorem rowEval7577 (x : Key → ℝ) : Integer.Sparse.eval row7577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7577, Integer.Sparse.eval_collectBalanced, rawRowCheck7577]

theorem rawRowCheck7578 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form0 = rawRow7578 := by decide +kernel

theorem rowCheck7578 : row7578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7578 := by decide +kernel

theorem rowEval7578 (x : Key → ℝ) : Integer.Sparse.eval row7578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7578, Integer.Sparse.eval_collectBalanced, rawRowCheck7578]

theorem rawRowCheck7579 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form0 = rawRow7579 := by decide +kernel

theorem rowCheck7579 : row7579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7579 := by decide +kernel

theorem rowEval7579 (x : Key → ℝ) : Integer.Sparse.eval row7579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7579, Integer.Sparse.eval_collectBalanced, rawRowCheck7579]

theorem rawRowCheck7580 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form0 = rawRow7580 := by decide +kernel

theorem rowCheck7580 : row7580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7580 := by decide +kernel

theorem rowEval7580 (x : Key → ℝ) : Integer.Sparse.eval row7580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7580, Integer.Sparse.eval_collectBalanced, rawRowCheck7580]

theorem rawRowCheck7581 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form0 = rawRow7581 := by decide +kernel

theorem rowCheck7581 : row7581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7581 := by decide +kernel

theorem rowEval7581 (x : Key → ℝ) : Integer.Sparse.eval row7581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7581, Integer.Sparse.eval_collectBalanced, rawRowCheck7581]

theorem rawRowCheck7582 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form0 = rawRow7582 := by decide +kernel

theorem rowCheck7582 : row7582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7582 := by decide +kernel

theorem rowEval7582 (x : Key → ℝ) : Integer.Sparse.eval row7582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7582, Integer.Sparse.eval_collectBalanced, rawRowCheck7582]

theorem rawRowCheck7583 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7583 := by decide +kernel

theorem rowCheck7583 : row7583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7583 := by decide +kernel

theorem rowEval7583 (x : Key → ℝ) : Integer.Sparse.eval row7583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7583, Integer.Sparse.eval_collectBalanced, rawRowCheck7583]

theorem rawRowCheck7584 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7584 := by decide +kernel

theorem rowCheck7584 : row7584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7584 := by decide +kernel

theorem rowEval7584 (x : Key → ℝ) : Integer.Sparse.eval row7584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7584, Integer.Sparse.eval_collectBalanced, rawRowCheck7584]

theorem rawRowCheck7585 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7585 := by decide +kernel

theorem rowCheck7585 : row7585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7585 := by decide +kernel

theorem rowEval7585 (x : Key → ℝ) : Integer.Sparse.eval row7585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7585, Integer.Sparse.eval_collectBalanced, rawRowCheck7585]

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

theorem rawRowCheck8953 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8953 := by decide +kernel

theorem rowCheck8953 : row8953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8953 := by decide +kernel

theorem rowEval8953 (x : Key → ℝ) : Integer.Sparse.eval row8953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8953, Integer.Sparse.eval_collectBalanced, rawRowCheck8953]

theorem rawRowCheck8954 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8954 := by decide +kernel

theorem rowCheck8954 : row8954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8954 := by decide +kernel

theorem rowEval8954 (x : Key → ℝ) : Integer.Sparse.eval row8954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8954, Integer.Sparse.eval_collectBalanced, rawRowCheck8954]

theorem rawRowCheck8955 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8955 := by decide +kernel

theorem rowCheck8955 : row8955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8955 := by decide +kernel

theorem rowEval8955 (x : Key → ℝ) : Integer.Sparse.eval row8955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8955, Integer.Sparse.eval_collectBalanced, rawRowCheck8955]

theorem rawRowCheck8956 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8956 := by decide +kernel

theorem rowCheck8956 : row8956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8956 := by decide +kernel

theorem rowEval8956 (x : Key → ℝ) : Integer.Sparse.eval row8956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8956, Integer.Sparse.eval_collectBalanced, rawRowCheck8956]

theorem rawRowCheck8957 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8957 := by decide +kernel

theorem rowCheck8957 : row8957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8957 := by decide +kernel

theorem rowEval8957 (x : Key → ℝ) : Integer.Sparse.eval row8957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8957, Integer.Sparse.eval_collectBalanced, rawRowCheck8957]

theorem rawRowCheck8958 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8958 := by decide +kernel

theorem rowCheck8958 : row8958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8958 := by decide +kernel

theorem rowEval8958 (x : Key → ℝ) : Integer.Sparse.eval row8958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8958, Integer.Sparse.eval_collectBalanced, rawRowCheck8958]

theorem rawRowCheck8959 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8959 := by decide +kernel

theorem rowCheck8959 : row8959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8959 := by decide +kernel

theorem rowEval8959 (x : Key → ℝ) : Integer.Sparse.eval row8959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8959, Integer.Sparse.eval_collectBalanced, rawRowCheck8959]

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

theorem entryCheck12_7 : entry12_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_7 k)) := by decide +kernel

theorem rowsSound12_7 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8793 x
  · exact rowEval8794 x
  · exact rowEval8795 x
  · exact rowEval8796 x
  · exact rowEval8797 x
  · exact rowEval8798 x
  · exact rowEval8799 x
  · exact rowEval8800 x

theorem entryEval12_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_7 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck12_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_7]

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

theorem rawRowCheck8960 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form7 = rawRow8960 := by decide +kernel

theorem rowCheck8960 : row8960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8960 := by decide +kernel

theorem rowEval8960 (x : Key → ℝ) : Integer.Sparse.eval row8960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8960, Integer.Sparse.eval_collectBalanced, rawRowCheck8960]

theorem rawRowCheck8961 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form7 = rawRow8961 := by decide +kernel

theorem rowCheck8961 : row8961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8961 := by decide +kernel

theorem rowEval8961 (x : Key → ℝ) : Integer.Sparse.eval row8961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8961, Integer.Sparse.eval_collectBalanced, rawRowCheck8961]

theorem rawRowCheck8962 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form7 = rawRow8962 := by decide +kernel

theorem rowCheck8962 : row8962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8962 := by decide +kernel

theorem rowEval8962 (x : Key → ℝ) : Integer.Sparse.eval row8962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8962, Integer.Sparse.eval_collectBalanced, rawRowCheck8962]

theorem rawRowCheck8963 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form7 = rawRow8963 := by decide +kernel

theorem rowCheck8963 : row8963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8963 := by decide +kernel

theorem rowEval8963 (x : Key → ℝ) : Integer.Sparse.eval row8963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8963, Integer.Sparse.eval_collectBalanced, rawRowCheck8963]

theorem rawRowCheck8964 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form7 = rawRow8964 := by decide +kernel

theorem rowCheck8964 : row8964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8964 := by decide +kernel

theorem rowEval8964 (x : Key → ℝ) : Integer.Sparse.eval row8964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8964, Integer.Sparse.eval_collectBalanced, rawRowCheck8964]

theorem rawRowCheck8965 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form7 = rawRow8965 := by decide +kernel

theorem rowCheck8965 : row8965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8965 := by decide +kernel

theorem rowEval8965 (x : Key → ℝ) : Integer.Sparse.eval row8965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8965, Integer.Sparse.eval_collectBalanced, rawRowCheck8965]

theorem rawRowCheck8966 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow8966 := by decide +kernel

theorem rowCheck8966 : row8966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8966 := by decide +kernel

theorem rowEval8966 (x : Key → ℝ) : Integer.Sparse.eval row8966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8966, Integer.Sparse.eval_collectBalanced, rawRowCheck8966]

theorem rawRowCheck8967 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow8967 := by decide +kernel

theorem rowCheck8967 : row8967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8967 := by decide +kernel

theorem rowEval8967 (x : Key → ℝ) : Integer.Sparse.eval row8967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8967, Integer.Sparse.eval_collectBalanced, rawRowCheck8967]

theorem rawRowCheck8968 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow8968 := by decide +kernel

theorem rowCheck8968 : row8968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8968 := by decide +kernel

theorem rowEval8968 (x : Key → ℝ) : Integer.Sparse.eval row8968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8968, Integer.Sparse.eval_collectBalanced, rawRowCheck8968]

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

theorem entryCheck13_7 : entry13_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_7 k)) := by decide +kernel

theorem rowsSound13_7 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8953 x
  · exact rowEval8954 x
  · exact rowEval8955 x
  · exact rowEval8956 x
  · exact rowEval8957 x
  · exact rowEval8958 x
  · exact rowEval8959 x
  · exact rowEval8960 x
  · exact rowEval8961 x
  · exact rowEval8962 x
  · exact rowEval8963 x
  · exact rowEval8964 x
  · exact rowEval8965 x
  · exact rowEval8966 x
  · exact rowEval8967 x
  · exact rowEval8968 x

theorem entryEval13_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_7 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck13_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_7]

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

theorem rawRowCheck9109 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow9109 := by decide +kernel

theorem rowCheck9109 : row9109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9109 := by decide +kernel

theorem rowEval9109 (x : Key → ℝ) : Integer.Sparse.eval row9109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9109, Integer.Sparse.eval_collectBalanced, rawRowCheck9109]

theorem rawRowCheck9110 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow9110 := by decide +kernel

theorem rowCheck9110 : row9110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9110 := by decide +kernel

theorem rowEval9110 (x : Key → ℝ) : Integer.Sparse.eval row9110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9110, Integer.Sparse.eval_collectBalanced, rawRowCheck9110]

theorem rawRowCheck9111 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow9111 := by decide +kernel

theorem rowCheck9111 : row9111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9111 := by decide +kernel

theorem rowEval9111 (x : Key → ℝ) : Integer.Sparse.eval row9111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9111, Integer.Sparse.eval_collectBalanced, rawRowCheck9111]

theorem rawRowCheck9112 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9112 := by decide +kernel

theorem rowCheck9112 : row9112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9112 := by decide +kernel

theorem rowEval9112 (x : Key → ℝ) : Integer.Sparse.eval row9112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9112, Integer.Sparse.eval_collectBalanced, rawRowCheck9112]

theorem rawRowCheck9113 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9113 := by decide +kernel

theorem rowCheck9113 : row9113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9113 := by decide +kernel

theorem rowEval9113 (x : Key → ℝ) : Integer.Sparse.eval row9113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9113, Integer.Sparse.eval_collectBalanced, rawRowCheck9113]

theorem rawRowCheck9114 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7 = rawRow9114 := by decide +kernel

theorem rowCheck9114 : row9114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9114 := by decide +kernel

theorem rowEval9114 (x : Key → ℝ) : Integer.Sparse.eval row9114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9114, Integer.Sparse.eval_collectBalanced, rawRowCheck9114]

theorem rawRowCheck9115 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7 = rawRow9115 := by decide +kernel

theorem rowCheck9115 : row9115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9115 := by decide +kernel

theorem rowEval9115 (x : Key → ℝ) : Integer.Sparse.eval row9115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9115, Integer.Sparse.eval_collectBalanced, rawRowCheck9115]

theorem rawRowCheck9116 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7 = rawRow9116 := by decide +kernel

theorem rowCheck9116 : row9116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9116 := by decide +kernel

theorem rowEval9116 (x : Key → ℝ) : Integer.Sparse.eval row9116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9116, Integer.Sparse.eval_collectBalanced, rawRowCheck9116]

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

theorem entryCheck14_7 : entry14_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_7 k)) := by decide +kernel

theorem rowsSound14_7 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval9109 x
  · exact rowEval9110 x
  · exact rowEval9111 x
  · exact rowEval9112 x
  · exact rowEval9113 x
  · exact rowEval9114 x
  · exact rowEval9115 x
  · exact rowEval9116 x

theorem entryEval14_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_7 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck14_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_7]

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

theorem rawRowCheck9257 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form7 = rawRow9257 := by decide +kernel

theorem rowCheck9257 : row9257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9257 := by decide +kernel

theorem rowEval9257 (x : Key → ℝ) : Integer.Sparse.eval row9257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9257, Integer.Sparse.eval_collectBalanced, rawRowCheck9257]

theorem rawRowCheck9258 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form7 = rawRow9258 := by decide +kernel

theorem rowCheck9258 : row9258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9258 := by decide +kernel

theorem rowEval9258 (x : Key → ℝ) : Integer.Sparse.eval row9258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9258, Integer.Sparse.eval_collectBalanced, rawRowCheck9258]

theorem rawRowCheck9259 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form7 = rawRow9259 := by decide +kernel

theorem rowCheck9259 : row9259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9259 := by decide +kernel

theorem rowEval9259 (x : Key → ℝ) : Integer.Sparse.eval row9259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9259, Integer.Sparse.eval_collectBalanced, rawRowCheck9259]

theorem rawRowCheck9260 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form7 = rawRow9260 := by decide +kernel

theorem rowCheck9260 : row9260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9260 := by decide +kernel

theorem rowEval9260 (x : Key → ℝ) : Integer.Sparse.eval row9260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9260, Integer.Sparse.eval_collectBalanced, rawRowCheck9260]

theorem rawRowCheck9261 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form7 = rawRow9261 := by decide +kernel

theorem rowCheck9261 : row9261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9261 := by decide +kernel

theorem rowEval9261 (x : Key → ℝ) : Integer.Sparse.eval row9261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9261, Integer.Sparse.eval_collectBalanced, rawRowCheck9261]

theorem rawRowCheck9262 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form7 = rawRow9262 := by decide +kernel

theorem rowCheck9262 : row9262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9262 := by decide +kernel

theorem rowEval9262 (x : Key → ℝ) : Integer.Sparse.eval row9262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9262, Integer.Sparse.eval_collectBalanced, rawRowCheck9262]

theorem rawRowCheck9263 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form7 = rawRow9263 := by decide +kernel

theorem rowCheck9263 : row9263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9263 := by decide +kernel

theorem rowEval9263 (x : Key → ℝ) : Integer.Sparse.eval row9263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9263, Integer.Sparse.eval_collectBalanced, rawRowCheck9263]

theorem rawRowCheck9264 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form7 = rawRow9264 := by decide +kernel

theorem rowCheck9264 : row9264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9264 := by decide +kernel

theorem rowEval9264 (x : Key → ℝ) : Integer.Sparse.eval row9264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9264, Integer.Sparse.eval_collectBalanced, rawRowCheck9264]

theorem rawRowCheck9265 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form7 = rawRow9265 := by decide +kernel

theorem rowCheck9265 : row9265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9265 := by decide +kernel

theorem rowEval9265 (x : Key → ℝ) : Integer.Sparse.eval row9265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9265, Integer.Sparse.eval_collectBalanced, rawRowCheck9265]

theorem rawRowCheck9266 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form7 = rawRow9266 := by decide +kernel

theorem rowCheck9266 : row9266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9266 := by decide +kernel

theorem rowEval9266 (x : Key → ℝ) : Integer.Sparse.eval row9266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9266, Integer.Sparse.eval_collectBalanced, rawRowCheck9266]

theorem rawRowCheck9267 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form7 = rawRow9267 := by decide +kernel

theorem rowCheck9267 : row9267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9267 := by decide +kernel

theorem rowEval9267 (x : Key → ℝ) : Integer.Sparse.eval row9267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9267, Integer.Sparse.eval_collectBalanced, rawRowCheck9267]

theorem rawRowCheck9268 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form7 = rawRow9268 := by decide +kernel

theorem rowCheck9268 : row9268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9268 := by decide +kernel

theorem rowEval9268 (x : Key → ℝ) : Integer.Sparse.eval row9268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9268, Integer.Sparse.eval_collectBalanced, rawRowCheck9268]

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

theorem rawRowCheck9421 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9421 := by decide +kernel

theorem rowCheck9421 : row9421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9421 := by decide +kernel

theorem rowEval9421 (x : Key → ℝ) : Integer.Sparse.eval row9421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9421, Integer.Sparse.eval_collectBalanced, rawRowCheck9421]

theorem rawRowCheck9422 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form7 = rawRow9422 := by decide +kernel

theorem rowCheck9422 : row9422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9422 := by decide +kernel

theorem rowEval9422 (x : Key → ℝ) : Integer.Sparse.eval row9422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9422, Integer.Sparse.eval_collectBalanced, rawRowCheck9422]

theorem rawRowCheck9423 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form7 = rawRow9423 := by decide +kernel

theorem rowCheck9423 : row9423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9423 := by decide +kernel

theorem rowEval9423 (x : Key → ℝ) : Integer.Sparse.eval row9423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9423, Integer.Sparse.eval_collectBalanced, rawRowCheck9423]

theorem rawRowCheck9424 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form7 = rawRow9424 := by decide +kernel

theorem rowCheck9424 : row9424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9424 := by decide +kernel

theorem rowEval9424 (x : Key → ℝ) : Integer.Sparse.eval row9424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9424, Integer.Sparse.eval_collectBalanced, rawRowCheck9424]

theorem rawRowCheck9425 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9425 := by decide +kernel

theorem rowCheck9425 : row9425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9425 := by decide +kernel

theorem rowEval9425 (x : Key → ℝ) : Integer.Sparse.eval row9425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9425, Integer.Sparse.eval_collectBalanced, rawRowCheck9425]

theorem rawRowCheck9426 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7 = rawRow9426 := by decide +kernel

theorem rowCheck9426 : row9426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9426 := by decide +kernel

theorem rowEval9426 (x : Key → ℝ) : Integer.Sparse.eval row9426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9426, Integer.Sparse.eval_collectBalanced, rawRowCheck9426]

theorem rawRowCheck9427 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7 = rawRow9427 := by decide +kernel

theorem rowCheck9427 : row9427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9427 := by decide +kernel

theorem rowEval9427 (x : Key → ℝ) : Integer.Sparse.eval row9427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9427, Integer.Sparse.eval_collectBalanced, rawRowCheck9427]

theorem rawRowCheck9428 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7 = rawRow9428 := by decide +kernel

theorem rowCheck9428 : row9428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9428 := by decide +kernel

theorem rowEval9428 (x : Key → ℝ) : Integer.Sparse.eval row9428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9428, Integer.Sparse.eval_collectBalanced, rawRowCheck9428]

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

theorem entryCheck15_7 : entry15_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_7 k)) := by decide +kernel

theorem rowsSound15_7 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8717 x
  · exact rowEval8718 x
  · exact rowEval8719 x
  · exact rowEval8720 x
  · exact rowEval9257 x
  · exact rowEval9258 x
  · exact rowEval9259 x
  · exact rowEval9260 x
  · exact rowEval9261 x
  · exact rowEval9262 x
  · exact rowEval9263 x
  · exact rowEval9264 x
  · exact rowEval9265 x
  · exact rowEval9266 x
  · exact rowEval9267 x
  · exact rowEval9268 x

theorem entryEval15_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_7 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck15_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_7]

end MUB6.Certificate.GramEntries.Block3

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

theorem entryCheck16_7 : entry16_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_7 k)) := by decide +kernel

theorem rowsSound16_7 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval9421 x
  · exact rowEval9422 x
  · exact rowEval9423 x
  · exact rowEval9424 x
  · exact rowEval9425 x
  · exact rowEval9426 x
  · exact rowEval9427 x
  · exact rowEval9428 x

theorem entryEval16_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_7 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck16_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_7]

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

theorem rawRowCheck10459 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form7 = rawRow10459 := by decide +kernel

theorem rowCheck10459 : row10459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10459 := by decide +kernel

theorem rowEval10459 (x : Key → ℝ) : Integer.Sparse.eval row10459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10459, Integer.Sparse.eval_collectBalanced, rawRowCheck10459]

theorem rawRowCheck10460 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form7 = rawRow10460 := by decide +kernel

theorem rowCheck10460 : row10460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10460 := by decide +kernel

theorem rowEval10460 (x : Key → ℝ) : Integer.Sparse.eval row10460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10460, Integer.Sparse.eval_collectBalanced, rawRowCheck10460]

theorem rawRowCheck10461 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form7 = rawRow10461 := by decide +kernel

theorem rowCheck10461 : row10461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10461 := by decide +kernel

theorem rowEval10461 (x : Key → ℝ) : Integer.Sparse.eval row10461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10461, Integer.Sparse.eval_collectBalanced, rawRowCheck10461]

theorem rawRowCheck10462 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form7 = rawRow10462 := by decide +kernel

theorem rowCheck10462 : row10462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10462 := by decide +kernel

theorem rowEval10462 (x : Key → ℝ) : Integer.Sparse.eval row10462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10462, Integer.Sparse.eval_collectBalanced, rawRowCheck10462]

theorem rawRowCheck10463 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form7 = rawRow10463 := by decide +kernel

theorem rowCheck10463 : row10463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10463 := by decide +kernel

theorem rowEval10463 (x : Key → ℝ) : Integer.Sparse.eval row10463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10463, Integer.Sparse.eval_collectBalanced, rawRowCheck10463]

theorem rawRowCheck10464 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form7 = rawRow10464 := by decide +kernel

theorem rowCheck10464 : row10464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10464 := by decide +kernel

theorem rowEval10464 (x : Key → ℝ) : Integer.Sparse.eval row10464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10464, Integer.Sparse.eval_collectBalanced, rawRowCheck10464]

theorem rawRowCheck10465 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form7 = rawRow10465 := by decide +kernel

theorem rowCheck10465 : row10465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10465 := by decide +kernel

theorem rowEval10465 (x : Key → ℝ) : Integer.Sparse.eval row10465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10465, Integer.Sparse.eval_collectBalanced, rawRowCheck10465]

theorem rawRowCheck10466 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form7 = rawRow10466 := by decide +kernel

theorem rowCheck10466 : row10466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10466 := by decide +kernel

theorem rowEval10466 (x : Key → ℝ) : Integer.Sparse.eval row10466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10466, Integer.Sparse.eval_collectBalanced, rawRowCheck10466]

theorem rawRowCheck10467 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form7 = rawRow10467 := by decide +kernel

theorem rowCheck10467 : row10467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10467 := by decide +kernel

theorem rowEval10467 (x : Key → ℝ) : Integer.Sparse.eval row10467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10467, Integer.Sparse.eval_collectBalanced, rawRowCheck10467]

theorem rawRowCheck10468 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form7 = rawRow10468 := by decide +kernel

theorem rowCheck10468 : row10468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10468 := by decide +kernel

theorem rowEval10468 (x : Key → ℝ) : Integer.Sparse.eval row10468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10468, Integer.Sparse.eval_collectBalanced, rawRowCheck10468]

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

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval10459 x
  · exact rowEval10460 x
  · exact rowEval10461 x
  · exact rowEval10462 x
  · exact rowEval10463 x
  · exact rowEval10464 x
  · exact rowEval10465 x
  · exact rowEval10466 x
  · exact rowEval10467 x
  · exact rowEval10468 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

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

theorem rawRowCheck10624 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow10624 := by decide +kernel

theorem rowCheck10624 : row10624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10624 := by decide +kernel

theorem rowEval10624 (x : Key → ℝ) : Integer.Sparse.eval row10624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10624, Integer.Sparse.eval_collectBalanced, rawRowCheck10624]

theorem rawRowCheck10625 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow10625 := by decide +kernel

theorem rowCheck10625 : row10625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10625 := by decide +kernel

theorem rowEval10625 (x : Key → ℝ) : Integer.Sparse.eval row10625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10625, Integer.Sparse.eval_collectBalanced, rawRowCheck10625]

theorem rawRowCheck10626 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow10626 := by decide +kernel

theorem rowCheck10626 : row10626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10626 := by decide +kernel

theorem rowEval10626 (x : Key → ℝ) : Integer.Sparse.eval row10626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10626, Integer.Sparse.eval_collectBalanced, rawRowCheck10626]

theorem rawRowCheck10627 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow10627 := by decide +kernel

theorem rowCheck10627 : row10627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10627 := by decide +kernel

theorem rowEval10627 (x : Key → ℝ) : Integer.Sparse.eval row10627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10627, Integer.Sparse.eval_collectBalanced, rawRowCheck10627]

theorem rawRowCheck10628 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form7 = rawRow10628 := by decide +kernel

theorem rowCheck10628 : row10628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10628 := by decide +kernel

theorem rowEval10628 (x : Key → ℝ) : Integer.Sparse.eval row10628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10628, Integer.Sparse.eval_collectBalanced, rawRowCheck10628]

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

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval10624 x
  · exact rowEval10625 x
  · exact rowEval10626 x
  · exact rowEval10627 x
  · exact rowEval10628 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck12241 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form7 = rawRow12241 := by decide +kernel

theorem rowCheck12241 : row12241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12241 := by decide +kernel

theorem rowEval12241 (x : Key → ℝ) : Integer.Sparse.eval row12241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12241, Integer.Sparse.eval_collectBalanced, rawRowCheck12241]

theorem rawRowCheck12242 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow12242 := by decide +kernel

theorem rowCheck12242 : row12242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12242 := by decide +kernel

theorem rowEval12242 (x : Key → ℝ) : Integer.Sparse.eval row12242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12242, Integer.Sparse.eval_collectBalanced, rawRowCheck12242]

theorem rawRowCheck12243 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form7 = rawRow12243 := by decide +kernel

theorem rowCheck12243 : row12243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12243 := by decide +kernel

theorem rowEval12243 (x : Key → ℝ) : Integer.Sparse.eval row12243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12243, Integer.Sparse.eval_collectBalanced, rawRowCheck12243]

theorem rawRowCheck12244 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form7 = rawRow12244 := by decide +kernel

theorem rowCheck12244 : row12244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12244 := by decide +kernel

theorem rowEval12244 (x : Key → ℝ) : Integer.Sparse.eval row12244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12244, Integer.Sparse.eval_collectBalanced, rawRowCheck12244]

theorem rawRowCheck12245 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form7 = rawRow12245 := by decide +kernel

theorem rowCheck12245 : row12245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12245 := by decide +kernel

theorem rowEval12245 (x : Key → ℝ) : Integer.Sparse.eval row12245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12245, Integer.Sparse.eval_collectBalanced, rawRowCheck12245]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck12387 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form7 = rawRow12387 := by decide +kernel

theorem rowCheck12387 : row12387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12387 := by decide +kernel

theorem rowEval12387 (x : Key → ℝ) : Integer.Sparse.eval row12387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12387, Integer.Sparse.eval_collectBalanced, rawRowCheck12387]

theorem rawRowCheck12388 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form7 = rawRow12388 := by decide +kernel

theorem rowCheck12388 : row12388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12388 := by decide +kernel

theorem rowEval12388 (x : Key → ℝ) : Integer.Sparse.eval row12388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12388, Integer.Sparse.eval_collectBalanced, rawRowCheck12388]

theorem rawRowCheck12389 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form7 = rawRow12389 := by decide +kernel

theorem rowCheck12389 : row12389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12389 := by decide +kernel

theorem rowEval12389 (x : Key → ℝ) : Integer.Sparse.eval row12389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12389, Integer.Sparse.eval_collectBalanced, rawRowCheck12389]

theorem rawRowCheck12390 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form7 = rawRow12390 := by decide +kernel

theorem rowCheck12390 : row12390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12390 := by decide +kernel

theorem rowEval12390 (x : Key → ℝ) : Integer.Sparse.eval row12390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12390, Integer.Sparse.eval_collectBalanced, rawRowCheck12390]

theorem rawRowCheck12391 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form7 = rawRow12391 := by decide +kernel

theorem rowCheck12391 : row12391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12391 := by decide +kernel

theorem rowEval12391 (x : Key → ℝ) : Integer.Sparse.eval row12391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12391, Integer.Sparse.eval_collectBalanced, rawRowCheck12391]

theorem rawRowCheck12392 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form7 = rawRow12392 := by decide +kernel

theorem rowCheck12392 : row12392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12392 := by decide +kernel

theorem rowEval12392 (x : Key → ℝ) : Integer.Sparse.eval row12392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12392, Integer.Sparse.eval_collectBalanced, rawRowCheck12392]

theorem rawRowCheck12393 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form7 = rawRow12393 := by decide +kernel

theorem rowCheck12393 : row12393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12393 := by decide +kernel

theorem rowEval12393 (x : Key → ℝ) : Integer.Sparse.eval row12393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12393, Integer.Sparse.eval_collectBalanced, rawRowCheck12393]

theorem rawRowCheck12394 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form7 = rawRow12394 := by decide +kernel

theorem rowCheck12394 : row12394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12394 := by decide +kernel

theorem rowEval12394 (x : Key → ℝ) : Integer.Sparse.eval row12394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12394, Integer.Sparse.eval_collectBalanced, rawRowCheck12394]

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

theorem entryCheck24_7 : entry24_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_7 k)) := by decide +kernel

theorem rowsSound24_7 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval12241 x
  · exact rowEval12242 x
  · exact rowEval12243 x
  · exact rowEval12244 x
  · exact rowEval12245 x

theorem entryEval24_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_7 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck24_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_7]

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

theorem entryCheck25_7 : entry25_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_7 k)) := by decide +kernel

theorem rowsSound25_7 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval12387 x
  · exact rowEval12388 x
  · exact rowEval12389 x
  · exact rowEval12390 x
  · exact rowEval12391 x
  · exact rowEval12392 x
  · exact rowEval12393 x
  · exact rowEval12394 x

theorem entryEval25_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_7 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck25_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_7]

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

theorem rawRowCheck7718 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7718 := by decide +kernel

theorem rowCheck7718 : row7718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7718 := by decide +kernel

theorem rowEval7718 (x : Key → ℝ) : Integer.Sparse.eval row7718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7718, Integer.Sparse.eval_collectBalanced, rawRowCheck7718]

theorem rawRowCheck7719 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7719 := by decide +kernel

theorem rowCheck7719 : row7719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7719 := by decide +kernel

theorem rowEval7719 (x : Key → ℝ) : Integer.Sparse.eval row7719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7719, Integer.Sparse.eval_collectBalanced, rawRowCheck7719]

theorem rawRowCheck7720 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7720 := by decide +kernel

theorem rowCheck7720 : row7720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7720 := by decide +kernel

theorem rowEval7720 (x : Key → ℝ) : Integer.Sparse.eval row7720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7720, Integer.Sparse.eval_collectBalanced, rawRowCheck7720]

theorem rawRowCheck7721 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form4 = rawRow7721 := by decide +kernel

theorem rowCheck7721 : row7721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7721 := by decide +kernel

theorem rowEval7721 (x : Key → ℝ) : Integer.Sparse.eval row7721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7721, Integer.Sparse.eval_collectBalanced, rawRowCheck7721]

theorem rawRowCheck7722 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form4 = rawRow7722 := by decide +kernel

theorem rowCheck7722 : row7722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7722 := by decide +kernel

theorem rowEval7722 (x : Key → ℝ) : Integer.Sparse.eval row7722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7722, Integer.Sparse.eval_collectBalanced, rawRowCheck7722]

theorem rawRowCheck7723 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form4 = rawRow7723 := by decide +kernel

theorem rowCheck7723 : row7723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7723 := by decide +kernel

theorem rowEval7723 (x : Key → ℝ) : Integer.Sparse.eval row7723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7723, Integer.Sparse.eval_collectBalanced, rawRowCheck7723]

theorem rawRowCheck7724 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form4 = rawRow7724 := by decide +kernel

theorem rowCheck7724 : row7724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7724 := by decide +kernel

theorem rowEval7724 (x : Key → ℝ) : Integer.Sparse.eval row7724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7724, Integer.Sparse.eval_collectBalanced, rawRowCheck7724]

theorem rawRowCheck7725 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form4 = rawRow7725 := by decide +kernel

theorem rowCheck7725 : row7725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7725 := by decide +kernel

theorem rowEval7725 (x : Key → ℝ) : Integer.Sparse.eval row7725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7725, Integer.Sparse.eval_collectBalanced, rawRowCheck7725]

theorem rawRowCheck7726 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form4 = rawRow7726 := by decide +kernel

theorem rowCheck7726 : row7726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7726 := by decide +kernel

theorem rowEval7726 (x : Key → ℝ) : Integer.Sparse.eval row7726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7726, Integer.Sparse.eval_collectBalanced, rawRowCheck7726]

theorem rawRowCheck7727 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form4 = rawRow7727 := by decide +kernel

theorem rowCheck7727 : row7727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7727 := by decide +kernel

theorem rowEval7727 (x : Key → ℝ) : Integer.Sparse.eval row7727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7727, Integer.Sparse.eval_collectBalanced, rawRowCheck7727]

theorem rawRowCheck7728 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form4 = rawRow7728 := by decide +kernel

theorem rowCheck7728 : row7728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7728 := by decide +kernel

theorem rowEval7728 (x : Key → ℝ) : Integer.Sparse.eval row7728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7728, Integer.Sparse.eval_collectBalanced, rawRowCheck7728]

theorem rawRowCheck7729 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form4 = rawRow7729 := by decide +kernel

theorem rowCheck7729 : row7729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7729 := by decide +kernel

theorem rowEval7729 (x : Key → ℝ) : Integer.Sparse.eval row7729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7729, Integer.Sparse.eval_collectBalanced, rawRowCheck7729]

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

theorem rawRowCheck7825 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7825 := by decide +kernel

theorem rowCheck7825 : row7825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7825 := by decide +kernel

theorem rowEval7825 (x : Key → ℝ) : Integer.Sparse.eval row7825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7825, Integer.Sparse.eval_collectBalanced, rawRowCheck7825]

theorem rawRowCheck7826 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7826 := by decide +kernel

theorem rowCheck7826 : row7826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7826 := by decide +kernel

theorem rowEval7826 (x : Key → ℝ) : Integer.Sparse.eval row7826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7826, Integer.Sparse.eval_collectBalanced, rawRowCheck7826]

theorem rawRowCheck7827 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7827 := by decide +kernel

theorem rowCheck7827 : row7827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7827 := by decide +kernel

theorem rowEval7827 (x : Key → ℝ) : Integer.Sparse.eval row7827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7827, Integer.Sparse.eval_collectBalanced, rawRowCheck7827]

theorem rawRowCheck7828 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form0 = rawRow7828 := by decide +kernel

theorem rowCheck7828 : row7828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7828 := by decide +kernel

theorem rowEval7828 (x : Key → ℝ) : Integer.Sparse.eval row7828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7828, Integer.Sparse.eval_collectBalanced, rawRowCheck7828]

theorem rawRowCheck7829 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form0 = rawRow7829 := by decide +kernel

theorem rowCheck7829 : row7829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7829 := by decide +kernel

theorem rowEval7829 (x : Key → ℝ) : Integer.Sparse.eval row7829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7829, Integer.Sparse.eval_collectBalanced, rawRowCheck7829]

theorem rawRowCheck7830 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form0 = rawRow7830 := by decide +kernel

theorem rowCheck7830 : row7830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7830 := by decide +kernel

theorem rowEval7830 (x : Key → ℝ) : Integer.Sparse.eval row7830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7830, Integer.Sparse.eval_collectBalanced, rawRowCheck7830]

theorem rawRowCheck7831 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form0 = rawRow7831 := by decide +kernel

theorem rowCheck7831 : row7831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7831 := by decide +kernel

theorem rowEval7831 (x : Key → ℝ) : Integer.Sparse.eval row7831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7831, Integer.Sparse.eval_collectBalanced, rawRowCheck7831]

theorem rawRowCheck7832 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form0 = rawRow7832 := by decide +kernel

theorem rowCheck7832 : row7832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7832 := by decide +kernel

theorem rowEval7832 (x : Key → ℝ) : Integer.Sparse.eval row7832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7832, Integer.Sparse.eval_collectBalanced, rawRowCheck7832]

theorem rawRowCheck7833 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form0 = rawRow7833 := by decide +kernel

theorem rowCheck7833 : row7833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7833 := by decide +kernel

theorem rowEval7833 (x : Key → ℝ) : Integer.Sparse.eval row7833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7833, Integer.Sparse.eval_collectBalanced, rawRowCheck7833]

theorem rawRowCheck7834 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow7834 := by decide +kernel

theorem rowCheck7834 : row7834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7834 := by decide +kernel

theorem rowEval7834 (x : Key → ℝ) : Integer.Sparse.eval row7834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7834, Integer.Sparse.eval_collectBalanced, rawRowCheck7834]

theorem rawRowCheck7835 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow7835 := by decide +kernel

theorem rowCheck7835 : row7835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7835 := by decide +kernel

theorem rowEval7835 (x : Key → ℝ) : Integer.Sparse.eval row7835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7835, Integer.Sparse.eval_collectBalanced, rawRowCheck7835]

theorem rawRowCheck7836 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow7836 := by decide +kernel

theorem rowCheck7836 : row7836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7836 := by decide +kernel

theorem rowEval7836 (x : Key → ℝ) : Integer.Sparse.eval row7836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7836, Integer.Sparse.eval_collectBalanced, rawRowCheck7836]

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

theorem rawRowCheck7873 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7873 := by decide +kernel

theorem rowCheck7873 : row7873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7873 := by decide +kernel

theorem rowEval7873 (x : Key → ℝ) : Integer.Sparse.eval row7873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7873, Integer.Sparse.eval_collectBalanced, rawRowCheck7873]

theorem rawRowCheck7874 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7874 := by decide +kernel

theorem rowCheck7874 : row7874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7874 := by decide +kernel

theorem rowEval7874 (x : Key → ℝ) : Integer.Sparse.eval row7874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7874, Integer.Sparse.eval_collectBalanced, rawRowCheck7874]

theorem rawRowCheck7875 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7875 := by decide +kernel

theorem rowCheck7875 : row7875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7875 := by decide +kernel

theorem rowEval7875 (x : Key → ℝ) : Integer.Sparse.eval row7875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7875, Integer.Sparse.eval_collectBalanced, rawRowCheck7875]

theorem rawRowCheck7876 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form4 = rawRow7876 := by decide +kernel

theorem rowCheck7876 : row7876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7876 := by decide +kernel

theorem rowEval7876 (x : Key → ℝ) : Integer.Sparse.eval row7876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7876, Integer.Sparse.eval_collectBalanced, rawRowCheck7876]

theorem rawRowCheck7877 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form4 = rawRow7877 := by decide +kernel

theorem rowCheck7877 : row7877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7877 := by decide +kernel

theorem rowEval7877 (x : Key → ℝ) : Integer.Sparse.eval row7877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7877, Integer.Sparse.eval_collectBalanced, rawRowCheck7877]

theorem rawRowCheck7878 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form4 = rawRow7878 := by decide +kernel

theorem rowCheck7878 : row7878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7878 := by decide +kernel

theorem rowEval7878 (x : Key → ℝ) : Integer.Sparse.eval row7878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7878, Integer.Sparse.eval_collectBalanced, rawRowCheck7878]

theorem rawRowCheck7879 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form4 = rawRow7879 := by decide +kernel

theorem rowCheck7879 : row7879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7879 := by decide +kernel

theorem rowEval7879 (x : Key → ℝ) : Integer.Sparse.eval row7879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7879, Integer.Sparse.eval_collectBalanced, rawRowCheck7879]

theorem rawRowCheck7880 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form4 = rawRow7880 := by decide +kernel

theorem rowCheck7880 : row7880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7880 := by decide +kernel

theorem rowEval7880 (x : Key → ℝ) : Integer.Sparse.eval row7880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7880, Integer.Sparse.eval_collectBalanced, rawRowCheck7880]

theorem rawRowCheck7881 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form4 = rawRow7881 := by decide +kernel

theorem rowCheck7881 : row7881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7881 := by decide +kernel

theorem rowEval7881 (x : Key → ℝ) : Integer.Sparse.eval row7881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7881, Integer.Sparse.eval_collectBalanced, rawRowCheck7881]

theorem rawRowCheck7882 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow7882 := by decide +kernel

theorem rowCheck7882 : row7882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7882 := by decide +kernel

theorem rowEval7882 (x : Key → ℝ) : Integer.Sparse.eval row7882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7882, Integer.Sparse.eval_collectBalanced, rawRowCheck7882]

theorem rawRowCheck7883 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow7883 := by decide +kernel

theorem rowCheck7883 : row7883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7883 := by decide +kernel

theorem rowEval7883 (x : Key → ℝ) : Integer.Sparse.eval row7883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7883, Integer.Sparse.eval_collectBalanced, rawRowCheck7883]

theorem rawRowCheck7884 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow7884 := by decide +kernel

theorem rowCheck7884 : row7884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7884 := by decide +kernel

theorem rowEval7884 (x : Key → ℝ) : Integer.Sparse.eval row7884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7884, Integer.Sparse.eval_collectBalanced, rawRowCheck7884]

theorem rawRowCheck7897 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form6 = rawRow7897 := by decide +kernel

theorem rowCheck7897 : row7897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7897 := by decide +kernel

theorem rowEval7897 (x : Key → ℝ) : Integer.Sparse.eval row7897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7897, Integer.Sparse.eval_collectBalanced, rawRowCheck7897]

theorem rawRowCheck7898 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form6 = rawRow7898 := by decide +kernel

theorem rowCheck7898 : row7898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7898 := by decide +kernel

theorem rowEval7898 (x : Key → ℝ) : Integer.Sparse.eval row7898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7898, Integer.Sparse.eval_collectBalanced, rawRowCheck7898]

theorem rawRowCheck7899 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form6 = rawRow7899 := by decide +kernel

theorem rowCheck7899 : row7899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7899 := by decide +kernel

theorem rowEval7899 (x : Key → ℝ) : Integer.Sparse.eval row7899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7899, Integer.Sparse.eval_collectBalanced, rawRowCheck7899]

theorem rawRowCheck7900 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form6 = rawRow7900 := by decide +kernel

theorem rowCheck7900 : row7900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7900 := by decide +kernel

theorem rowEval7900 (x : Key → ℝ) : Integer.Sparse.eval row7900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7900, Integer.Sparse.eval_collectBalanced, rawRowCheck7900]

theorem rawRowCheck7901 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form6 = rawRow7901 := by decide +kernel

theorem rowCheck7901 : row7901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7901 := by decide +kernel

theorem rowEval7901 (x : Key → ℝ) : Integer.Sparse.eval row7901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7901, Integer.Sparse.eval_collectBalanced, rawRowCheck7901]

theorem rawRowCheck7902 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form6 = rawRow7902 := by decide +kernel

theorem rowCheck7902 : row7902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7902 := by decide +kernel

theorem rowEval7902 (x : Key → ℝ) : Integer.Sparse.eval row7902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7902, Integer.Sparse.eval_collectBalanced, rawRowCheck7902]

theorem rawRowCheck7903 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form6 = rawRow7903 := by decide +kernel

theorem rowCheck7903 : row7903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7903 := by decide +kernel

theorem rowEval7903 (x : Key → ℝ) : Integer.Sparse.eval row7903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck7903, Integer.Sparse.eval_collectBalanced, rawRowCheck7903]

theorem rawRowCheck7904 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form6 = rawRow7904 := by decide +kernel

theorem rowCheck7904 : row7904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7904 := by decide +kernel

theorem rowEval7904 (x : Key → ℝ) : Integer.Sparse.eval row7904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7904, Integer.Sparse.eval_collectBalanced, rawRowCheck7904]

theorem rawRowCheck7905 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form6 = rawRow7905 := by decide +kernel

theorem rowCheck7905 : row7905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7905 := by decide +kernel

theorem rowEval7905 (x : Key → ℝ) : Integer.Sparse.eval row7905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck7905, Integer.Sparse.eval_collectBalanced, rawRowCheck7905]

theorem rawRowCheck7906 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow7906 := by decide +kernel

theorem rowCheck7906 : row7906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7906 := by decide +kernel

theorem rowEval7906 (x : Key → ℝ) : Integer.Sparse.eval row7906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7906, Integer.Sparse.eval_collectBalanced, rawRowCheck7906]

theorem rawRowCheck7907 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow7907 := by decide +kernel

theorem rowCheck7907 : row7907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7907 := by decide +kernel

theorem rowEval7907 (x : Key → ℝ) : Integer.Sparse.eval row7907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7907, Integer.Sparse.eval_collectBalanced, rawRowCheck7907]

theorem rawRowCheck7908 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow7908 := by decide +kernel

theorem rowCheck7908 : row7908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7908 := by decide +kernel

theorem rowEval7908 (x : Key → ℝ) : Integer.Sparse.eval row7908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck7908, Integer.Sparse.eval_collectBalanced, rawRowCheck7908]

theorem rawRowCheck7909 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form6 = rawRow7909 := by decide +kernel

theorem rowCheck7909 : row7909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7909 := by decide +kernel

theorem rowEval7909 (x : Key → ℝ) : Integer.Sparse.eval row7909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7909, Integer.Sparse.eval_collectBalanced, rawRowCheck7909]

theorem rawRowCheck7910 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form6 = rawRow7910 := by decide +kernel

theorem rowCheck7910 : row7910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7910 := by decide +kernel

theorem rowEval7910 (x : Key → ℝ) : Integer.Sparse.eval row7910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7910, Integer.Sparse.eval_collectBalanced, rawRowCheck7910]

theorem rawRowCheck7911 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form6 = rawRow7911 := by decide +kernel

theorem rowCheck7911 : row7911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7911 := by decide +kernel

theorem rowEval7911 (x : Key → ℝ) : Integer.Sparse.eval row7911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7911, Integer.Sparse.eval_collectBalanced, rawRowCheck7911]

theorem rawRowCheck7912 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form6 = rawRow7912 := by decide +kernel

theorem rowCheck7912 : row7912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7912 := by decide +kernel

theorem rowEval7912 (x : Key → ℝ) : Integer.Sparse.eval row7912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7912, Integer.Sparse.eval_collectBalanced, rawRowCheck7912]

theorem rawRowCheck7913 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form6 = rawRow7913 := by decide +kernel

theorem rowCheck7913 : row7913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7913 := by decide +kernel

theorem rowEval7913 (x : Key → ℝ) : Integer.Sparse.eval row7913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7913, Integer.Sparse.eval_collectBalanced, rawRowCheck7913]

theorem rawRowCheck7914 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form6 = rawRow7914 := by decide +kernel

theorem rowCheck7914 : row7914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7914 := by decide +kernel

theorem rowEval7914 (x : Key → ℝ) : Integer.Sparse.eval row7914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7914, Integer.Sparse.eval_collectBalanced, rawRowCheck7914]

theorem rawRowCheck7915 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form6 = rawRow7915 := by decide +kernel

theorem rowCheck7915 : row7915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7915 := by decide +kernel

theorem rowEval7915 (x : Key → ℝ) : Integer.Sparse.eval row7915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7915, Integer.Sparse.eval_collectBalanced, rawRowCheck7915]

theorem rawRowCheck7916 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form6 = rawRow7916 := by decide +kernel

theorem rowCheck7916 : row7916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7916 := by decide +kernel

theorem rowEval7916 (x : Key → ℝ) : Integer.Sparse.eval row7916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7916, Integer.Sparse.eval_collectBalanced, rawRowCheck7916]

theorem rawRowCheck7917 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form6 = rawRow7917 := by decide +kernel

theorem rowCheck7917 : row7917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7917 := by decide +kernel

theorem rowEval7917 (x : Key → ℝ) : Integer.Sparse.eval row7917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7917, Integer.Sparse.eval_collectBalanced, rawRowCheck7917]

theorem rawRowCheck7918 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form6 = rawRow7918 := by decide +kernel

theorem rowCheck7918 : row7918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7918 := by decide +kernel

theorem rowEval7918 (x : Key → ℝ) : Integer.Sparse.eval row7918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7918, Integer.Sparse.eval_collectBalanced, rawRowCheck7918]

theorem rawRowCheck7919 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form6 = rawRow7919 := by decide +kernel

theorem rowCheck7919 : row7919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7919 := by decide +kernel

theorem rowEval7919 (x : Key → ℝ) : Integer.Sparse.eval row7919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7919, Integer.Sparse.eval_collectBalanced, rawRowCheck7919]

theorem rawRowCheck7920 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form6 = rawRow7920 := by decide +kernel

theorem rowCheck7920 : row7920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7920 := by decide +kernel

theorem rowEval7920 (x : Key → ℝ) : Integer.Sparse.eval row7920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7920, Integer.Sparse.eval_collectBalanced, rawRowCheck7920]

theorem rawRowCheck7921 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form7 = rawRow7921 := by decide +kernel

theorem rowCheck7921 : row7921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7921 := by decide +kernel

theorem rowEval7921 (x : Key → ℝ) : Integer.Sparse.eval row7921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7921, Integer.Sparse.eval_collectBalanced, rawRowCheck7921]

theorem rawRowCheck7922 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form7 = rawRow7922 := by decide +kernel

theorem rowCheck7922 : row7922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7922 := by decide +kernel

theorem rowEval7922 (x : Key → ℝ) : Integer.Sparse.eval row7922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7922, Integer.Sparse.eval_collectBalanced, rawRowCheck7922]

theorem rawRowCheck7923 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form7 = rawRow7923 := by decide +kernel

theorem rowCheck7923 : row7923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7923 := by decide +kernel

theorem rowEval7923 (x : Key → ℝ) : Integer.Sparse.eval row7923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7923, Integer.Sparse.eval_collectBalanced, rawRowCheck7923]

theorem rawRowCheck7924 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form7 = rawRow7924 := by decide +kernel

theorem rowCheck7924 : row7924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7924 := by decide +kernel

theorem rowEval7924 (x : Key → ℝ) : Integer.Sparse.eval row7924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7924, Integer.Sparse.eval_collectBalanced, rawRowCheck7924]

theorem rawRowCheck7925 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form7 = rawRow7925 := by decide +kernel

theorem rowCheck7925 : row7925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7925 := by decide +kernel

theorem rowEval7925 (x : Key → ℝ) : Integer.Sparse.eval row7925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7925, Integer.Sparse.eval_collectBalanced, rawRowCheck7925]

theorem rawRowCheck7926 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form7 = rawRow7926 := by decide +kernel

theorem rowCheck7926 : row7926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7926 := by decide +kernel

theorem rowEval7926 (x : Key → ℝ) : Integer.Sparse.eval row7926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7926, Integer.Sparse.eval_collectBalanced, rawRowCheck7926]

theorem rawRowCheck7927 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form7 = rawRow7927 := by decide +kernel

theorem rowCheck7927 : row7927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7927 := by decide +kernel

theorem rowEval7927 (x : Key → ℝ) : Integer.Sparse.eval row7927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck7927, Integer.Sparse.eval_collectBalanced, rawRowCheck7927]

theorem rawRowCheck7928 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form7 = rawRow7928 := by decide +kernel

theorem rowCheck7928 : row7928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7928 := by decide +kernel

theorem rowEval7928 (x : Key → ℝ) : Integer.Sparse.eval row7928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7928, Integer.Sparse.eval_collectBalanced, rawRowCheck7928]

theorem rawRowCheck7929 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form7 = rawRow7929 := by decide +kernel

theorem rowCheck7929 : row7929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7929 := by decide +kernel

theorem rowEval7929 (x : Key → ℝ) : Integer.Sparse.eval row7929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck7929, Integer.Sparse.eval_collectBalanced, rawRowCheck7929]

theorem rawRowCheck7930 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow7930 := by decide +kernel

theorem rowCheck7930 : row7930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7930 := by decide +kernel

theorem rowEval7930 (x : Key → ℝ) : Integer.Sparse.eval row7930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7930, Integer.Sparse.eval_collectBalanced, rawRowCheck7930]

theorem rawRowCheck7931 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow7931 := by decide +kernel

theorem rowCheck7931 : row7931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7931 := by decide +kernel

theorem rowEval7931 (x : Key → ℝ) : Integer.Sparse.eval row7931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7931, Integer.Sparse.eval_collectBalanced, rawRowCheck7931]

theorem rawRowCheck7932 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow7932 := by decide +kernel

theorem rowCheck7932 : row7932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7932 := by decide +kernel

theorem rowEval7932 (x : Key → ℝ) : Integer.Sparse.eval row7932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck7932, Integer.Sparse.eval_collectBalanced, rawRowCheck7932]

theorem rawRowCheck7933 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form7 = rawRow7933 := by decide +kernel

theorem rowCheck7933 : row7933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7933 := by decide +kernel

theorem rowEval7933 (x : Key → ℝ) : Integer.Sparse.eval row7933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7933, Integer.Sparse.eval_collectBalanced, rawRowCheck7933]

theorem rawRowCheck7934 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form7 = rawRow7934 := by decide +kernel

theorem rowCheck7934 : row7934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7934 := by decide +kernel

theorem rowEval7934 (x : Key → ℝ) : Integer.Sparse.eval row7934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7934, Integer.Sparse.eval_collectBalanced, rawRowCheck7934]

theorem rawRowCheck7935 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form7 = rawRow7935 := by decide +kernel

theorem rowCheck7935 : row7935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7935 := by decide +kernel

theorem rowEval7935 (x : Key → ℝ) : Integer.Sparse.eval row7935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7935, Integer.Sparse.eval_collectBalanced, rawRowCheck7935]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck7936 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form7 = rawRow7936 := by decide +kernel

theorem rowCheck7936 : row7936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7936 := by decide +kernel

theorem rowEval7936 (x : Key → ℝ) : Integer.Sparse.eval row7936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7936, Integer.Sparse.eval_collectBalanced, rawRowCheck7936]

theorem rawRowCheck7937 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form7 = rawRow7937 := by decide +kernel

theorem rowCheck7937 : row7937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7937 := by decide +kernel

theorem rowEval7937 (x : Key → ℝ) : Integer.Sparse.eval row7937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7937, Integer.Sparse.eval_collectBalanced, rawRowCheck7937]

theorem rawRowCheck7938 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form7 = rawRow7938 := by decide +kernel

theorem rowCheck7938 : row7938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7938 := by decide +kernel

theorem rowEval7938 (x : Key → ℝ) : Integer.Sparse.eval row7938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7938, Integer.Sparse.eval_collectBalanced, rawRowCheck7938]

theorem rawRowCheck7939 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form7 = rawRow7939 := by decide +kernel

theorem rowCheck7939 : row7939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7939 := by decide +kernel

theorem rowEval7939 (x : Key → ℝ) : Integer.Sparse.eval row7939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7939, Integer.Sparse.eval_collectBalanced, rawRowCheck7939]

theorem rawRowCheck7940 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form7 = rawRow7940 := by decide +kernel

theorem rowCheck7940 : row7940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7940 := by decide +kernel

theorem rowEval7940 (x : Key → ℝ) : Integer.Sparse.eval row7940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7940, Integer.Sparse.eval_collectBalanced, rawRowCheck7940]

theorem rawRowCheck7941 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form7 = rawRow7941 := by decide +kernel

theorem rowCheck7941 : row7941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7941 := by decide +kernel

theorem rowEval7941 (x : Key → ℝ) : Integer.Sparse.eval row7941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7941, Integer.Sparse.eval_collectBalanced, rawRowCheck7941]

theorem rawRowCheck7942 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form7 = rawRow7942 := by decide +kernel

theorem rowCheck7942 : row7942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7942 := by decide +kernel

theorem rowEval7942 (x : Key → ℝ) : Integer.Sparse.eval row7942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7942, Integer.Sparse.eval_collectBalanced, rawRowCheck7942]

theorem rawRowCheck7943 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form7 = rawRow7943 := by decide +kernel

theorem rowCheck7943 : row7943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7943 := by decide +kernel

theorem rowEval7943 (x : Key → ℝ) : Integer.Sparse.eval row7943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7943, Integer.Sparse.eval_collectBalanced, rawRowCheck7943]

theorem rawRowCheck7944 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form7 = rawRow7944 := by decide +kernel

theorem rowCheck7944 : row7944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7944 := by decide +kernel

theorem rowEval7944 (x : Key → ℝ) : Integer.Sparse.eval row7944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7944, Integer.Sparse.eval_collectBalanced, rawRowCheck7944]

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

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7825 x
  · exact rowEval7826 x
  · exact rowEval7827 x
  · exact rowEval7828 x
  · exact rowEval7829 x
  · exact rowEval7830 x
  · exact rowEval7831 x
  · exact rowEval7832 x
  · exact rowEval7833 x
  · exact rowEval7834 x
  · exact rowEval7835 x
  · exact rowEval7836 x
  · exact rowEval7574 x
  · exact rowEval7575 x
  · exact rowEval7576 x
  · exact rowEval7577 x
  · exact rowEval7578 x
  · exact rowEval7579 x
  · exact rowEval7580 x
  · exact rowEval7581 x
  · exact rowEval7582 x
  · exact rowEval7583 x
  · exact rowEval7584 x
  · exact rowEval7585 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

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

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7873 x
  · exact rowEval7874 x
  · exact rowEval7875 x
  · exact rowEval7876 x
  · exact rowEval7877 x
  · exact rowEval7878 x
  · exact rowEval7879 x
  · exact rowEval7880 x
  · exact rowEval7881 x
  · exact rowEval7882 x
  · exact rowEval7883 x
  · exact rowEval7884 x
  · exact rowEval7718 x
  · exact rowEval7719 x
  · exact rowEval7720 x
  · exact rowEval7721 x
  · exact rowEval7722 x
  · exact rowEval7723 x
  · exact rowEval7724 x
  · exact rowEval7725 x
  · exact rowEval7726 x
  · exact rowEval7727 x
  · exact rowEval7728 x
  · exact rowEval7729 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval7897 x
  · exact rowEval7898 x
  · exact rowEval7899 x
  · exact rowEval7900 x
  · exact rowEval7901 x
  · exact rowEval7902 x
  · exact rowEval7903 x
  · exact rowEval7904 x
  · exact rowEval7905 x
  · exact rowEval7906 x
  · exact rowEval7907 x
  · exact rowEval7908 x
  · exact rowEval7909 x
  · exact rowEval7910 x
  · exact rowEval7911 x
  · exact rowEval7912 x
  · exact rowEval7913 x
  · exact rowEval7914 x
  · exact rowEval7915 x
  · exact rowEval7916 x
  · exact rowEval7917 x
  · exact rowEval7918 x
  · exact rowEval7919 x
  · exact rowEval7920 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval7921 x
  · exact rowEval7922 x
  · exact rowEval7923 x
  · exact rowEval7924 x
  · exact rowEval7925 x
  · exact rowEval7926 x
  · exact rowEval7927 x
  · exact rowEval7928 x
  · exact rowEval7929 x
  · exact rowEval7930 x
  · exact rowEval7931 x
  · exact rowEval7932 x
  · exact rowEval7933 x
  · exact rowEval7934 x
  · exact rowEval7935 x
  · exact rowEval7936 x
  · exact rowEval7937 x
  · exact rowEval7938 x
  · exact rowEval7939 x
  · exact rowEval7940 x
  · exact rowEval7941 x
  · exact rowEval7942 x
  · exact rowEval7943 x
  · exact rowEval7944 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

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

theorem entryEvalRow7_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 7 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 7).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval7_0 B hB
  · exact entryEval7_1 B hB
  · exact entryEval7_2 B hB
  · exact entryEval7_3 B hB
  · exact entryEval7_4 B hB
  · exact entryEval7_5_e B hB
  · exact entryEval7_6 B hB
  · exact entryEval7_7 B hB
  · exact (entryEval8_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e_oai
