-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:26:01.145149+00:00
-- url     : https://prove2.me/submissions/f73b7f91-35d0-418d-9a5b-1fa2a359ca46

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E057
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_17_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9501 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form0 = rawRow9501 := by decide +kernel

theorem rowCheck9501 : row9501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9501 := by decide +kernel

theorem rowEval9501 (x : Key → ℝ) : Integer.Sparse.eval row9501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9501, Integer.Sparse.eval_collectBalanced, rawRowCheck9501]

theorem rawRowCheck9502 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form0 = rawRow9502 := by decide +kernel

theorem rowCheck9502 : row9502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9502 := by decide +kernel

theorem rowEval9502 (x : Key → ℝ) : Integer.Sparse.eval row9502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9502, Integer.Sparse.eval_collectBalanced, rawRowCheck9502]

theorem rawRowCheck9503 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form0 = rawRow9503 := by decide +kernel

theorem rowCheck9503 : row9503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9503 := by decide +kernel

theorem rowEval9503 (x : Key → ℝ) : Integer.Sparse.eval row9503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9503, Integer.Sparse.eval_collectBalanced, rawRowCheck9503]

theorem rawRowCheck9504 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form0 = rawRow9504 := by decide +kernel

theorem rowCheck9504 : row9504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9504 := by decide +kernel

theorem rowEval9504 (x : Key → ℝ) : Integer.Sparse.eval row9504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9504, Integer.Sparse.eval_collectBalanced, rawRowCheck9504]

theorem rawRowCheck9505 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form0 = rawRow9505 := by decide +kernel

theorem rowCheck9505 : row9505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9505 := by decide +kernel

theorem rowEval9505 (x : Key → ℝ) : Integer.Sparse.eval row9505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9505, Integer.Sparse.eval_collectBalanced, rawRowCheck9505]

theorem rawRowCheck9506 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form0 = rawRow9506 := by decide +kernel

theorem rowCheck9506 : row9506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9506 := by decide +kernel

theorem rowEval9506 (x : Key → ℝ) : Integer.Sparse.eval row9506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9506, Integer.Sparse.eval_collectBalanced, rawRowCheck9506]

theorem rawRowCheck9507 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form0 = rawRow9507 := by decide +kernel

theorem rowCheck9507 : row9507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9507 := by decide +kernel

theorem rowEval9507 (x : Key → ℝ) : Integer.Sparse.eval row9507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9507, Integer.Sparse.eval_collectBalanced, rawRowCheck9507]

theorem rawRowCheck9508 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form0 = rawRow9508 := by decide +kernel

theorem rowCheck9508 : row9508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9508 := by decide +kernel

theorem rowEval9508 (x : Key → ℝ) : Integer.Sparse.eval row9508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9508, Integer.Sparse.eval_collectBalanced, rawRowCheck9508]

theorem rawRowCheck9509 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form0 = rawRow9509 := by decide +kernel

theorem rowCheck9509 : row9509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9509 := by decide +kernel

theorem rowEval9509 (x : Key → ℝ) : Integer.Sparse.eval row9509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9509, Integer.Sparse.eval_collectBalanced, rawRowCheck9509]

theorem rawRowCheck9510 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form0 = rawRow9510 := by decide +kernel

theorem rowCheck9510 : row9510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9510 := by decide +kernel

theorem rowEval9510 (x : Key → ℝ) : Integer.Sparse.eval row9510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9510, Integer.Sparse.eval_collectBalanced, rawRowCheck9510]

theorem rawRowCheck9511 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form0 = rawRow9511 := by decide +kernel

theorem rowCheck9511 : row9511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9511 := by decide +kernel

theorem rowEval9511 (x : Key → ℝ) : Integer.Sparse.eval row9511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9511, Integer.Sparse.eval_collectBalanced, rawRowCheck9511]

theorem rawRowCheck9512 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form0 = rawRow9512 := by decide +kernel

theorem rowCheck9512 : row9512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9512 := by decide +kernel

theorem rowEval9512 (x : Key → ℝ) : Integer.Sparse.eval row9512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9512, Integer.Sparse.eval_collectBalanced, rawRowCheck9512]

theorem rawRowCheck9513 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form0 = rawRow9513 := by decide +kernel

theorem rowCheck9513 : row9513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9513 := by decide +kernel

theorem rowEval9513 (x : Key → ℝ) : Integer.Sparse.eval row9513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9513, Integer.Sparse.eval_collectBalanced, rawRowCheck9513]

theorem rawRowCheck9514 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form0 = rawRow9514 := by decide +kernel

theorem rowCheck9514 : row9514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9514 := by decide +kernel

theorem rowEval9514 (x : Key → ℝ) : Integer.Sparse.eval row9514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9514, Integer.Sparse.eval_collectBalanced, rawRowCheck9514]

theorem rawRowCheck9515 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form0 = rawRow9515 := by decide +kernel

theorem rowCheck9515 : row9515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9515 := by decide +kernel

theorem rowEval9515 (x : Key → ℝ) : Integer.Sparse.eval row9515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9515, Integer.Sparse.eval_collectBalanced, rawRowCheck9515]

theorem rawRowCheck9516 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form0 = rawRow9516 := by decide +kernel

theorem rowCheck9516 : row9516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9516 := by decide +kernel

theorem rowEval9516 (x : Key → ℝ) : Integer.Sparse.eval row9516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9516, Integer.Sparse.eval_collectBalanced, rawRowCheck9516]

theorem rawRowCheck9517 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form0 = rawRow9517 := by decide +kernel

theorem rowCheck9517 : row9517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9517 := by decide +kernel

theorem rowEval9517 (x : Key → ℝ) : Integer.Sparse.eval row9517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9517, Integer.Sparse.eval_collectBalanced, rawRowCheck9517]

theorem rawRowCheck9518 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form0 = rawRow9518 := by decide +kernel

theorem rowCheck9518 : row9518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9518 := by decide +kernel

theorem rowEval9518 (x : Key → ℝ) : Integer.Sparse.eval row9518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9518, Integer.Sparse.eval_collectBalanced, rawRowCheck9518]

theorem rawRowCheck9519 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form0 = rawRow9519 := by decide +kernel

theorem rowCheck9519 : row9519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9519 := by decide +kernel

theorem rowEval9519 (x : Key → ℝ) : Integer.Sparse.eval row9519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9519, Integer.Sparse.eval_collectBalanced, rawRowCheck9519]

theorem rawRowCheck9520 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form0 = rawRow9520 := by decide +kernel

theorem rowCheck9520 : row9520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9520 := by decide +kernel

theorem rowEval9520 (x : Key → ℝ) : Integer.Sparse.eval row9520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9520, Integer.Sparse.eval_collectBalanced, rawRowCheck9520]

theorem rawRowCheck9521 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form0 = rawRow9521 := by decide +kernel

theorem rowCheck9521 : row9521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9521 := by decide +kernel

theorem rowEval9521 (x : Key → ℝ) : Integer.Sparse.eval row9521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9521, Integer.Sparse.eval_collectBalanced, rawRowCheck9521]

theorem rawRowCheck9522 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form0 = rawRow9522 := by decide +kernel

theorem rowCheck9522 : row9522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9522 := by decide +kernel

theorem rowEval9522 (x : Key → ℝ) : Integer.Sparse.eval row9522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9522, Integer.Sparse.eval_collectBalanced, rawRowCheck9522]

theorem rawRowCheck9523 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form0 = rawRow9523 := by decide +kernel

theorem rowCheck9523 : row9523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9523 := by decide +kernel

theorem rowEval9523 (x : Key → ℝ) : Integer.Sparse.eval row9523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9523, Integer.Sparse.eval_collectBalanced, rawRowCheck9523]

theorem rawRowCheck9524 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form0 = rawRow9524 := by decide +kernel

theorem rowCheck9524 : row9524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9524 := by decide +kernel

theorem rowEval9524 (x : Key → ℝ) : Integer.Sparse.eval row9524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9524, Integer.Sparse.eval_collectBalanced, rawRowCheck9524]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9765 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form11 = rawRow9765 := by decide +kernel

theorem rowCheck9765 : row9765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9765 := by decide +kernel

theorem rowEval9765 (x : Key → ℝ) : Integer.Sparse.eval row9765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9765, Integer.Sparse.eval_collectBalanced, rawRowCheck9765]

theorem rawRowCheck9766 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form11 = rawRow9766 := by decide +kernel

theorem rowCheck9766 : row9766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9766 := by decide +kernel

theorem rowEval9766 (x : Key → ℝ) : Integer.Sparse.eval row9766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9766, Integer.Sparse.eval_collectBalanced, rawRowCheck9766]

theorem rawRowCheck9767 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form11 = rawRow9767 := by decide +kernel

theorem rowCheck9767 : row9767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9767 := by decide +kernel

theorem rowEval9767 (x : Key → ℝ) : Integer.Sparse.eval row9767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9767, Integer.Sparse.eval_collectBalanced, rawRowCheck9767]

theorem rawRowCheck9768 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form11 = rawRow9768 := by decide +kernel

theorem rowCheck9768 : row9768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9768 := by decide +kernel

theorem rowEval9768 (x : Key → ℝ) : Integer.Sparse.eval row9768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9768, Integer.Sparse.eval_collectBalanced, rawRowCheck9768]

theorem rawRowCheck9769 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form11 = rawRow9769 := by decide +kernel

theorem rowCheck9769 : row9769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9769 := by decide +kernel

theorem rowEval9769 (x : Key → ℝ) : Integer.Sparse.eval row9769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9769, Integer.Sparse.eval_collectBalanced, rawRowCheck9769]

theorem rawRowCheck9770 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form11 = rawRow9770 := by decide +kernel

theorem rowCheck9770 : row9770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9770 := by decide +kernel

theorem rowEval9770 (x : Key → ℝ) : Integer.Sparse.eval row9770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9770, Integer.Sparse.eval_collectBalanced, rawRowCheck9770]

theorem rawRowCheck9771 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form11 = rawRow9771 := by decide +kernel

theorem rowCheck9771 : row9771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9771 := by decide +kernel

theorem rowEval9771 (x : Key → ℝ) : Integer.Sparse.eval row9771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9771, Integer.Sparse.eval_collectBalanced, rawRowCheck9771]

theorem rawRowCheck9772 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form11 = rawRow9772 := by decide +kernel

theorem rowCheck9772 : row9772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9772 := by decide +kernel

theorem rowEval9772 (x : Key → ℝ) : Integer.Sparse.eval row9772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9772, Integer.Sparse.eval_collectBalanced, rawRowCheck9772]

theorem rawRowCheck9773 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form11 = rawRow9773 := by decide +kernel

theorem rowCheck9773 : row9773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9773 := by decide +kernel

theorem rowEval9773 (x : Key → ℝ) : Integer.Sparse.eval row9773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9773, Integer.Sparse.eval_collectBalanced, rawRowCheck9773]

theorem rawRowCheck9774 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form11 = rawRow9774 := by decide +kernel

theorem rowCheck9774 : row9774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9774 := by decide +kernel

theorem rowEval9774 (x : Key → ℝ) : Integer.Sparse.eval row9774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9774, Integer.Sparse.eval_collectBalanced, rawRowCheck9774]

theorem rawRowCheck9775 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form11 = rawRow9775 := by decide +kernel

theorem rowCheck9775 : row9775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9775 := by decide +kernel

theorem rowEval9775 (x : Key → ℝ) : Integer.Sparse.eval row9775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9775, Integer.Sparse.eval_collectBalanced, rawRowCheck9775]

theorem rawRowCheck9776 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form11 = rawRow9776 := by decide +kernel

theorem rowCheck9776 : row9776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9776 := by decide +kernel

theorem rowEval9776 (x : Key → ℝ) : Integer.Sparse.eval row9776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9776, Integer.Sparse.eval_collectBalanced, rawRowCheck9776]

theorem rawRowCheck9777 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form11 = rawRow9777 := by decide +kernel

theorem rowCheck9777 : row9777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9777 := by decide +kernel

theorem rowEval9777 (x : Key → ℝ) : Integer.Sparse.eval row9777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9777, Integer.Sparse.eval_collectBalanced, rawRowCheck9777]

theorem rawRowCheck9778 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form11 = rawRow9778 := by decide +kernel

theorem rowCheck9778 : row9778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9778 := by decide +kernel

theorem rowEval9778 (x : Key → ℝ) : Integer.Sparse.eval row9778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9778, Integer.Sparse.eval_collectBalanced, rawRowCheck9778]

theorem rawRowCheck9779 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form11 = rawRow9779 := by decide +kernel

theorem rowCheck9779 : row9779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9779 := by decide +kernel

theorem rowEval9779 (x : Key → ℝ) : Integer.Sparse.eval row9779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9779, Integer.Sparse.eval_collectBalanced, rawRowCheck9779]

theorem rawRowCheck9780 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form11 = rawRow9780 := by decide +kernel

theorem rowCheck9780 : row9780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9780 := by decide +kernel

theorem rowEval9780 (x : Key → ℝ) : Integer.Sparse.eval row9780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9780, Integer.Sparse.eval_collectBalanced, rawRowCheck9780]

theorem rawRowCheck9781 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form11 = rawRow9781 := by decide +kernel

theorem rowCheck9781 : row9781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9781 := by decide +kernel

theorem rowEval9781 (x : Key → ℝ) : Integer.Sparse.eval row9781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9781, Integer.Sparse.eval_collectBalanced, rawRowCheck9781]

theorem rawRowCheck9782 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form11 = rawRow9782 := by decide +kernel

theorem rowCheck9782 : row9782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9782 := by decide +kernel

theorem rowEval9782 (x : Key → ℝ) : Integer.Sparse.eval row9782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9782, Integer.Sparse.eval_collectBalanced, rawRowCheck9782]

theorem rawRowCheck9783 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form11 = rawRow9783 := by decide +kernel

theorem rowCheck9783 : row9783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9783 := by decide +kernel

theorem rowEval9783 (x : Key → ℝ) : Integer.Sparse.eval row9783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9783, Integer.Sparse.eval_collectBalanced, rawRowCheck9783]

theorem rawRowCheck9784 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form11 = rawRow9784 := by decide +kernel

theorem rowCheck9784 : row9784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9784 := by decide +kernel

theorem rowEval9784 (x : Key → ℝ) : Integer.Sparse.eval row9784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9784, Integer.Sparse.eval_collectBalanced, rawRowCheck9784]

theorem rawRowCheck9785 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form11 = rawRow9785 := by decide +kernel

theorem rowCheck9785 : row9785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9785 := by decide +kernel

theorem rowEval9785 (x : Key → ℝ) : Integer.Sparse.eval row9785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9785, Integer.Sparse.eval_collectBalanced, rawRowCheck9785]

theorem rawRowCheck9786 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form11 = rawRow9786 := by decide +kernel

theorem rowCheck9786 : row9786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9786 := by decide +kernel

theorem rowEval9786 (x : Key → ℝ) : Integer.Sparse.eval row9786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9786, Integer.Sparse.eval_collectBalanced, rawRowCheck9786]

theorem rawRowCheck9787 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form11 = rawRow9787 := by decide +kernel

theorem rowCheck9787 : row9787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9787 := by decide +kernel

theorem rowEval9787 (x : Key → ℝ) : Integer.Sparse.eval row9787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9787, Integer.Sparse.eval_collectBalanced, rawRowCheck9787]

theorem rawRowCheck9788 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form11 = rawRow9788 := by decide +kernel

theorem rowCheck9788 : row9788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9788 := by decide +kernel

theorem rowEval9788 (x : Key → ℝ) : Integer.Sparse.eval row9788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9788, Integer.Sparse.eval_collectBalanced, rawRowCheck9788]

theorem rawRowCheck9789 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form12 = rawRow9789 := by decide +kernel

theorem rowCheck9789 : row9789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9789 := by decide +kernel

theorem rowEval9789 (x : Key → ℝ) : Integer.Sparse.eval row9789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9789, Integer.Sparse.eval_collectBalanced, rawRowCheck9789]

theorem rawRowCheck9790 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form12 = rawRow9790 := by decide +kernel

theorem rowCheck9790 : row9790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9790 := by decide +kernel

theorem rowEval9790 (x : Key → ℝ) : Integer.Sparse.eval row9790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9790, Integer.Sparse.eval_collectBalanced, rawRowCheck9790]

theorem rawRowCheck9791 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form12 = rawRow9791 := by decide +kernel

theorem rowCheck9791 : row9791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9791 := by decide +kernel

theorem rowEval9791 (x : Key → ℝ) : Integer.Sparse.eval row9791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9791, Integer.Sparse.eval_collectBalanced, rawRowCheck9791]

theorem rawRowCheck9792 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form12 = rawRow9792 := by decide +kernel

theorem rowCheck9792 : row9792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9792 := by decide +kernel

theorem rowEval9792 (x : Key → ℝ) : Integer.Sparse.eval row9792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9792, Integer.Sparse.eval_collectBalanced, rawRowCheck9792]

theorem rawRowCheck9793 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form12 = rawRow9793 := by decide +kernel

theorem rowCheck9793 : row9793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9793 := by decide +kernel

theorem rowEval9793 (x : Key → ℝ) : Integer.Sparse.eval row9793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9793, Integer.Sparse.eval_collectBalanced, rawRowCheck9793]

theorem rawRowCheck9794 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form12 = rawRow9794 := by decide +kernel

theorem rowCheck9794 : row9794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9794 := by decide +kernel

theorem rowEval9794 (x : Key → ℝ) : Integer.Sparse.eval row9794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9794, Integer.Sparse.eval_collectBalanced, rawRowCheck9794]

theorem rawRowCheck9795 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form12 = rawRow9795 := by decide +kernel

theorem rowCheck9795 : row9795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9795 := by decide +kernel

theorem rowEval9795 (x : Key → ℝ) : Integer.Sparse.eval row9795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9795, Integer.Sparse.eval_collectBalanced, rawRowCheck9795]

theorem rawRowCheck9796 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form12 = rawRow9796 := by decide +kernel

theorem rowCheck9796 : row9796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9796 := by decide +kernel

theorem rowEval9796 (x : Key → ℝ) : Integer.Sparse.eval row9796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9796, Integer.Sparse.eval_collectBalanced, rawRowCheck9796]

theorem rawRowCheck9797 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form12 = rawRow9797 := by decide +kernel

theorem rowCheck9797 : row9797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9797 := by decide +kernel

theorem rowEval9797 (x : Key → ℝ) : Integer.Sparse.eval row9797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9797, Integer.Sparse.eval_collectBalanced, rawRowCheck9797]

theorem rawRowCheck9798 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form12 = rawRow9798 := by decide +kernel

theorem rowCheck9798 : row9798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9798 := by decide +kernel

theorem rowEval9798 (x : Key → ℝ) : Integer.Sparse.eval row9798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9798, Integer.Sparse.eval_collectBalanced, rawRowCheck9798]

theorem rawRowCheck9799 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form12 = rawRow9799 := by decide +kernel

theorem rowCheck9799 : row9799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9799 := by decide +kernel

theorem rowEval9799 (x : Key → ℝ) : Integer.Sparse.eval row9799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9799, Integer.Sparse.eval_collectBalanced, rawRowCheck9799]

theorem rawRowCheck9800 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form12 = rawRow9800 := by decide +kernel

theorem rowCheck9800 : row9800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9800 := by decide +kernel

theorem rowEval9800 (x : Key → ℝ) : Integer.Sparse.eval row9800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9800, Integer.Sparse.eval_collectBalanced, rawRowCheck9800]

theorem rawRowCheck9801 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form12 = rawRow9801 := by decide +kernel

theorem rowCheck9801 : row9801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9801 := by decide +kernel

theorem rowEval9801 (x : Key → ℝ) : Integer.Sparse.eval row9801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9801, Integer.Sparse.eval_collectBalanced, rawRowCheck9801]

theorem rawRowCheck9802 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form12 = rawRow9802 := by decide +kernel

theorem rowCheck9802 : row9802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9802 := by decide +kernel

theorem rowEval9802 (x : Key → ℝ) : Integer.Sparse.eval row9802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9802, Integer.Sparse.eval_collectBalanced, rawRowCheck9802]

theorem rawRowCheck9803 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form12 = rawRow9803 := by decide +kernel

theorem rowCheck9803 : row9803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9803 := by decide +kernel

theorem rowEval9803 (x : Key → ℝ) : Integer.Sparse.eval row9803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9803, Integer.Sparse.eval_collectBalanced, rawRowCheck9803]

theorem rawRowCheck9804 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form12 = rawRow9804 := by decide +kernel

theorem rowCheck9804 : row9804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9804 := by decide +kernel

theorem rowEval9804 (x : Key → ℝ) : Integer.Sparse.eval row9804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9804, Integer.Sparse.eval_collectBalanced, rawRowCheck9804]

theorem rawRowCheck9805 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form12 = rawRow9805 := by decide +kernel

theorem rowCheck9805 : row9805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9805 := by decide +kernel

theorem rowEval9805 (x : Key → ℝ) : Integer.Sparse.eval row9805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9805, Integer.Sparse.eval_collectBalanced, rawRowCheck9805]

theorem rawRowCheck9806 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form12 = rawRow9806 := by decide +kernel

theorem rowCheck9806 : row9806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9806 := by decide +kernel

theorem rowEval9806 (x : Key → ℝ) : Integer.Sparse.eval row9806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9806, Integer.Sparse.eval_collectBalanced, rawRowCheck9806]

theorem rawRowCheck9807 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form12 = rawRow9807 := by decide +kernel

theorem rowCheck9807 : row9807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9807 := by decide +kernel

theorem rowEval9807 (x : Key → ℝ) : Integer.Sparse.eval row9807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9807, Integer.Sparse.eval_collectBalanced, rawRowCheck9807]

theorem rawRowCheck9808 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form12 = rawRow9808 := by decide +kernel

theorem rowCheck9808 : row9808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9808 := by decide +kernel

theorem rowEval9808 (x : Key → ℝ) : Integer.Sparse.eval row9808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9808, Integer.Sparse.eval_collectBalanced, rawRowCheck9808]

theorem rawRowCheck9809 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form12 = rawRow9809 := by decide +kernel

theorem rowCheck9809 : row9809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9809 := by decide +kernel

theorem rowEval9809 (x : Key → ℝ) : Integer.Sparse.eval row9809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9809, Integer.Sparse.eval_collectBalanced, rawRowCheck9809]

theorem rawRowCheck9810 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form12 = rawRow9810 := by decide +kernel

theorem rowCheck9810 : row9810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9810 := by decide +kernel

theorem rowEval9810 (x : Key → ℝ) : Integer.Sparse.eval row9810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9810, Integer.Sparse.eval_collectBalanced, rawRowCheck9810]

theorem rawRowCheck9811 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form12 = rawRow9811 := by decide +kernel

theorem rowCheck9811 : row9811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9811 := by decide +kernel

theorem rowEval9811 (x : Key → ℝ) : Integer.Sparse.eval row9811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9811, Integer.Sparse.eval_collectBalanced, rawRowCheck9811]

theorem rawRowCheck9812 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form12 = rawRow9812 := by decide +kernel

theorem rowCheck9812 : row9812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9812 := by decide +kernel

theorem rowEval9812 (x : Key → ℝ) : Integer.Sparse.eval row9812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9812, Integer.Sparse.eval_collectBalanced, rawRowCheck9812]

theorem rawRowCheck9837 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form14 = rawRow9837 := by decide +kernel

theorem rowCheck9837 : row9837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9837 := by decide +kernel

theorem rowEval9837 (x : Key → ℝ) : Integer.Sparse.eval row9837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9837, Integer.Sparse.eval_collectBalanced, rawRowCheck9837]

theorem rawRowCheck9838 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form14 = rawRow9838 := by decide +kernel

theorem rowCheck9838 : row9838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9838 := by decide +kernel

theorem rowEval9838 (x : Key → ℝ) : Integer.Sparse.eval row9838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9838, Integer.Sparse.eval_collectBalanced, rawRowCheck9838]

theorem rawRowCheck9839 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form14 = rawRow9839 := by decide +kernel

theorem rowCheck9839 : row9839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9839 := by decide +kernel

theorem rowEval9839 (x : Key → ℝ) : Integer.Sparse.eval row9839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9839, Integer.Sparse.eval_collectBalanced, rawRowCheck9839]

theorem rawRowCheck9840 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form14 = rawRow9840 := by decide +kernel

theorem rowCheck9840 : row9840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9840 := by decide +kernel

theorem rowEval9840 (x : Key → ℝ) : Integer.Sparse.eval row9840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9840, Integer.Sparse.eval_collectBalanced, rawRowCheck9840]

theorem rawRowCheck9841 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form14 = rawRow9841 := by decide +kernel

theorem rowCheck9841 : row9841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9841 := by decide +kernel

theorem rowEval9841 (x : Key → ℝ) : Integer.Sparse.eval row9841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9841, Integer.Sparse.eval_collectBalanced, rawRowCheck9841]

theorem rawRowCheck9842 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form14 = rawRow9842 := by decide +kernel

theorem rowCheck9842 : row9842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9842 := by decide +kernel

theorem rowEval9842 (x : Key → ℝ) : Integer.Sparse.eval row9842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9842, Integer.Sparse.eval_collectBalanced, rawRowCheck9842]

theorem rawRowCheck9843 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow9843 := by decide +kernel

theorem rowCheck9843 : row9843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9843 := by decide +kernel

theorem rowEval9843 (x : Key → ℝ) : Integer.Sparse.eval row9843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9843, Integer.Sparse.eval_collectBalanced, rawRowCheck9843]

theorem rawRowCheck9844 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow9844 := by decide +kernel

theorem rowCheck9844 : row9844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9844 := by decide +kernel

theorem rowEval9844 (x : Key → ℝ) : Integer.Sparse.eval row9844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9844, Integer.Sparse.eval_collectBalanced, rawRowCheck9844]

theorem rawRowCheck9845 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow9845 := by decide +kernel

theorem rowCheck9845 : row9845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9845 := by decide +kernel

theorem rowEval9845 (x : Key → ℝ) : Integer.Sparse.eval row9845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9845, Integer.Sparse.eval_collectBalanced, rawRowCheck9845]

theorem rawRowCheck9846 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow9846 := by decide +kernel

theorem rowCheck9846 : row9846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9846 := by decide +kernel

theorem rowEval9846 (x : Key → ℝ) : Integer.Sparse.eval row9846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9846, Integer.Sparse.eval_collectBalanced, rawRowCheck9846]

theorem rawRowCheck9847 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow9847 := by decide +kernel

theorem rowCheck9847 : row9847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9847 := by decide +kernel

theorem rowEval9847 (x : Key → ℝ) : Integer.Sparse.eval row9847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9847, Integer.Sparse.eval_collectBalanced, rawRowCheck9847]

theorem rawRowCheck9848 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow9848 := by decide +kernel

theorem rowCheck9848 : row9848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9848 := by decide +kernel

theorem rowEval9848 (x : Key → ℝ) : Integer.Sparse.eval row9848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9848, Integer.Sparse.eval_collectBalanced, rawRowCheck9848]

theorem rawRowCheck9849 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form14 = rawRow9849 := by decide +kernel

theorem rowCheck9849 : row9849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9849 := by decide +kernel

theorem rowEval9849 (x : Key → ℝ) : Integer.Sparse.eval row9849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9849, Integer.Sparse.eval_collectBalanced, rawRowCheck9849]

theorem rawRowCheck9850 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form14 = rawRow9850 := by decide +kernel

theorem rowCheck9850 : row9850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9850 := by decide +kernel

theorem rowEval9850 (x : Key → ℝ) : Integer.Sparse.eval row9850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9850, Integer.Sparse.eval_collectBalanced, rawRowCheck9850]

theorem rawRowCheck9851 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form14 = rawRow9851 := by decide +kernel

theorem rowCheck9851 : row9851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9851 := by decide +kernel

theorem rowEval9851 (x : Key → ℝ) : Integer.Sparse.eval row9851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9851, Integer.Sparse.eval_collectBalanced, rawRowCheck9851]

theorem rawRowCheck9852 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form14 = rawRow9852 := by decide +kernel

theorem rowCheck9852 : row9852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9852 := by decide +kernel

theorem rowEval9852 (x : Key → ℝ) : Integer.Sparse.eval row9852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9852, Integer.Sparse.eval_collectBalanced, rawRowCheck9852]

theorem rawRowCheck9853 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form14 = rawRow9853 := by decide +kernel

theorem rowCheck9853 : row9853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9853 := by decide +kernel

theorem rowEval9853 (x : Key → ℝ) : Integer.Sparse.eval row9853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9853, Integer.Sparse.eval_collectBalanced, rawRowCheck9853]

theorem rawRowCheck9854 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form14 = rawRow9854 := by decide +kernel

theorem rowCheck9854 : row9854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9854 := by decide +kernel

theorem rowEval9854 (x : Key → ℝ) : Integer.Sparse.eval row9854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9854, Integer.Sparse.eval_collectBalanced, rawRowCheck9854]

theorem rawRowCheck9855 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form14 = rawRow9855 := by decide +kernel

theorem rowCheck9855 : row9855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9855 := by decide +kernel

theorem rowEval9855 (x : Key → ℝ) : Integer.Sparse.eval row9855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9855, Integer.Sparse.eval_collectBalanced, rawRowCheck9855]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck9856 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form14 = rawRow9856 := by decide +kernel

theorem rowCheck9856 : row9856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9856 := by decide +kernel

theorem rowEval9856 (x : Key → ℝ) : Integer.Sparse.eval row9856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9856, Integer.Sparse.eval_collectBalanced, rawRowCheck9856]

theorem rawRowCheck9857 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form14 = rawRow9857 := by decide +kernel

theorem rowCheck9857 : row9857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9857 := by decide +kernel

theorem rowEval9857 (x : Key → ℝ) : Integer.Sparse.eval row9857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9857, Integer.Sparse.eval_collectBalanced, rawRowCheck9857]

theorem rawRowCheck9858 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form14 = rawRow9858 := by decide +kernel

theorem rowCheck9858 : row9858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9858 := by decide +kernel

theorem rowEval9858 (x : Key → ℝ) : Integer.Sparse.eval row9858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9858, Integer.Sparse.eval_collectBalanced, rawRowCheck9858]

theorem rawRowCheck9859 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form14 = rawRow9859 := by decide +kernel

theorem rowCheck9859 : row9859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9859 := by decide +kernel

theorem rowEval9859 (x : Key → ℝ) : Integer.Sparse.eval row9859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9859, Integer.Sparse.eval_collectBalanced, rawRowCheck9859]

theorem rawRowCheck9860 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form14 = rawRow9860 := by decide +kernel

theorem rowCheck9860 : row9860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9860 := by decide +kernel

theorem rowEval9860 (x : Key → ℝ) : Integer.Sparse.eval row9860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9860, Integer.Sparse.eval_collectBalanced, rawRowCheck9860]

theorem rawRowCheck9885 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form16 = rawRow9885 := by decide +kernel

theorem rowCheck9885 : row9885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9885 := by decide +kernel

theorem rowEval9885 (x : Key → ℝ) : Integer.Sparse.eval row9885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9885, Integer.Sparse.eval_collectBalanced, rawRowCheck9885]

theorem rawRowCheck9886 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form16 = rawRow9886 := by decide +kernel

theorem rowCheck9886 : row9886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9886 := by decide +kernel

theorem rowEval9886 (x : Key → ℝ) : Integer.Sparse.eval row9886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9886, Integer.Sparse.eval_collectBalanced, rawRowCheck9886]

theorem rawRowCheck9887 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form16 = rawRow9887 := by decide +kernel

theorem rowCheck9887 : row9887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9887 := by decide +kernel

theorem rowEval9887 (x : Key → ℝ) : Integer.Sparse.eval row9887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9887, Integer.Sparse.eval_collectBalanced, rawRowCheck9887]

theorem rawRowCheck9888 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form16 = rawRow9888 := by decide +kernel

theorem rowCheck9888 : row9888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9888 := by decide +kernel

theorem rowEval9888 (x : Key → ℝ) : Integer.Sparse.eval row9888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9888, Integer.Sparse.eval_collectBalanced, rawRowCheck9888]

theorem rawRowCheck9889 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form16 = rawRow9889 := by decide +kernel

theorem rowCheck9889 : row9889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9889 := by decide +kernel

theorem rowEval9889 (x : Key → ℝ) : Integer.Sparse.eval row9889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9889, Integer.Sparse.eval_collectBalanced, rawRowCheck9889]

theorem rawRowCheck9890 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form16 = rawRow9890 := by decide +kernel

theorem rowCheck9890 : row9890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9890 := by decide +kernel

theorem rowEval9890 (x : Key → ℝ) : Integer.Sparse.eval row9890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9890, Integer.Sparse.eval_collectBalanced, rawRowCheck9890]

theorem rawRowCheck9891 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form16 = rawRow9891 := by decide +kernel

theorem rowCheck9891 : row9891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9891 := by decide +kernel

theorem rowEval9891 (x : Key → ℝ) : Integer.Sparse.eval row9891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9891, Integer.Sparse.eval_collectBalanced, rawRowCheck9891]

theorem rawRowCheck9892 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form16 = rawRow9892 := by decide +kernel

theorem rowCheck9892 : row9892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9892 := by decide +kernel

theorem rowEval9892 (x : Key → ℝ) : Integer.Sparse.eval row9892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9892, Integer.Sparse.eval_collectBalanced, rawRowCheck9892]

theorem rawRowCheck9893 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form16 = rawRow9893 := by decide +kernel

theorem rowCheck9893 : row9893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9893 := by decide +kernel

theorem rowEval9893 (x : Key → ℝ) : Integer.Sparse.eval row9893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9893, Integer.Sparse.eval_collectBalanced, rawRowCheck9893]

theorem rawRowCheck9894 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form16 = rawRow9894 := by decide +kernel

theorem rowCheck9894 : row9894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9894 := by decide +kernel

theorem rowEval9894 (x : Key → ℝ) : Integer.Sparse.eval row9894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9894, Integer.Sparse.eval_collectBalanced, rawRowCheck9894]

theorem rawRowCheck9895 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form16 = rawRow9895 := by decide +kernel

theorem rowCheck9895 : row9895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9895 := by decide +kernel

theorem rowEval9895 (x : Key → ℝ) : Integer.Sparse.eval row9895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9895, Integer.Sparse.eval_collectBalanced, rawRowCheck9895]

theorem rawRowCheck9896 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form16 = rawRow9896 := by decide +kernel

theorem rowCheck9896 : row9896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9896 := by decide +kernel

theorem rowEval9896 (x : Key → ℝ) : Integer.Sparse.eval row9896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9896, Integer.Sparse.eval_collectBalanced, rawRowCheck9896]

theorem rawRowCheck9897 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form16 = rawRow9897 := by decide +kernel

theorem rowCheck9897 : row9897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9897 := by decide +kernel

theorem rowEval9897 (x : Key → ℝ) : Integer.Sparse.eval row9897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9897, Integer.Sparse.eval_collectBalanced, rawRowCheck9897]

theorem rawRowCheck9898 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form16 = rawRow9898 := by decide +kernel

theorem rowCheck9898 : row9898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9898 := by decide +kernel

theorem rowEval9898 (x : Key → ℝ) : Integer.Sparse.eval row9898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9898, Integer.Sparse.eval_collectBalanced, rawRowCheck9898]

theorem rawRowCheck9899 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form16 = rawRow9899 := by decide +kernel

theorem rowCheck9899 : row9899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9899 := by decide +kernel

theorem rowEval9899 (x : Key → ℝ) : Integer.Sparse.eval row9899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9899, Integer.Sparse.eval_collectBalanced, rawRowCheck9899]

theorem rawRowCheck9900 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form16 = rawRow9900 := by decide +kernel

theorem rowCheck9900 : row9900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9900 := by decide +kernel

theorem rowEval9900 (x : Key → ℝ) : Integer.Sparse.eval row9900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9900, Integer.Sparse.eval_collectBalanced, rawRowCheck9900]

theorem rawRowCheck9901 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form16 = rawRow9901 := by decide +kernel

theorem rowCheck9901 : row9901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9901 := by decide +kernel

theorem rowEval9901 (x : Key → ℝ) : Integer.Sparse.eval row9901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9901, Integer.Sparse.eval_collectBalanced, rawRowCheck9901]

theorem rawRowCheck9902 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form16 = rawRow9902 := by decide +kernel

theorem rowCheck9902 : row9902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9902 := by decide +kernel

theorem rowEval9902 (x : Key → ℝ) : Integer.Sparse.eval row9902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9902, Integer.Sparse.eval_collectBalanced, rawRowCheck9902]

theorem rawRowCheck9903 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form16 = rawRow9903 := by decide +kernel

theorem rowCheck9903 : row9903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9903 := by decide +kernel

theorem rowEval9903 (x : Key → ℝ) : Integer.Sparse.eval row9903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9903, Integer.Sparse.eval_collectBalanced, rawRowCheck9903]

theorem rawRowCheck9904 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form16 = rawRow9904 := by decide +kernel

theorem rowCheck9904 : row9904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9904 := by decide +kernel

theorem rowEval9904 (x : Key → ℝ) : Integer.Sparse.eval row9904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9904, Integer.Sparse.eval_collectBalanced, rawRowCheck9904]

theorem rawRowCheck9905 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form16 = rawRow9905 := by decide +kernel

theorem rowCheck9905 : row9905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9905 := by decide +kernel

theorem rowEval9905 (x : Key → ℝ) : Integer.Sparse.eval row9905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9905, Integer.Sparse.eval_collectBalanced, rawRowCheck9905]

theorem rawRowCheck9906 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form16 = rawRow9906 := by decide +kernel

theorem rowCheck9906 : row9906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9906 := by decide +kernel

theorem rowEval9906 (x : Key → ℝ) : Integer.Sparse.eval row9906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9906, Integer.Sparse.eval_collectBalanced, rawRowCheck9906]

theorem rawRowCheck9907 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form16 = rawRow9907 := by decide +kernel

theorem rowCheck9907 : row9907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9907 := by decide +kernel

theorem rowEval9907 (x : Key → ℝ) : Integer.Sparse.eval row9907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9907, Integer.Sparse.eval_collectBalanced, rawRowCheck9907]

theorem rawRowCheck9908 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form16 = rawRow9908 := by decide +kernel

theorem rowCheck9908 : row9908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9908 := by decide +kernel

theorem rowEval9908 (x : Key → ℝ) : Integer.Sparse.eval row9908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9908, Integer.Sparse.eval_collectBalanced, rawRowCheck9908]

theorem rawRowCheck9909 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form17 = rawRow9909 := by decide +kernel

theorem rowCheck9909 : row9909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9909 := by decide +kernel

theorem rowEval9909 (x : Key → ℝ) : Integer.Sparse.eval row9909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9909, Integer.Sparse.eval_collectBalanced, rawRowCheck9909]

theorem rawRowCheck9910 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form17 = rawRow9910 := by decide +kernel

theorem rowCheck9910 : row9910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9910 := by decide +kernel

theorem rowEval9910 (x : Key → ℝ) : Integer.Sparse.eval row9910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9910, Integer.Sparse.eval_collectBalanced, rawRowCheck9910]

theorem rawRowCheck9911 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form17 = rawRow9911 := by decide +kernel

theorem rowCheck9911 : row9911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9911 := by decide +kernel

theorem rowEval9911 (x : Key → ℝ) : Integer.Sparse.eval row9911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck9911, Integer.Sparse.eval_collectBalanced, rawRowCheck9911]

theorem rawRowCheck9912 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form17 = rawRow9912 := by decide +kernel

theorem rowCheck9912 : row9912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9912 := by decide +kernel

theorem rowEval9912 (x : Key → ℝ) : Integer.Sparse.eval row9912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9912, Integer.Sparse.eval_collectBalanced, rawRowCheck9912]

theorem rawRowCheck9913 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form17 = rawRow9913 := by decide +kernel

theorem rowCheck9913 : row9913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9913 := by decide +kernel

theorem rowEval9913 (x : Key → ℝ) : Integer.Sparse.eval row9913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9913, Integer.Sparse.eval_collectBalanced, rawRowCheck9913]

theorem rawRowCheck9914 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form17 = rawRow9914 := by decide +kernel

theorem rowCheck9914 : row9914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9914 := by decide +kernel

theorem rowEval9914 (x : Key → ℝ) : Integer.Sparse.eval row9914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9914, Integer.Sparse.eval_collectBalanced, rawRowCheck9914]

theorem rawRowCheck9915 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form17 = rawRow9915 := by decide +kernel

theorem rowCheck9915 : row9915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9915 := by decide +kernel

theorem rowEval9915 (x : Key → ℝ) : Integer.Sparse.eval row9915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9915, Integer.Sparse.eval_collectBalanced, rawRowCheck9915]

theorem rawRowCheck9916 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form17 = rawRow9916 := by decide +kernel

theorem rowCheck9916 : row9916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9916 := by decide +kernel

theorem rowEval9916 (x : Key → ℝ) : Integer.Sparse.eval row9916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck9916, Integer.Sparse.eval_collectBalanced, rawRowCheck9916]

theorem rawRowCheck9917 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form17 = rawRow9917 := by decide +kernel

theorem rowCheck9917 : row9917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9917 := by decide +kernel

theorem rowEval9917 (x : Key → ℝ) : Integer.Sparse.eval row9917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9917, Integer.Sparse.eval_collectBalanced, rawRowCheck9917]

theorem rawRowCheck9918 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form17 = rawRow9918 := by decide +kernel

theorem rowCheck9918 : row9918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9918 := by decide +kernel

theorem rowEval9918 (x : Key → ℝ) : Integer.Sparse.eval row9918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9918, Integer.Sparse.eval_collectBalanced, rawRowCheck9918]

theorem rawRowCheck9919 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form17 = rawRow9919 := by decide +kernel

theorem rowCheck9919 : row9919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9919 := by decide +kernel

theorem rowEval9919 (x : Key → ℝ) : Integer.Sparse.eval row9919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck9919, Integer.Sparse.eval_collectBalanced, rawRowCheck9919]

theorem rawRowCheck9920 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form17 = rawRow9920 := by decide +kernel

theorem rowCheck9920 : row9920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9920 := by decide +kernel

theorem rowEval9920 (x : Key → ℝ) : Integer.Sparse.eval row9920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9920, Integer.Sparse.eval_collectBalanced, rawRowCheck9920]

theorem rawRowCheck9921 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form17 = rawRow9921 := by decide +kernel

theorem rowCheck9921 : row9921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9921 := by decide +kernel

theorem rowEval9921 (x : Key → ℝ) : Integer.Sparse.eval row9921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9921, Integer.Sparse.eval_collectBalanced, rawRowCheck9921]

theorem rawRowCheck9922 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form17 = rawRow9922 := by decide +kernel

theorem rowCheck9922 : row9922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9922 := by decide +kernel

theorem rowEval9922 (x : Key → ℝ) : Integer.Sparse.eval row9922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9922, Integer.Sparse.eval_collectBalanced, rawRowCheck9922]

theorem rawRowCheck9923 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form17 = rawRow9923 := by decide +kernel

theorem rowCheck9923 : row9923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9923 := by decide +kernel

theorem rowEval9923 (x : Key → ℝ) : Integer.Sparse.eval row9923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9923, Integer.Sparse.eval_collectBalanced, rawRowCheck9923]

theorem rawRowCheck9924 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form17 = rawRow9924 := by decide +kernel

theorem rowCheck9924 : row9924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9924 := by decide +kernel

theorem rowEval9924 (x : Key → ℝ) : Integer.Sparse.eval row9924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9924, Integer.Sparse.eval_collectBalanced, rawRowCheck9924]

theorem rawRowCheck9925 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form17 = rawRow9925 := by decide +kernel

theorem rowCheck9925 : row9925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9925 := by decide +kernel

theorem rowEval9925 (x : Key → ℝ) : Integer.Sparse.eval row9925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9925, Integer.Sparse.eval_collectBalanced, rawRowCheck9925]

theorem rawRowCheck9926 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form17 = rawRow9926 := by decide +kernel

theorem rowCheck9926 : row9926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9926 := by decide +kernel

theorem rowEval9926 (x : Key → ℝ) : Integer.Sparse.eval row9926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9926, Integer.Sparse.eval_collectBalanced, rawRowCheck9926]

theorem rawRowCheck9927 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form17 = rawRow9927 := by decide +kernel

theorem rowCheck9927 : row9927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9927 := by decide +kernel

theorem rowEval9927 (x : Key → ℝ) : Integer.Sparse.eval row9927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9927, Integer.Sparse.eval_collectBalanced, rawRowCheck9927]

theorem rawRowCheck9928 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form17 = rawRow9928 := by decide +kernel

theorem rowCheck9928 : row9928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9928 := by decide +kernel

theorem rowEval9928 (x : Key → ℝ) : Integer.Sparse.eval row9928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9928, Integer.Sparse.eval_collectBalanced, rawRowCheck9928]

theorem rawRowCheck9929 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form17 = rawRow9929 := by decide +kernel

theorem rowCheck9929 : row9929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9929 := by decide +kernel

theorem rowEval9929 (x : Key → ℝ) : Integer.Sparse.eval row9929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9929, Integer.Sparse.eval_collectBalanced, rawRowCheck9929]

theorem rawRowCheck9930 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form17 = rawRow9930 := by decide +kernel

theorem rowCheck9930 : row9930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9930 := by decide +kernel

theorem rowEval9930 (x : Key → ℝ) : Integer.Sparse.eval row9930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9930, Integer.Sparse.eval_collectBalanced, rawRowCheck9930]

theorem rawRowCheck9931 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form17 = rawRow9931 := by decide +kernel

theorem rowCheck9931 : row9931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9931 := by decide +kernel

theorem rowEval9931 (x : Key → ℝ) : Integer.Sparse.eval row9931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck9931, Integer.Sparse.eval_collectBalanced, rawRowCheck9931]

theorem rawRowCheck9932 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form17 = rawRow9932 := by decide +kernel

theorem rowCheck9932 : row9932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9932 := by decide +kernel

theorem rowEval9932 (x : Key → ℝ) : Integer.Sparse.eval row9932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck9932, Integer.Sparse.eval_collectBalanced, rawRowCheck9932]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck9645 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form6 = rawRow9645 := by decide +kernel

theorem rowCheck9645 : row9645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9645 := by decide +kernel

theorem rowEval9645 (x : Key → ℝ) : Integer.Sparse.eval row9645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9645, Integer.Sparse.eval_collectBalanced, rawRowCheck9645]

theorem rawRowCheck9646 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form6 = rawRow9646 := by decide +kernel

theorem rowCheck9646 : row9646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9646 := by decide +kernel

theorem rowEval9646 (x : Key → ℝ) : Integer.Sparse.eval row9646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9646, Integer.Sparse.eval_collectBalanced, rawRowCheck9646]

theorem rawRowCheck9647 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form6 = rawRow9647 := by decide +kernel

theorem rowCheck9647 : row9647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9647 := by decide +kernel

theorem rowEval9647 (x : Key → ℝ) : Integer.Sparse.eval row9647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9647, Integer.Sparse.eval_collectBalanced, rawRowCheck9647]

theorem rawRowCheck9648 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form6 = rawRow9648 := by decide +kernel

theorem rowCheck9648 : row9648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9648 := by decide +kernel

theorem rowEval9648 (x : Key → ℝ) : Integer.Sparse.eval row9648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9648, Integer.Sparse.eval_collectBalanced, rawRowCheck9648]

theorem rawRowCheck9649 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form6 = rawRow9649 := by decide +kernel

theorem rowCheck9649 : row9649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9649 := by decide +kernel

theorem rowEval9649 (x : Key → ℝ) : Integer.Sparse.eval row9649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9649, Integer.Sparse.eval_collectBalanced, rawRowCheck9649]

theorem rawRowCheck9650 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form6 = rawRow9650 := by decide +kernel

theorem rowCheck9650 : row9650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9650 := by decide +kernel

theorem rowEval9650 (x : Key → ℝ) : Integer.Sparse.eval row9650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9650, Integer.Sparse.eval_collectBalanced, rawRowCheck9650]

theorem rawRowCheck9651 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form6 = rawRow9651 := by decide +kernel

theorem rowCheck9651 : row9651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9651 := by decide +kernel

theorem rowEval9651 (x : Key → ℝ) : Integer.Sparse.eval row9651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9651, Integer.Sparse.eval_collectBalanced, rawRowCheck9651]

theorem rawRowCheck9652 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form6 = rawRow9652 := by decide +kernel

theorem rowCheck9652 : row9652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9652 := by decide +kernel

theorem rowEval9652 (x : Key → ℝ) : Integer.Sparse.eval row9652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9652, Integer.Sparse.eval_collectBalanced, rawRowCheck9652]

theorem rawRowCheck9653 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form6 = rawRow9653 := by decide +kernel

theorem rowCheck9653 : row9653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9653 := by decide +kernel

theorem rowEval9653 (x : Key → ℝ) : Integer.Sparse.eval row9653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9653, Integer.Sparse.eval_collectBalanced, rawRowCheck9653]

theorem rawRowCheck9654 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form6 = rawRow9654 := by decide +kernel

theorem rowCheck9654 : row9654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9654 := by decide +kernel

theorem rowEval9654 (x : Key → ℝ) : Integer.Sparse.eval row9654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9654, Integer.Sparse.eval_collectBalanced, rawRowCheck9654]

theorem rawRowCheck9655 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form6 = rawRow9655 := by decide +kernel

theorem rowCheck9655 : row9655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9655 := by decide +kernel

theorem rowEval9655 (x : Key → ℝ) : Integer.Sparse.eval row9655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9655, Integer.Sparse.eval_collectBalanced, rawRowCheck9655]

theorem rawRowCheck9656 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form6 = rawRow9656 := by decide +kernel

theorem rowCheck9656 : row9656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9656 := by decide +kernel

theorem rowEval9656 (x : Key → ℝ) : Integer.Sparse.eval row9656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9656, Integer.Sparse.eval_collectBalanced, rawRowCheck9656]

theorem rawRowCheck9657 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form6 = rawRow9657 := by decide +kernel

theorem rowCheck9657 : row9657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9657 := by decide +kernel

theorem rowEval9657 (x : Key → ℝ) : Integer.Sparse.eval row9657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9657, Integer.Sparse.eval_collectBalanced, rawRowCheck9657]

theorem rawRowCheck9658 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form6 = rawRow9658 := by decide +kernel

theorem rowCheck9658 : row9658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9658 := by decide +kernel

theorem rowEval9658 (x : Key → ℝ) : Integer.Sparse.eval row9658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9658, Integer.Sparse.eval_collectBalanced, rawRowCheck9658]

theorem rawRowCheck9659 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form6 = rawRow9659 := by decide +kernel

theorem rowCheck9659 : row9659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9659 := by decide +kernel

theorem rowEval9659 (x : Key → ℝ) : Integer.Sparse.eval row9659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9659, Integer.Sparse.eval_collectBalanced, rawRowCheck9659]

theorem rawRowCheck9660 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form6 = rawRow9660 := by decide +kernel

theorem rowCheck9660 : row9660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9660 := by decide +kernel

theorem rowEval9660 (x : Key → ℝ) : Integer.Sparse.eval row9660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9660, Integer.Sparse.eval_collectBalanced, rawRowCheck9660]

theorem rawRowCheck9661 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form6 = rawRow9661 := by decide +kernel

theorem rowCheck9661 : row9661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9661 := by decide +kernel

theorem rowEval9661 (x : Key → ℝ) : Integer.Sparse.eval row9661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9661, Integer.Sparse.eval_collectBalanced, rawRowCheck9661]

theorem rawRowCheck9662 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form6 = rawRow9662 := by decide +kernel

theorem rowCheck9662 : row9662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9662 := by decide +kernel

theorem rowEval9662 (x : Key → ℝ) : Integer.Sparse.eval row9662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9662, Integer.Sparse.eval_collectBalanced, rawRowCheck9662]

theorem rawRowCheck9663 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form6 = rawRow9663 := by decide +kernel

theorem rowCheck9663 : row9663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9663 := by decide +kernel

theorem rowEval9663 (x : Key → ℝ) : Integer.Sparse.eval row9663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9663, Integer.Sparse.eval_collectBalanced, rawRowCheck9663]

theorem rawRowCheck9664 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form6 = rawRow9664 := by decide +kernel

theorem rowCheck9664 : row9664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9664 := by decide +kernel

theorem rowEval9664 (x : Key → ℝ) : Integer.Sparse.eval row9664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9664, Integer.Sparse.eval_collectBalanced, rawRowCheck9664]

theorem rawRowCheck9665 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form6 = rawRow9665 := by decide +kernel

theorem rowCheck9665 : row9665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9665 := by decide +kernel

theorem rowEval9665 (x : Key → ℝ) : Integer.Sparse.eval row9665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9665, Integer.Sparse.eval_collectBalanced, rawRowCheck9665]

theorem rawRowCheck9666 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form6 = rawRow9666 := by decide +kernel

theorem rowCheck9666 : row9666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9666 := by decide +kernel

theorem rowEval9666 (x : Key → ℝ) : Integer.Sparse.eval row9666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9666, Integer.Sparse.eval_collectBalanced, rawRowCheck9666]

theorem rawRowCheck9667 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form6 = rawRow9667 := by decide +kernel

theorem rowCheck9667 : row9667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9667 := by decide +kernel

theorem rowEval9667 (x : Key → ℝ) : Integer.Sparse.eval row9667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9667, Integer.Sparse.eval_collectBalanced, rawRowCheck9667]

theorem rawRowCheck9668 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form6 = rawRow9668 := by decide +kernel

theorem rowCheck9668 : row9668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9668 := by decide +kernel

theorem rowEval9668 (x : Key → ℝ) : Integer.Sparse.eval row9668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9668, Integer.Sparse.eval_collectBalanced, rawRowCheck9668]

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

theorem entryCheck17_0 : entry17_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_0 k)) := by decide +kernel

theorem rowsSound17_0 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval9501 x
  · exact rowEval9502 x
  · exact rowEval9503 x
  · exact rowEval9504 x
  · exact rowEval9505 x
  · exact rowEval9506 x
  · exact rowEval9507 x
  · exact rowEval9508 x
  · exact rowEval9509 x
  · exact rowEval9510 x
  · exact rowEval9511 x
  · exact rowEval9512 x
  · exact rowEval9513 x
  · exact rowEval9514 x
  · exact rowEval9515 x
  · exact rowEval9516 x
  · exact rowEval9517 x
  · exact rowEval9518 x
  · exact rowEval9519 x
  · exact rowEval9520 x
  · exact rowEval9521 x
  · exact rowEval9522 x
  · exact rowEval9523 x
  · exact rowEval9524 x

theorem entryEval17_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_0 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck17_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_0]

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

theorem entryCheck17_6 : entry17_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_6 k)) := by decide +kernel

theorem rowsSound17_6 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval9645 x
  · exact rowEval9646 x
  · exact rowEval9647 x
  · exact rowEval9648 x
  · exact rowEval9649 x
  · exact rowEval9650 x
  · exact rowEval9651 x
  · exact rowEval9652 x
  · exact rowEval9653 x
  · exact rowEval9654 x
  · exact rowEval9655 x
  · exact rowEval9656 x
  · exact rowEval9657 x
  · exact rowEval9658 x
  · exact rowEval9659 x
  · exact rowEval9660 x
  · exact rowEval9661 x
  · exact rowEval9662 x
  · exact rowEval9663 x
  · exact rowEval9664 x
  · exact rowEval9665 x
  · exact rowEval9666 x
  · exact rowEval9667 x
  · exact rowEval9668 x

theorem entryEval17_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_6 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck17_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_6]

theorem entryCheck17_11 : entry17_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_11 k)) := by decide +kernel

theorem rowsSound17_11 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9765 x
  · exact rowEval9766 x
  · exact rowEval9767 x
  · exact rowEval9768 x
  · exact rowEval9769 x
  · exact rowEval9770 x
  · exact rowEval9771 x
  · exact rowEval9772 x
  · exact rowEval9773 x
  · exact rowEval9774 x
  · exact rowEval9775 x
  · exact rowEval9776 x
  · exact rowEval9777 x
  · exact rowEval9778 x
  · exact rowEval9779 x
  · exact rowEval9780 x
  · exact rowEval9781 x
  · exact rowEval9782 x
  · exact rowEval9783 x
  · exact rowEval9784 x
  · exact rowEval9785 x
  · exact rowEval9786 x
  · exact rowEval9787 x
  · exact rowEval9788 x

theorem entryEval17_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_11 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck17_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_11]

theorem entryCheck17_12 : entry17_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_12 k)) := by decide +kernel

theorem rowsSound17_12 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9789 x
  · exact rowEval9790 x
  · exact rowEval9791 x
  · exact rowEval9792 x
  · exact rowEval9793 x
  · exact rowEval9794 x
  · exact rowEval9795 x
  · exact rowEval9796 x
  · exact rowEval9797 x
  · exact rowEval9798 x
  · exact rowEval9799 x
  · exact rowEval9800 x
  · exact rowEval9801 x
  · exact rowEval9802 x
  · exact rowEval9803 x
  · exact rowEval9804 x
  · exact rowEval9805 x
  · exact rowEval9806 x
  · exact rowEval9807 x
  · exact rowEval9808 x
  · exact rowEval9809 x
  · exact rowEval9810 x
  · exact rowEval9811 x
  · exact rowEval9812 x

theorem entryEval17_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_12 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck17_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_12]

theorem entryCheck17_14 : entry17_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_14 k)) := by decide +kernel

theorem rowsSound17_14 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9837 x
  · exact rowEval9838 x
  · exact rowEval9839 x
  · exact rowEval9840 x
  · exact rowEval9841 x
  · exact rowEval9842 x
  · exact rowEval9843 x
  · exact rowEval9844 x
  · exact rowEval9845 x
  · exact rowEval9846 x
  · exact rowEval9847 x
  · exact rowEval9848 x
  · exact rowEval9849 x
  · exact rowEval9850 x
  · exact rowEval9851 x
  · exact rowEval9852 x
  · exact rowEval9853 x
  · exact rowEval9854 x
  · exact rowEval9855 x
  · exact rowEval9856 x
  · exact rowEval9857 x
  · exact rowEval9858 x
  · exact rowEval9859 x
  · exact rowEval9860 x

theorem entryEval17_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_14 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck17_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_14]

theorem entryCheck17_16 : entry17_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_16 k)) := by decide +kernel

theorem rowsSound17_16 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval9885 x
  · exact rowEval9886 x
  · exact rowEval9887 x
  · exact rowEval9888 x
  · exact rowEval9889 x
  · exact rowEval9890 x
  · exact rowEval9891 x
  · exact rowEval9892 x
  · exact rowEval9893 x
  · exact rowEval9894 x
  · exact rowEval9895 x
  · exact rowEval9896 x
  · exact rowEval9897 x
  · exact rowEval9898 x
  · exact rowEval9899 x
  · exact rowEval9900 x
  · exact rowEval9901 x
  · exact rowEval9902 x
  · exact rowEval9903 x
  · exact rowEval9904 x
  · exact rowEval9905 x
  · exact rowEval9906 x
  · exact rowEval9907 x
  · exact rowEval9908 x

theorem entryEval17_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_16 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck17_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_16]

theorem entryCheck17_17 : entry17_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_17 k)) := by decide +kernel

theorem rowsSound17_17 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval9909 x
  · exact rowEval9910 x
  · exact rowEval9911 x
  · exact rowEval9912 x
  · exact rowEval9913 x
  · exact rowEval9914 x
  · exact rowEval9915 x
  · exact rowEval9916 x
  · exact rowEval9917 x
  · exact rowEval9918 x
  · exact rowEval9919 x
  · exact rowEval9920 x
  · exact rowEval9921 x
  · exact rowEval9922 x
  · exact rowEval9923 x
  · exact rowEval9924 x
  · exact rowEval9925 x
  · exact rowEval9926 x
  · exact rowEval9927 x
  · exact rowEval9928 x
  · exact rowEval9929 x
  · exact rowEval9930 x
  · exact rowEval9931 x
  · exact rowEval9932 x

theorem entryEval17_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_17 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck17_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_17]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10341 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17 = rawRow10341 := by decide +kernel

theorem rowCheck10341 : row10341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10341 := by decide +kernel

theorem rowEval10341 (x : Key → ℝ) : Integer.Sparse.eval row10341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10341, Integer.Sparse.eval_collectBalanced, rawRowCheck10341]

theorem rawRowCheck10342 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17 = rawRow10342 := by decide +kernel

theorem rowCheck10342 : row10342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10342 := by decide +kernel

theorem rowEval10342 (x : Key → ℝ) : Integer.Sparse.eval row10342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10342, Integer.Sparse.eval_collectBalanced, rawRowCheck10342]

theorem rawRowCheck10343 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17 = rawRow10343 := by decide +kernel

theorem rowCheck10343 : row10343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10343 := by decide +kernel

theorem rowEval10343 (x : Key → ℝ) : Integer.Sparse.eval row10343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10343, Integer.Sparse.eval_collectBalanced, rawRowCheck10343]

theorem rawRowCheck10344 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17 = rawRow10344 := by decide +kernel

theorem rowCheck10344 : row10344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10344 := by decide +kernel

theorem rowEval10344 (x : Key → ℝ) : Integer.Sparse.eval row10344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10344, Integer.Sparse.eval_collectBalanced, rawRowCheck10344]

theorem rawRowCheck10345 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17 = rawRow10345 := by decide +kernel

theorem rowCheck10345 : row10345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10345 := by decide +kernel

theorem rowEval10345 (x : Key → ℝ) : Integer.Sparse.eval row10345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10345, Integer.Sparse.eval_collectBalanced, rawRowCheck10345]

theorem rawRowCheck10346 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17 = rawRow10346 := by decide +kernel

theorem rowCheck10346 : row10346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10346 := by decide +kernel

theorem rowEval10346 (x : Key → ℝ) : Integer.Sparse.eval row10346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10346, Integer.Sparse.eval_collectBalanced, rawRowCheck10346]

theorem rawRowCheck10347 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17 = rawRow10347 := by decide +kernel

theorem rowCheck10347 : row10347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10347 := by decide +kernel

theorem rowEval10347 (x : Key → ℝ) : Integer.Sparse.eval row10347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10347, Integer.Sparse.eval_collectBalanced, rawRowCheck10347]

theorem rawRowCheck10348 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17 = rawRow10348 := by decide +kernel

theorem rowCheck10348 : row10348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10348 := by decide +kernel

theorem rowEval10348 (x : Key → ℝ) : Integer.Sparse.eval row10348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10348, Integer.Sparse.eval_collectBalanced, rawRowCheck10348]

theorem rawRowCheck10349 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17 = rawRow10349 := by decide +kernel

theorem rowCheck10349 : row10349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10349 := by decide +kernel

theorem rowEval10349 (x : Key → ℝ) : Integer.Sparse.eval row10349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10349, Integer.Sparse.eval_collectBalanced, rawRowCheck10349]

theorem rawRowCheck10350 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17 = rawRow10350 := by decide +kernel

theorem rowCheck10350 : row10350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10350 := by decide +kernel

theorem rowEval10350 (x : Key → ℝ) : Integer.Sparse.eval row10350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10350, Integer.Sparse.eval_collectBalanced, rawRowCheck10350]

theorem rawRowCheck10351 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17 = rawRow10351 := by decide +kernel

theorem rowCheck10351 : row10351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10351 := by decide +kernel

theorem rowEval10351 (x : Key → ℝ) : Integer.Sparse.eval row10351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10351, Integer.Sparse.eval_collectBalanced, rawRowCheck10351]

theorem rawRowCheck10352 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17 = rawRow10352 := by decide +kernel

theorem rowCheck10352 : row10352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10352 := by decide +kernel

theorem rowEval10352 (x : Key → ℝ) : Integer.Sparse.eval row10352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10352, Integer.Sparse.eval_collectBalanced, rawRowCheck10352]

theorem rawRowCheck10353 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form17 = rawRow10353 := by decide +kernel

theorem rowCheck10353 : row10353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10353 := by decide +kernel

theorem rowEval10353 (x : Key → ℝ) : Integer.Sparse.eval row10353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10353, Integer.Sparse.eval_collectBalanced, rawRowCheck10353]

theorem rawRowCheck10354 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form17 = rawRow10354 := by decide +kernel

theorem rowCheck10354 : row10354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10354 := by decide +kernel

theorem rowEval10354 (x : Key → ℝ) : Integer.Sparse.eval row10354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10354, Integer.Sparse.eval_collectBalanced, rawRowCheck10354]

theorem rawRowCheck10355 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form17 = rawRow10355 := by decide +kernel

theorem rowCheck10355 : row10355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10355 := by decide +kernel

theorem rowEval10355 (x : Key → ℝ) : Integer.Sparse.eval row10355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10355, Integer.Sparse.eval_collectBalanced, rawRowCheck10355]

theorem rawRowCheck10356 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form17 = rawRow10356 := by decide +kernel

theorem rowCheck10356 : row10356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10356 := by decide +kernel

theorem rowEval10356 (x : Key → ℝ) : Integer.Sparse.eval row10356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10356, Integer.Sparse.eval_collectBalanced, rawRowCheck10356]

theorem rawRowCheck10357 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form17 = rawRow10357 := by decide +kernel

theorem rowCheck10357 : row10357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10357 := by decide +kernel

theorem rowEval10357 (x : Key → ℝ) : Integer.Sparse.eval row10357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10357, Integer.Sparse.eval_collectBalanced, rawRowCheck10357]

theorem rawRowCheck10358 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form17 = rawRow10358 := by decide +kernel

theorem rowCheck10358 : row10358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10358 := by decide +kernel

theorem rowEval10358 (x : Key → ℝ) : Integer.Sparse.eval row10358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10358, Integer.Sparse.eval_collectBalanced, rawRowCheck10358]

theorem rawRowCheck10359 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form17 = rawRow10359 := by decide +kernel

theorem rowCheck10359 : row10359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10359 := by decide +kernel

theorem rowEval10359 (x : Key → ℝ) : Integer.Sparse.eval row10359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10359, Integer.Sparse.eval_collectBalanced, rawRowCheck10359]

theorem rawRowCheck10360 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form17 = rawRow10360 := by decide +kernel

theorem rowCheck10360 : row10360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10360 := by decide +kernel

theorem rowEval10360 (x : Key → ℝ) : Integer.Sparse.eval row10360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10360, Integer.Sparse.eval_collectBalanced, rawRowCheck10360]

theorem rawRowCheck10361 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form17 = rawRow10361 := by decide +kernel

theorem rowCheck10361 : row10361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10361 := by decide +kernel

theorem rowEval10361 (x : Key → ℝ) : Integer.Sparse.eval row10361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10361, Integer.Sparse.eval_collectBalanced, rawRowCheck10361]

theorem rawRowCheck10362 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form17 = rawRow10362 := by decide +kernel

theorem rowCheck10362 : row10362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10362 := by decide +kernel

theorem rowEval10362 (x : Key → ℝ) : Integer.Sparse.eval row10362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10362, Integer.Sparse.eval_collectBalanced, rawRowCheck10362]

theorem rawRowCheck10363 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form17 = rawRow10363 := by decide +kernel

theorem rowCheck10363 : row10363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10363 := by decide +kernel

theorem rowEval10363 (x : Key → ℝ) : Integer.Sparse.eval row10363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10363, Integer.Sparse.eval_collectBalanced, rawRowCheck10363]

theorem rawRowCheck10364 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form17 = rawRow10364 := by decide +kernel

theorem rowCheck10364 : row10364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10364 := by decide +kernel

theorem rowEval10364 (x : Key → ℝ) : Integer.Sparse.eval row10364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10364, Integer.Sparse.eval_collectBalanced, rawRowCheck10364]

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

theorem entryCheck18_17 : entry18_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_17 k)) := by decide +kernel

theorem rowsSound18_17 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval10341 x
  · exact rowEval10342 x
  · exact rowEval10343 x
  · exact rowEval10344 x
  · exact rowEval10345 x
  · exact rowEval10346 x
  · exact rowEval10347 x
  · exact rowEval10348 x
  · exact rowEval10349 x
  · exact rowEval10350 x
  · exact rowEval10351 x
  · exact rowEval10352 x
  · exact rowEval10353 x
  · exact rowEval10354 x
  · exact rowEval10355 x
  · exact rowEval10356 x
  · exact rowEval10357 x
  · exact rowEval10358 x
  · exact rowEval10359 x
  · exact rowEval10360 x
  · exact rowEval10361 x
  · exact rowEval10362 x
  · exact rowEval10363 x
  · exact rowEval10364 x

theorem entryEval18_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_17 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck18_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_17]

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

theorem rawRowCheck10559 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form17 = rawRow10559 := by decide +kernel

theorem rowCheck10559 : row10559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10559 := by decide +kernel

theorem rowEval10559 (x : Key → ℝ) : Integer.Sparse.eval row10559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10559, Integer.Sparse.eval_collectBalanced, rawRowCheck10559]

theorem rawRowCheck10560 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form17 = rawRow10560 := by decide +kernel

theorem rowCheck10560 : row10560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10560 := by decide +kernel

theorem rowEval10560 (x : Key → ℝ) : Integer.Sparse.eval row10560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10560, Integer.Sparse.eval_collectBalanced, rawRowCheck10560]

theorem rawRowCheck10561 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form17 = rawRow10561 := by decide +kernel

theorem rowCheck10561 : row10561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10561 := by decide +kernel

theorem rowEval10561 (x : Key → ℝ) : Integer.Sparse.eval row10561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10561, Integer.Sparse.eval_collectBalanced, rawRowCheck10561]

theorem rawRowCheck10562 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form17 = rawRow10562 := by decide +kernel

theorem rowCheck10562 : row10562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10562 := by decide +kernel

theorem rowEval10562 (x : Key → ℝ) : Integer.Sparse.eval row10562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10562, Integer.Sparse.eval_collectBalanced, rawRowCheck10562]

theorem rawRowCheck10563 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form17 = rawRow10563 := by decide +kernel

theorem rowCheck10563 : row10563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10563 := by decide +kernel

theorem rowEval10563 (x : Key → ℝ) : Integer.Sparse.eval row10563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10563, Integer.Sparse.eval_collectBalanced, rawRowCheck10563]

theorem rawRowCheck10564 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form17 = rawRow10564 := by decide +kernel

theorem rowCheck10564 : row10564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10564 := by decide +kernel

theorem rowEval10564 (x : Key → ℝ) : Integer.Sparse.eval row10564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10564, Integer.Sparse.eval_collectBalanced, rawRowCheck10564]

theorem rawRowCheck10565 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form17 = rawRow10565 := by decide +kernel

theorem rowCheck10565 : row10565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10565 := by decide +kernel

theorem rowEval10565 (x : Key → ℝ) : Integer.Sparse.eval row10565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10565, Integer.Sparse.eval_collectBalanced, rawRowCheck10565]

theorem rawRowCheck10566 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form17 = rawRow10566 := by decide +kernel

theorem rowCheck10566 : row10566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10566 := by decide +kernel

theorem rowEval10566 (x : Key → ℝ) : Integer.Sparse.eval row10566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10566, Integer.Sparse.eval_collectBalanced, rawRowCheck10566]

theorem rawRowCheck10567 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form17 = rawRow10567 := by decide +kernel

theorem rowCheck10567 : row10567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10567 := by decide +kernel

theorem rowEval10567 (x : Key → ℝ) : Integer.Sparse.eval row10567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10567, Integer.Sparse.eval_collectBalanced, rawRowCheck10567]

theorem rawRowCheck10568 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form17 = rawRow10568 := by decide +kernel

theorem rowCheck10568 : row10568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10568 := by decide +kernel

theorem rowEval10568 (x : Key → ℝ) : Integer.Sparse.eval row10568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10568, Integer.Sparse.eval_collectBalanced, rawRowCheck10568]

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

theorem entryCheck19_17 : entry19_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_17 k)) := by decide +kernel

theorem rowsSound19_17 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval10559 x
  · exact rowEval10560 x
  · exact rowEval10561 x
  · exact rowEval10562 x
  · exact rowEval10563 x
  · exact rowEval10564 x
  · exact rowEval10565 x
  · exact rowEval10566 x
  · exact rowEval10567 x
  · exact rowEval10568 x

theorem entryEval19_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_17 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck19_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_17]

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

theorem rawRowCheck10674 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form17 = rawRow10674 := by decide +kernel

theorem rowCheck10674 : row10674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10674 := by decide +kernel

theorem rowEval10674 (x : Key → ℝ) : Integer.Sparse.eval row10674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form17) x := by
  rw [rowCheck10674, Integer.Sparse.eval_collectBalanced, rawRowCheck10674]

theorem rawRowCheck10675 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form17 = rawRow10675 := by decide +kernel

theorem rowCheck10675 : row10675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10675 := by decide +kernel

theorem rowEval10675 (x : Key → ℝ) : Integer.Sparse.eval row10675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10675, Integer.Sparse.eval_collectBalanced, rawRowCheck10675]

theorem rawRowCheck10676 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form17 = rawRow10676 := by decide +kernel

theorem rowCheck10676 : row10676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10676 := by decide +kernel

theorem rowEval10676 (x : Key → ℝ) : Integer.Sparse.eval row10676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10676, Integer.Sparse.eval_collectBalanced, rawRowCheck10676]

theorem rawRowCheck10677 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form17 = rawRow10677 := by decide +kernel

theorem rowCheck10677 : row10677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10677 := by decide +kernel

theorem rowEval10677 (x : Key → ℝ) : Integer.Sparse.eval row10677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10677, Integer.Sparse.eval_collectBalanced, rawRowCheck10677]

theorem rawRowCheck10678 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form17 = rawRow10678 := by decide +kernel

theorem rowCheck10678 : row10678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10678 := by decide +kernel

theorem rowEval10678 (x : Key → ℝ) : Integer.Sparse.eval row10678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10678, Integer.Sparse.eval_collectBalanced, rawRowCheck10678]

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

theorem entryCheck20_17 : entry20_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_17 k)) := by decide +kernel

theorem rowsSound20_17 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval10674 x
  · exact rowEval10675 x
  · exact rowEval10676 x
  · exact rowEval10677 x
  · exact rowEval10678 x

theorem entryEval20_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_17 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck20_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_17]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12080 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form17 = rawRow12080 := by decide +kernel

theorem rowCheck12080 : row12080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12080 := by decide +kernel

theorem rowEval12080 (x : Key → ℝ) : Integer.Sparse.eval row12080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12080, Integer.Sparse.eval_collectBalanced, rawRowCheck12080]

theorem rawRowCheck12081 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form17 = rawRow12081 := by decide +kernel

theorem rowCheck12081 : row12081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12081 := by decide +kernel

theorem rowEval12081 (x : Key → ℝ) : Integer.Sparse.eval row12081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12081, Integer.Sparse.eval_collectBalanced, rawRowCheck12081]

theorem rawRowCheck12082 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form17 = rawRow12082 := by decide +kernel

theorem rowCheck12082 : row12082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12082 := by decide +kernel

theorem rowEval12082 (x : Key → ℝ) : Integer.Sparse.eval row12082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12082, Integer.Sparse.eval_collectBalanced, rawRowCheck12082]

theorem rawRowCheck12083 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form17 = rawRow12083 := by decide +kernel

theorem rowCheck12083 : row12083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12083 := by decide +kernel

theorem rowEval12083 (x : Key → ℝ) : Integer.Sparse.eval row12083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12083, Integer.Sparse.eval_collectBalanced, rawRowCheck12083]

theorem rawRowCheck12084 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form17 = rawRow12084 := by decide +kernel

theorem rowCheck12084 : row12084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12084 := by decide +kernel

theorem rowEval12084 (x : Key → ℝ) : Integer.Sparse.eval row12084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12084, Integer.Sparse.eval_collectBalanced, rawRowCheck12084]

theorem rawRowCheck12085 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form17 = rawRow12085 := by decide +kernel

theorem rowCheck12085 : row12085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12085 := by decide +kernel

theorem rowEval12085 (x : Key → ℝ) : Integer.Sparse.eval row12085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12085, Integer.Sparse.eval_collectBalanced, rawRowCheck12085]

theorem rawRowCheck12086 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17 = rawRow12086 := by decide +kernel

theorem rowCheck12086 : row12086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12086 := by decide +kernel

theorem rowEval12086 (x : Key → ℝ) : Integer.Sparse.eval row12086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12086, Integer.Sparse.eval_collectBalanced, rawRowCheck12086]

theorem rawRowCheck12087 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17 = rawRow12087 := by decide +kernel

theorem rowCheck12087 : row12087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12087 := by decide +kernel

theorem rowEval12087 (x : Key → ℝ) : Integer.Sparse.eval row12087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12087, Integer.Sparse.eval_collectBalanced, rawRowCheck12087]

theorem rawRowCheck12088 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17 = rawRow12088 := by decide +kernel

theorem rowCheck12088 : row12088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12088 := by decide +kernel

theorem rowEval12088 (x : Key → ℝ) : Integer.Sparse.eval row12088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12088, Integer.Sparse.eval_collectBalanced, rawRowCheck12088]

theorem rawRowCheck12089 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17 = rawRow12089 := by decide +kernel

theorem rowCheck12089 : row12089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12089 := by decide +kernel

theorem rowEval12089 (x : Key → ℝ) : Integer.Sparse.eval row12089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12089, Integer.Sparse.eval_collectBalanced, rawRowCheck12089]

theorem rawRowCheck12090 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17 = rawRow12090 := by decide +kernel

theorem rowCheck12090 : row12090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12090 := by decide +kernel

theorem rowEval12090 (x : Key → ℝ) : Integer.Sparse.eval row12090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12090, Integer.Sparse.eval_collectBalanced, rawRowCheck12090]

theorem rawRowCheck12091 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17 = rawRow12091 := by decide +kernel

theorem rowCheck12091 : row12091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12091 := by decide +kernel

theorem rowEval12091 (x : Key → ℝ) : Integer.Sparse.eval row12091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12091, Integer.Sparse.eval_collectBalanced, rawRowCheck12091]

theorem rawRowCheck12092 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17 = rawRow12092 := by decide +kernel

theorem rowCheck12092 : row12092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12092 := by decide +kernel

theorem rowEval12092 (x : Key → ℝ) : Integer.Sparse.eval row12092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12092, Integer.Sparse.eval_collectBalanced, rawRowCheck12092]

theorem rawRowCheck12093 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17 = rawRow12093 := by decide +kernel

theorem rowCheck12093 : row12093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12093 := by decide +kernel

theorem rowEval12093 (x : Key → ℝ) : Integer.Sparse.eval row12093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12093, Integer.Sparse.eval_collectBalanced, rawRowCheck12093]

theorem rawRowCheck12094 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17 = rawRow12094 := by decide +kernel

theorem rowCheck12094 : row12094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12094 := by decide +kernel

theorem rowEval12094 (x : Key → ℝ) : Integer.Sparse.eval row12094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12094, Integer.Sparse.eval_collectBalanced, rawRowCheck12094]

theorem rawRowCheck12095 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17 = rawRow12095 := by decide +kernel

theorem rowCheck12095 : row12095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12095 := by decide +kernel

theorem rowEval12095 (x : Key → ℝ) : Integer.Sparse.eval row12095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12095, Integer.Sparse.eval_collectBalanced, rawRowCheck12095]

theorem rawRowCheck12096 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17 = rawRow12096 := by decide +kernel

theorem rowCheck12096 : row12096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12096 := by decide +kernel

theorem rowEval12096 (x : Key → ℝ) : Integer.Sparse.eval row12096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12096, Integer.Sparse.eval_collectBalanced, rawRowCheck12096]

theorem rawRowCheck12097 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17 = rawRow12097 := by decide +kernel

theorem rowCheck12097 : row12097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12097 := by decide +kernel

theorem rowEval12097 (x : Key → ℝ) : Integer.Sparse.eval row12097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12097, Integer.Sparse.eval_collectBalanced, rawRowCheck12097]

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

theorem entryCheck23_17 : entry23_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_17 k)) := by decide +kernel

theorem rowsSound23_17 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12080 x
  · exact rowEval12081 x
  · exact rowEval12082 x
  · exact rowEval12083 x
  · exact rowEval12084 x
  · exact rowEval12085 x
  · exact rowEval12086 x
  · exact rowEval12087 x
  · exact rowEval12088 x
  · exact rowEval12089 x
  · exact rowEval12090 x
  · exact rowEval12091 x
  · exact rowEval12092 x
  · exact rowEval12093 x
  · exact rowEval12094 x
  · exact rowEval12095 x
  · exact rowEval12096 x
  · exact rowEval12097 x

theorem entryEval23_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_17 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck23_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_17]

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

theorem rawRowCheck12291 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form17 = rawRow12291 := by decide +kernel

theorem rowCheck12291 : row12291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12291 := by decide +kernel

theorem rowEval12291 (x : Key → ℝ) : Integer.Sparse.eval row12291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12291, Integer.Sparse.eval_collectBalanced, rawRowCheck12291]

theorem rawRowCheck12292 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form17 = rawRow12292 := by decide +kernel

theorem rowCheck12292 : row12292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12292 := by decide +kernel

theorem rowEval12292 (x : Key → ℝ) : Integer.Sparse.eval row12292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12292, Integer.Sparse.eval_collectBalanced, rawRowCheck12292]

theorem rawRowCheck12293 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form17 = rawRow12293 := by decide +kernel

theorem rowCheck12293 : row12293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12293 := by decide +kernel

theorem rowEval12293 (x : Key → ℝ) : Integer.Sparse.eval row12293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12293, Integer.Sparse.eval_collectBalanced, rawRowCheck12293]

theorem rawRowCheck12294 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form17 = rawRow12294 := by decide +kernel

theorem rowCheck12294 : row12294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12294 := by decide +kernel

theorem rowEval12294 (x : Key → ℝ) : Integer.Sparse.eval row12294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12294, Integer.Sparse.eval_collectBalanced, rawRowCheck12294]

theorem rawRowCheck12295 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form17 = rawRow12295 := by decide +kernel

theorem rowCheck12295 : row12295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12295 := by decide +kernel

theorem rowEval12295 (x : Key → ℝ) : Integer.Sparse.eval row12295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12295, Integer.Sparse.eval_collectBalanced, rawRowCheck12295]

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

theorem entryCheck24_17 : entry24_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_17 k)) := by decide +kernel

theorem rowsSound24_17 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12291 x
  · exact rowEval12292 x
  · exact rowEval12293 x
  · exact rowEval12294 x
  · exact rowEval12295 x

theorem entryEval24_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_17 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck24_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_17]

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

theorem rawRowCheck12467 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form17 = rawRow12467 := by decide +kernel

theorem rowCheck12467 : row12467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12467 := by decide +kernel

theorem rowEval12467 (x : Key → ℝ) : Integer.Sparse.eval row12467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12467, Integer.Sparse.eval_collectBalanced, rawRowCheck12467]

theorem rawRowCheck12468 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form17 = rawRow12468 := by decide +kernel

theorem rowCheck12468 : row12468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12468 := by decide +kernel

theorem rowEval12468 (x : Key → ℝ) : Integer.Sparse.eval row12468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12468, Integer.Sparse.eval_collectBalanced, rawRowCheck12468]

theorem rawRowCheck12469 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form17 = rawRow12469 := by decide +kernel

theorem rowCheck12469 : row12469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12469 := by decide +kernel

theorem rowEval12469 (x : Key → ℝ) : Integer.Sparse.eval row12469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12469, Integer.Sparse.eval_collectBalanced, rawRowCheck12469]

theorem rawRowCheck12470 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form17 = rawRow12470 := by decide +kernel

theorem rowCheck12470 : row12470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12470 := by decide +kernel

theorem rowEval12470 (x : Key → ℝ) : Integer.Sparse.eval row12470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12470, Integer.Sparse.eval_collectBalanced, rawRowCheck12470]

theorem rawRowCheck12471 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form17 = rawRow12471 := by decide +kernel

theorem rowCheck12471 : row12471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12471 := by decide +kernel

theorem rowEval12471 (x : Key → ℝ) : Integer.Sparse.eval row12471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12471, Integer.Sparse.eval_collectBalanced, rawRowCheck12471]

theorem rawRowCheck12472 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form17 = rawRow12472 := by decide +kernel

theorem rowCheck12472 : row12472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12472 := by decide +kernel

theorem rowEval12472 (x : Key → ℝ) : Integer.Sparse.eval row12472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12472, Integer.Sparse.eval_collectBalanced, rawRowCheck12472]

theorem rawRowCheck12473 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form17 = rawRow12473 := by decide +kernel

theorem rowCheck12473 : row12473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12473 := by decide +kernel

theorem rowEval12473 (x : Key → ℝ) : Integer.Sparse.eval row12473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12473, Integer.Sparse.eval_collectBalanced, rawRowCheck12473]

theorem rawRowCheck12474 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form17 = rawRow12474 := by decide +kernel

theorem rowCheck12474 : row12474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12474 := by decide +kernel

theorem rowEval12474 (x : Key → ℝ) : Integer.Sparse.eval row12474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12474, Integer.Sparse.eval_collectBalanced, rawRowCheck12474]

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

theorem entryCheck25_17 : entry25_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_17 k)) := by decide +kernel

theorem rowsSound25_17 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12467 x
  · exact rowEval12468 x
  · exact rowEval12469 x
  · exact rowEval12470 x
  · exact rowEval12471 x
  · exact rowEval12472 x
  · exact rowEval12473 x
  · exact rowEval12474 x

theorem entryEval25_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_17 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck25_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_17]

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

theorem entryEvalRow17_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 17 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 17).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval17_0 B hB
  · exact entryEval17_1 B hB
  · exact entryEval17_2 B hB
  · exact entryEval17_3 B hB
  · exact entryEval17_4_e B hB
  · exact entryEval17_5_e B hB
  · exact entryEval17_6 B hB
  · exact entryEval17_7_e B hB
  · exact entryEval17_8_e B hB
  · exact entryEval17_9_e B hB
  · exact entryEval17_10_e B hB
  · exact entryEval17_11 B hB
  · exact entryEval17_12 B hB
  · exact entryEval17_13_e B hB
  · exact entryEval17_14 B hB
  · exact entryEval17_15_e B hB
  · exact entryEval17_16 B hB
  · exact entryEval17_17 B hB
  · exact (entryEval18_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_17_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_17_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_17_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e_oai
