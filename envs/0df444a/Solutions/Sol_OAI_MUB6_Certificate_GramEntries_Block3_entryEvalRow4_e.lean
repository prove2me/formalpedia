-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:18:00.974176+00:00
-- url     : https://prove2.me/submissions/55ff4f17-2320-4676-ab9c-9cc48f79ee71

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval17_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval5_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval8_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval9_4_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8549 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8549 := by decide +kernel

theorem rowCheck8549 : row8549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8549 := by decide +kernel

theorem rowEval8549 (x : Key → ℝ) : Integer.Sparse.eval row8549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8549, Integer.Sparse.eval_collectBalanced, rawRowCheck8549]

theorem rawRowCheck8550 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4 = rawRow8550 := by decide +kernel

theorem rowCheck8550 : row8550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8550 := by decide +kernel

theorem rowEval8550 (x : Key → ℝ) : Integer.Sparse.eval row8550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8550, Integer.Sparse.eval_collectBalanced, rawRowCheck8550]

theorem rawRowCheck8551 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4 = rawRow8551 := by decide +kernel

theorem rowCheck8551 : row8551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8551 := by decide +kernel

theorem rowEval8551 (x : Key → ℝ) : Integer.Sparse.eval row8551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8551, Integer.Sparse.eval_collectBalanced, rawRowCheck8551]

theorem rawRowCheck8552 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4 = rawRow8552 := by decide +kernel

theorem rowCheck8552 : row8552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8552 := by decide +kernel

theorem rowEval8552 (x : Key → ℝ) : Integer.Sparse.eval row8552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8552, Integer.Sparse.eval_collectBalanced, rawRowCheck8552]

theorem rawRowCheck8553 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow8553 := by decide +kernel

theorem rowCheck8553 : row8553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8553 := by decide +kernel

theorem rowEval8553 (x : Key → ℝ) : Integer.Sparse.eval row8553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8553, Integer.Sparse.eval_collectBalanced, rawRowCheck8553]

theorem rawRowCheck8554 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow8554 := by decide +kernel

theorem rowCheck8554 : row8554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8554 := by decide +kernel

theorem rowEval8554 (x : Key → ℝ) : Integer.Sparse.eval row8554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8554, Integer.Sparse.eval_collectBalanced, rawRowCheck8554]

theorem rawRowCheck8555 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow8555 := by decide +kernel

theorem rowCheck8555 : row8555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8555 := by decide +kernel

theorem rowEval8555 (x : Key → ℝ) : Integer.Sparse.eval row8555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8555, Integer.Sparse.eval_collectBalanced, rawRowCheck8555]

theorem rawRowCheck8556 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow8556 := by decide +kernel

theorem rowCheck8556 : row8556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8556 := by decide +kernel

theorem rowEval8556 (x : Key → ℝ) : Integer.Sparse.eval row8556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8556, Integer.Sparse.eval_collectBalanced, rawRowCheck8556]

theorem rawRowCheck8557 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow8557 := by decide +kernel

theorem rowCheck8557 : row8557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8557 := by decide +kernel

theorem rowEval8557 (x : Key → ℝ) : Integer.Sparse.eval row8557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8557, Integer.Sparse.eval_collectBalanced, rawRowCheck8557]

theorem rawRowCheck8558 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow8558 := by decide +kernel

theorem rowCheck8558 : row8558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8558 := by decide +kernel

theorem rowEval8558 (x : Key → ℝ) : Integer.Sparse.eval row8558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8558, Integer.Sparse.eval_collectBalanced, rawRowCheck8558]

theorem rawRowCheck8559 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form4 = rawRow8559 := by decide +kernel

theorem rowCheck8559 : row8559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8559 := by decide +kernel

theorem rowEval8559 (x : Key → ℝ) : Integer.Sparse.eval row8559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8559, Integer.Sparse.eval_collectBalanced, rawRowCheck8559]

theorem rawRowCheck8560 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form4 = rawRow8560 := by decide +kernel

theorem rowCheck8560 : row8560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8560 := by decide +kernel

theorem rowEval8560 (x : Key → ℝ) : Integer.Sparse.eval row8560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8560, Integer.Sparse.eval_collectBalanced, rawRowCheck8560]

theorem rawRowCheck8561 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form4 = rawRow8561 := by decide +kernel

theorem rowCheck8561 : row8561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8561 := by decide +kernel

theorem rowEval8561 (x : Key → ℝ) : Integer.Sparse.eval row8561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8561, Integer.Sparse.eval_collectBalanced, rawRowCheck8561]

theorem rawRowCheck8562 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form4 = rawRow8562 := by decide +kernel

theorem rowCheck8562 : row8562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8562 := by decide +kernel

theorem rowEval8562 (x : Key → ℝ) : Integer.Sparse.eval row8562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8562, Integer.Sparse.eval_collectBalanced, rawRowCheck8562]

theorem rawRowCheck8563 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form4 = rawRow8563 := by decide +kernel

theorem rowCheck8563 : row8563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8563 := by decide +kernel

theorem rowEval8563 (x : Key → ℝ) : Integer.Sparse.eval row8563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8563, Integer.Sparse.eval_collectBalanced, rawRowCheck8563]

theorem rawRowCheck8564 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form4 = rawRow8564 := by decide +kernel

theorem rowCheck8564 : row8564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8564 := by decide +kernel

theorem rowEval8564 (x : Key → ℝ) : Integer.Sparse.eval row8564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8564, Integer.Sparse.eval_collectBalanced, rawRowCheck8564]

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

theorem rawRowCheck8693 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form4 = rawRow8693 := by decide +kernel

theorem rowCheck8693 : row8693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8693 := by decide +kernel

theorem rowEval8693 (x : Key → ℝ) : Integer.Sparse.eval row8693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8693, Integer.Sparse.eval_collectBalanced, rawRowCheck8693]

theorem rawRowCheck8694 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form4 = rawRow8694 := by decide +kernel

theorem rowCheck8694 : row8694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8694 := by decide +kernel

theorem rowEval8694 (x : Key → ℝ) : Integer.Sparse.eval row8694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8694, Integer.Sparse.eval_collectBalanced, rawRowCheck8694]

theorem rawRowCheck8695 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form4 = rawRow8695 := by decide +kernel

theorem rowCheck8695 : row8695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8695 := by decide +kernel

theorem rowEval8695 (x : Key → ℝ) : Integer.Sparse.eval row8695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8695, Integer.Sparse.eval_collectBalanced, rawRowCheck8695]

theorem rawRowCheck8696 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8696 := by decide +kernel

theorem rowCheck8696 : row8696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8696 := by decide +kernel

theorem rowEval8696 (x : Key → ℝ) : Integer.Sparse.eval row8696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8696, Integer.Sparse.eval_collectBalanced, rawRowCheck8696]

theorem rawRowCheck8697 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8697 := by decide +kernel

theorem rowCheck8697 : row8697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8697 := by decide +kernel

theorem rowEval8697 (x : Key → ℝ) : Integer.Sparse.eval row8697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8697, Integer.Sparse.eval_collectBalanced, rawRowCheck8697]

theorem rawRowCheck8698 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow8698 := by decide +kernel

theorem rowCheck8698 : row8698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8698 := by decide +kernel

theorem rowEval8698 (x : Key → ℝ) : Integer.Sparse.eval row8698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8698, Integer.Sparse.eval_collectBalanced, rawRowCheck8698]

theorem rawRowCheck8699 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow8699 := by decide +kernel

theorem rowCheck8699 : row8699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8699 := by decide +kernel

theorem rowEval8699 (x : Key → ℝ) : Integer.Sparse.eval row8699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8699, Integer.Sparse.eval_collectBalanced, rawRowCheck8699]

theorem rawRowCheck8700 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow8700 := by decide +kernel

theorem rowCheck8700 : row8700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8700 := by decide +kernel

theorem rowEval8700 (x : Key → ℝ) : Integer.Sparse.eval row8700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck8700, Integer.Sparse.eval_collectBalanced, rawRowCheck8700]

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

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8549 x
  · exact rowEval8550 x
  · exact rowEval8551 x
  · exact rowEval8552 x
  · exact rowEval8553 x
  · exact rowEval8554 x
  · exact rowEval8555 x
  · exact rowEval8556 x
  · exact rowEval8557 x
  · exact rowEval8558 x
  · exact rowEval8559 x
  · exact rowEval8560 x
  · exact rowEval8561 x
  · exact rowEval8562 x
  · exact rowEval8563 x
  · exact rowEval8564 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

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

theorem rawRowCheck8773 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8773 := by decide +kernel

theorem rowCheck8773 : row8773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8773 := by decide +kernel

theorem rowEval8773 (x : Key → ℝ) : Integer.Sparse.eval row8773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8773, Integer.Sparse.eval_collectBalanced, rawRowCheck8773]

theorem rawRowCheck8774 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow8774 := by decide +kernel

theorem rowCheck8774 : row8774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8774 := by decide +kernel

theorem rowEval8774 (x : Key → ℝ) : Integer.Sparse.eval row8774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8774, Integer.Sparse.eval_collectBalanced, rawRowCheck8774]

theorem rawRowCheck8775 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow8775 := by decide +kernel

theorem rowCheck8775 : row8775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8775 := by decide +kernel

theorem rowEval8775 (x : Key → ℝ) : Integer.Sparse.eval row8775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8775, Integer.Sparse.eval_collectBalanced, rawRowCheck8775]

theorem rawRowCheck8776 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow8776 := by decide +kernel

theorem rowCheck8776 : row8776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8776 := by decide +kernel

theorem rowEval8776 (x : Key → ℝ) : Integer.Sparse.eval row8776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck8776, Integer.Sparse.eval_collectBalanced, rawRowCheck8776]

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

theorem entryCheck11_4 : entry11_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_4 k)) := by decide +kernel

theorem rowsSound11_4 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8693 x
  · exact rowEval8694 x
  · exact rowEval8695 x
  · exact rowEval8696 x
  · exact rowEval8697 x
  · exact rowEval8698 x
  · exact rowEval8699 x
  · exact rowEval8700 x

theorem entryEval11_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_4 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck11_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_4]

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

theorem rawRowCheck7494 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7494 := by decide +kernel

theorem rowCheck7494 : row7494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7494 := by decide +kernel

theorem rowEval7494 (x : Key → ℝ) : Integer.Sparse.eval row7494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7494, Integer.Sparse.eval_collectBalanced, rawRowCheck7494]

theorem rawRowCheck7495 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7495 := by decide +kernel

theorem rowCheck7495 : row7495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7495 := by decide +kernel

theorem rowEval7495 (x : Key → ℝ) : Integer.Sparse.eval row7495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7495, Integer.Sparse.eval_collectBalanced, rawRowCheck7495]

theorem rawRowCheck7496 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7496 := by decide +kernel

theorem rowCheck7496 : row7496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7496 := by decide +kernel

theorem rowEval7496 (x : Key → ℝ) : Integer.Sparse.eval row7496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7496, Integer.Sparse.eval_collectBalanced, rawRowCheck7496]

theorem rawRowCheck7497 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7497 := by decide +kernel

theorem rowCheck7497 : row7497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7497 := by decide +kernel

theorem rowEval7497 (x : Key → ℝ) : Integer.Sparse.eval row7497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7497, Integer.Sparse.eval_collectBalanced, rawRowCheck7497]

theorem rawRowCheck7498 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7498 := by decide +kernel

theorem rowCheck7498 : row7498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7498 := by decide +kernel

theorem rowEval7498 (x : Key → ℝ) : Integer.Sparse.eval row7498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7498, Integer.Sparse.eval_collectBalanced, rawRowCheck7498]

theorem rawRowCheck7499 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7499 := by decide +kernel

theorem rowCheck7499 : row7499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7499 := by decide +kernel

theorem rowEval7499 (x : Key → ℝ) : Integer.Sparse.eval row7499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7499, Integer.Sparse.eval_collectBalanced, rawRowCheck7499]

theorem rawRowCheck7500 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7500 := by decide +kernel

theorem rowCheck7500 : row7500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7500 := by decide +kernel

theorem rowEval7500 (x : Key → ℝ) : Integer.Sparse.eval row7500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7500, Integer.Sparse.eval_collectBalanced, rawRowCheck7500]

theorem rawRowCheck7501 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0 = rawRow7501 := by decide +kernel

theorem rowCheck7501 : row7501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7501 := by decide +kernel

theorem rowEval7501 (x : Key → ℝ) : Integer.Sparse.eval row7501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7501, Integer.Sparse.eval_collectBalanced, rawRowCheck7501]

theorem rawRowCheck7502 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0 = rawRow7502 := by decide +kernel

theorem rowCheck7502 : row7502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7502 := by decide +kernel

theorem rowEval7502 (x : Key → ℝ) : Integer.Sparse.eval row7502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7502, Integer.Sparse.eval_collectBalanced, rawRowCheck7502]

theorem rawRowCheck7503 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0 = rawRow7503 := by decide +kernel

theorem rowCheck7503 : row7503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7503 := by decide +kernel

theorem rowEval7503 (x : Key → ℝ) : Integer.Sparse.eval row7503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7503, Integer.Sparse.eval_collectBalanced, rawRowCheck7503]

theorem rawRowCheck7504 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0 = rawRow7504 := by decide +kernel

theorem rowCheck7504 : row7504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7504 := by decide +kernel

theorem rowEval7504 (x : Key → ℝ) : Integer.Sparse.eval row7504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7504, Integer.Sparse.eval_collectBalanced, rawRowCheck7504]

theorem rawRowCheck7505 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0 = rawRow7505 := by decide +kernel

theorem rowCheck7505 : row7505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7505 := by decide +kernel

theorem rowEval7505 (x : Key → ℝ) : Integer.Sparse.eval row7505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7505, Integer.Sparse.eval_collectBalanced, rawRowCheck7505]

theorem rawRowCheck7506 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0 = rawRow7506 := by decide +kernel

theorem rowCheck7506 : row7506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7506 := by decide +kernel

theorem rowEval7506 (x : Key → ℝ) : Integer.Sparse.eval row7506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7506, Integer.Sparse.eval_collectBalanced, rawRowCheck7506]

theorem rawRowCheck7507 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7507 := by decide +kernel

theorem rowCheck7507 : row7507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7507 := by decide +kernel

theorem rowEval7507 (x : Key → ℝ) : Integer.Sparse.eval row7507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7507, Integer.Sparse.eval_collectBalanced, rawRowCheck7507]

theorem rawRowCheck7508 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7508 := by decide +kernel

theorem rowCheck7508 : row7508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7508 := by decide +kernel

theorem rowEval7508 (x : Key → ℝ) : Integer.Sparse.eval row7508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7508, Integer.Sparse.eval_collectBalanced, rawRowCheck7508]

theorem rawRowCheck7509 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7509 := by decide +kernel

theorem rowCheck7509 : row7509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7509 := by decide +kernel

theorem rowEval7509 (x : Key → ℝ) : Integer.Sparse.eval row7509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7509, Integer.Sparse.eval_collectBalanced, rawRowCheck7509]

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

theorem rawRowCheck7542 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7542 := by decide +kernel

theorem rowCheck7542 : row7542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7542 := by decide +kernel

theorem rowEval7542 (x : Key → ℝ) : Integer.Sparse.eval row7542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7542, Integer.Sparse.eval_collectBalanced, rawRowCheck7542]

theorem rawRowCheck7543 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7543 := by decide +kernel

theorem rowCheck7543 : row7543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7543 := by decide +kernel

theorem rowEval7543 (x : Key → ℝ) : Integer.Sparse.eval row7543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7543, Integer.Sparse.eval_collectBalanced, rawRowCheck7543]

theorem rawRowCheck7544 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7544 := by decide +kernel

theorem rowCheck7544 : row7544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7544 := by decide +kernel

theorem rowEval7544 (x : Key → ℝ) : Integer.Sparse.eval row7544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7544, Integer.Sparse.eval_collectBalanced, rawRowCheck7544]

theorem rawRowCheck7545 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7545 := by decide +kernel

theorem rowCheck7545 : row7545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7545 := by decide +kernel

theorem rowEval7545 (x : Key → ℝ) : Integer.Sparse.eval row7545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7545, Integer.Sparse.eval_collectBalanced, rawRowCheck7545]

theorem rawRowCheck7546 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7546 := by decide +kernel

theorem rowCheck7546 : row7546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7546 := by decide +kernel

theorem rowEval7546 (x : Key → ℝ) : Integer.Sparse.eval row7546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7546, Integer.Sparse.eval_collectBalanced, rawRowCheck7546]

theorem rawRowCheck7547 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7547 := by decide +kernel

theorem rowCheck7547 : row7547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7547 := by decide +kernel

theorem rowEval7547 (x : Key → ℝ) : Integer.Sparse.eval row7547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7547, Integer.Sparse.eval_collectBalanced, rawRowCheck7547]

theorem rawRowCheck7548 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7548 := by decide +kernel

theorem rowCheck7548 : row7548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7548 := by decide +kernel

theorem rowEval7548 (x : Key → ℝ) : Integer.Sparse.eval row7548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7548, Integer.Sparse.eval_collectBalanced, rawRowCheck7548]

theorem rawRowCheck7549 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form3 = rawRow7549 := by decide +kernel

theorem rowCheck7549 : row7549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7549 := by decide +kernel

theorem rowEval7549 (x : Key → ℝ) : Integer.Sparse.eval row7549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7549, Integer.Sparse.eval_collectBalanced, rawRowCheck7549]

theorem rawRowCheck7550 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form3 = rawRow7550 := by decide +kernel

theorem rowCheck7550 : row7550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7550 := by decide +kernel

theorem rowEval7550 (x : Key → ℝ) : Integer.Sparse.eval row7550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7550, Integer.Sparse.eval_collectBalanced, rawRowCheck7550]

theorem rawRowCheck7551 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form3 = rawRow7551 := by decide +kernel

theorem rowCheck7551 : row7551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7551 := by decide +kernel

theorem rowEval7551 (x : Key → ℝ) : Integer.Sparse.eval row7551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7551, Integer.Sparse.eval_collectBalanced, rawRowCheck7551]

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

theorem rawRowCheck7552 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form3 = rawRow7552 := by decide +kernel

theorem rowCheck7552 : row7552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7552 := by decide +kernel

theorem rowEval7552 (x : Key → ℝ) : Integer.Sparse.eval row7552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7552, Integer.Sparse.eval_collectBalanced, rawRowCheck7552]

theorem rawRowCheck7553 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form3 = rawRow7553 := by decide +kernel

theorem rowCheck7553 : row7553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7553 := by decide +kernel

theorem rowEval7553 (x : Key → ℝ) : Integer.Sparse.eval row7553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7553, Integer.Sparse.eval_collectBalanced, rawRowCheck7553]

theorem rawRowCheck7554 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form3 = rawRow7554 := by decide +kernel

theorem rowCheck7554 : row7554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7554 := by decide +kernel

theorem rowEval7554 (x : Key → ℝ) : Integer.Sparse.eval row7554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7554, Integer.Sparse.eval_collectBalanced, rawRowCheck7554]

theorem rawRowCheck7555 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form3 = rawRow7555 := by decide +kernel

theorem rowCheck7555 : row7555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7555 := by decide +kernel

theorem rowEval7555 (x : Key → ℝ) : Integer.Sparse.eval row7555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7555, Integer.Sparse.eval_collectBalanced, rawRowCheck7555]

theorem rawRowCheck7556 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form3 = rawRow7556 := by decide +kernel

theorem rowCheck7556 : row7556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7556 := by decide +kernel

theorem rowEval7556 (x : Key → ℝ) : Integer.Sparse.eval row7556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7556, Integer.Sparse.eval_collectBalanced, rawRowCheck7556]

theorem rawRowCheck7557 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form3 = rawRow7557 := by decide +kernel

theorem rowCheck7557 : row7557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7557 := by decide +kernel

theorem rowEval7557 (x : Key → ℝ) : Integer.Sparse.eval row7557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7557, Integer.Sparse.eval_collectBalanced, rawRowCheck7557]

theorem rawRowCheck7558 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7558 := by decide +kernel

theorem rowCheck7558 : row7558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7558 := by decide +kernel

theorem rowEval7558 (x : Key → ℝ) : Integer.Sparse.eval row7558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7558, Integer.Sparse.eval_collectBalanced, rawRowCheck7558]

theorem rawRowCheck7559 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7559 := by decide +kernel

theorem rowCheck7559 : row7559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7559 := by decide +kernel

theorem rowEval7559 (x : Key → ℝ) : Integer.Sparse.eval row7559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7559, Integer.Sparse.eval_collectBalanced, rawRowCheck7559]

theorem rawRowCheck7560 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7560 := by decide +kernel

theorem rowCheck7560 : row7560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7560 := by decide +kernel

theorem rowEval7560 (x : Key → ℝ) : Integer.Sparse.eval row7560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7560, Integer.Sparse.eval_collectBalanced, rawRowCheck7560]

theorem rawRowCheck7561 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow7561 := by decide +kernel

theorem rowCheck7561 : row7561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7561 := by decide +kernel

theorem rowEval7561 (x : Key → ℝ) : Integer.Sparse.eval row7561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7561, Integer.Sparse.eval_collectBalanced, rawRowCheck7561]

theorem rawRowCheck7562 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7562 := by decide +kernel

theorem rowCheck7562 : row7562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7562 := by decide +kernel

theorem rowEval7562 (x : Key → ℝ) : Integer.Sparse.eval row7562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7562, Integer.Sparse.eval_collectBalanced, rawRowCheck7562]

theorem rawRowCheck7563 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7563 := by decide +kernel

theorem rowCheck7563 : row7563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7563 := by decide +kernel

theorem rowEval7563 (x : Key → ℝ) : Integer.Sparse.eval row7563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7563, Integer.Sparse.eval_collectBalanced, rawRowCheck7563]

theorem rawRowCheck7564 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7564 := by decide +kernel

theorem rowCheck7564 : row7564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7564 := by decide +kernel

theorem rowEval7564 (x : Key → ℝ) : Integer.Sparse.eval row7564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7564, Integer.Sparse.eval_collectBalanced, rawRowCheck7564]

theorem rawRowCheck7565 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form4 = rawRow7565 := by decide +kernel

theorem rowCheck7565 : row7565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7565 := by decide +kernel

theorem rowEval7565 (x : Key → ℝ) : Integer.Sparse.eval row7565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7565, Integer.Sparse.eval_collectBalanced, rawRowCheck7565]

theorem rawRowCheck7566 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form4 = rawRow7566 := by decide +kernel

theorem rowCheck7566 : row7566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7566 := by decide +kernel

theorem rowEval7566 (x : Key → ℝ) : Integer.Sparse.eval row7566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7566, Integer.Sparse.eval_collectBalanced, rawRowCheck7566]

theorem rawRowCheck7567 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form4 = rawRow7567 := by decide +kernel

theorem rowCheck7567 : row7567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7567 := by decide +kernel

theorem rowEval7567 (x : Key → ℝ) : Integer.Sparse.eval row7567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7567, Integer.Sparse.eval_collectBalanced, rawRowCheck7567]

theorem rawRowCheck7568 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form4 = rawRow7568 := by decide +kernel

theorem rowCheck7568 : row7568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7568 := by decide +kernel

theorem rowEval7568 (x : Key → ℝ) : Integer.Sparse.eval row7568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck7568, Integer.Sparse.eval_collectBalanced, rawRowCheck7568]

theorem rawRowCheck7569 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form4 = rawRow7569 := by decide +kernel

theorem rowCheck7569 : row7569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7569 := by decide +kernel

theorem rowEval7569 (x : Key → ℝ) : Integer.Sparse.eval row7569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7569, Integer.Sparse.eval_collectBalanced, rawRowCheck7569]

theorem rawRowCheck7570 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form4 = rawRow7570 := by decide +kernel

theorem rowCheck7570 : row7570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7570 := by decide +kernel

theorem rowEval7570 (x : Key → ℝ) : Integer.Sparse.eval row7570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck7570, Integer.Sparse.eval_collectBalanced, rawRowCheck7570]

theorem rawRowCheck7571 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form4 = rawRow7571 := by decide +kernel

theorem rowCheck7571 : row7571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7571 := by decide +kernel

theorem rowEval7571 (x : Key → ℝ) : Integer.Sparse.eval row7571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7571, Integer.Sparse.eval_collectBalanced, rawRowCheck7571]

theorem rawRowCheck7572 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form4 = rawRow7572 := by decide +kernel

theorem rowCheck7572 : row7572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7572 := by decide +kernel

theorem rowEval7572 (x : Key → ℝ) : Integer.Sparse.eval row7572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7572, Integer.Sparse.eval_collectBalanced, rawRowCheck7572]

theorem rawRowCheck7573 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form4 = rawRow7573 := by decide +kernel

theorem rowCheck7573 : row7573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7573 := by decide +kernel

theorem rowEval7573 (x : Key → ℝ) : Integer.Sparse.eval row7573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck7573, Integer.Sparse.eval_collectBalanced, rawRowCheck7573]

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

theorem rawRowCheck8905 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow8905 := by decide +kernel

theorem rowCheck8905 : row8905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8905 := by decide +kernel

theorem rowEval8905 (x : Key → ℝ) : Integer.Sparse.eval row8905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8905, Integer.Sparse.eval_collectBalanced, rawRowCheck8905]

theorem rawRowCheck8906 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow8906 := by decide +kernel

theorem rowCheck8906 : row8906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8906 := by decide +kernel

theorem rowEval8906 (x : Key → ℝ) : Integer.Sparse.eval row8906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8906, Integer.Sparse.eval_collectBalanced, rawRowCheck8906]

theorem rawRowCheck8907 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow8907 := by decide +kernel

theorem rowCheck8907 : row8907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8907 := by decide +kernel

theorem rowEval8907 (x : Key → ℝ) : Integer.Sparse.eval row8907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8907, Integer.Sparse.eval_collectBalanced, rawRowCheck8907]

theorem rawRowCheck8908 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8908 := by decide +kernel

theorem rowCheck8908 : row8908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8908 := by decide +kernel

theorem rowEval8908 (x : Key → ℝ) : Integer.Sparse.eval row8908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8908, Integer.Sparse.eval_collectBalanced, rawRowCheck8908]

theorem rawRowCheck8909 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form4 = rawRow8909 := by decide +kernel

theorem rowCheck8909 : row8909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8909 := by decide +kernel

theorem rowEval8909 (x : Key → ℝ) : Integer.Sparse.eval row8909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8909, Integer.Sparse.eval_collectBalanced, rawRowCheck8909]

theorem rawRowCheck8910 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form4 = rawRow8910 := by decide +kernel

theorem rowCheck8910 : row8910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8910 := by decide +kernel

theorem rowEval8910 (x : Key → ℝ) : Integer.Sparse.eval row8910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8910, Integer.Sparse.eval_collectBalanced, rawRowCheck8910]

theorem rawRowCheck8911 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form4 = rawRow8911 := by decide +kernel

theorem rowCheck8911 : row8911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8911 := by decide +kernel

theorem rowEval8911 (x : Key → ℝ) : Integer.Sparse.eval row8911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8911, Integer.Sparse.eval_collectBalanced, rawRowCheck8911]

theorem rawRowCheck8912 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form4 = rawRow8912 := by decide +kernel

theorem rowCheck8912 : row8912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8912 := by decide +kernel

theorem rowEval8912 (x : Key → ℝ) : Integer.Sparse.eval row8912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8912, Integer.Sparse.eval_collectBalanced, rawRowCheck8912]

theorem rawRowCheck8913 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form4 = rawRow8913 := by decide +kernel

theorem rowCheck8913 : row8913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8913 := by decide +kernel

theorem rowEval8913 (x : Key → ℝ) : Integer.Sparse.eval row8913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8913, Integer.Sparse.eval_collectBalanced, rawRowCheck8913]

theorem rawRowCheck8914 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form4 = rawRow8914 := by decide +kernel

theorem rowCheck8914 : row8914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8914 := by decide +kernel

theorem rowEval8914 (x : Key → ℝ) : Integer.Sparse.eval row8914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8914, Integer.Sparse.eval_collectBalanced, rawRowCheck8914]

theorem rawRowCheck8915 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form4 = rawRow8915 := by decide +kernel

theorem rowCheck8915 : row8915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8915 := by decide +kernel

theorem rowEval8915 (x : Key → ℝ) : Integer.Sparse.eval row8915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8915, Integer.Sparse.eval_collectBalanced, rawRowCheck8915]

theorem rawRowCheck8916 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form4 = rawRow8916 := by decide +kernel

theorem rowCheck8916 : row8916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8916 := by decide +kernel

theorem rowEval8916 (x : Key → ℝ) : Integer.Sparse.eval row8916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8916, Integer.Sparse.eval_collectBalanced, rawRowCheck8916]

theorem rawRowCheck8917 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form4 = rawRow8917 := by decide +kernel

theorem rowCheck8917 : row8917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8917 := by decide +kernel

theorem rowEval8917 (x : Key → ℝ) : Integer.Sparse.eval row8917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8917, Integer.Sparse.eval_collectBalanced, rawRowCheck8917]

theorem rawRowCheck8918 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow8918 := by decide +kernel

theorem rowCheck8918 : row8918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8918 := by decide +kernel

theorem rowEval8918 (x : Key → ℝ) : Integer.Sparse.eval row8918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8918, Integer.Sparse.eval_collectBalanced, rawRowCheck8918]

theorem rawRowCheck8919 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow8919 := by decide +kernel

theorem rowCheck8919 : row8919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8919 := by decide +kernel

theorem rowEval8919 (x : Key → ℝ) : Integer.Sparse.eval row8919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8919, Integer.Sparse.eval_collectBalanced, rawRowCheck8919]

theorem rawRowCheck8920 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow8920 := by decide +kernel

theorem rowCheck8920 : row8920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8920 := by decide +kernel

theorem rowEval8920 (x : Key → ℝ) : Integer.Sparse.eval row8920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8920, Integer.Sparse.eval_collectBalanced, rawRowCheck8920]

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

theorem entryCheck12_4 : entry12_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_4 k)) := by decide +kernel

theorem rowsSound12_4 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7558 x
  · exact rowEval7559 x
  · exact rowEval7560 x
  · exact rowEval7561 x
  · exact rowEval8773 x
  · exact rowEval8774 x
  · exact rowEval8775 x
  · exact rowEval8776 x

theorem entryEval12_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_4 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck12_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_4]

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

theorem rawRowCheck9085 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow9085 := by decide +kernel

theorem rowCheck9085 : row9085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9085 := by decide +kernel

theorem rowEval9085 (x : Key → ℝ) : Integer.Sparse.eval row9085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9085, Integer.Sparse.eval_collectBalanced, rawRowCheck9085]

theorem rawRowCheck9086 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow9086 := by decide +kernel

theorem rowCheck9086 : row9086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9086 := by decide +kernel

theorem rowEval9086 (x : Key → ℝ) : Integer.Sparse.eval row9086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9086, Integer.Sparse.eval_collectBalanced, rawRowCheck9086]

theorem rawRowCheck9087 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow9087 := by decide +kernel

theorem rowCheck9087 : row9087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9087 := by decide +kernel

theorem rowEval9087 (x : Key → ℝ) : Integer.Sparse.eval row9087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9087, Integer.Sparse.eval_collectBalanced, rawRowCheck9087]

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

theorem entryCheck13_4 : entry13_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_4 k)) := by decide +kernel

theorem rowsSound13_4 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8905 x
  · exact rowEval8906 x
  · exact rowEval8907 x
  · exact rowEval8908 x
  · exact rowEval8909 x
  · exact rowEval8910 x
  · exact rowEval8911 x
  · exact rowEval8912 x
  · exact rowEval8913 x
  · exact rowEval8914 x
  · exact rowEval8915 x
  · exact rowEval8916 x
  · exact rowEval8917 x
  · exact rowEval8918 x
  · exact rowEval8919 x
  · exact rowEval8920 x

theorem entryEval13_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_4 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck13_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_4]

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

theorem rawRowCheck9088 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9088 := by decide +kernel

theorem rowCheck9088 : row9088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9088 := by decide +kernel

theorem rowEval9088 (x : Key → ℝ) : Integer.Sparse.eval row9088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9088, Integer.Sparse.eval_collectBalanced, rawRowCheck9088]

theorem rawRowCheck9089 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9089 := by decide +kernel

theorem rowCheck9089 : row9089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9089 := by decide +kernel

theorem rowEval9089 (x : Key → ℝ) : Integer.Sparse.eval row9089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9089, Integer.Sparse.eval_collectBalanced, rawRowCheck9089]

theorem rawRowCheck9090 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow9090 := by decide +kernel

theorem rowCheck9090 : row9090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9090 := by decide +kernel

theorem rowEval9090 (x : Key → ℝ) : Integer.Sparse.eval row9090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9090, Integer.Sparse.eval_collectBalanced, rawRowCheck9090]

theorem rawRowCheck9091 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow9091 := by decide +kernel

theorem rowCheck9091 : row9091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9091 := by decide +kernel

theorem rowEval9091 (x : Key → ℝ) : Integer.Sparse.eval row9091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9091, Integer.Sparse.eval_collectBalanced, rawRowCheck9091]

theorem rawRowCheck9092 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow9092 := by decide +kernel

theorem rowCheck9092 : row9092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9092 := by decide +kernel

theorem rowEval9092 (x : Key → ℝ) : Integer.Sparse.eval row9092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9092, Integer.Sparse.eval_collectBalanced, rawRowCheck9092]

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

theorem entryCheck14_4 : entry14_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_4 k)) := by decide +kernel

theorem rowsSound14_4 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval9085 x
  · exact rowEval9086 x
  · exact rowEval9087 x
  · exact rowEval9088 x
  · exact rowEval9089 x
  · exact rowEval9090 x
  · exact rowEval9091 x
  · exact rowEval9092 x

theorem entryEval14_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_4 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck14_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_4]

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

theorem rawRowCheck9221 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form4 = rawRow9221 := by decide +kernel

theorem rowCheck9221 : row9221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9221 := by decide +kernel

theorem rowEval9221 (x : Key → ℝ) : Integer.Sparse.eval row9221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9221, Integer.Sparse.eval_collectBalanced, rawRowCheck9221]

theorem rawRowCheck9222 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form4 = rawRow9222 := by decide +kernel

theorem rowCheck9222 : row9222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9222 := by decide +kernel

theorem rowEval9222 (x : Key → ℝ) : Integer.Sparse.eval row9222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9222, Integer.Sparse.eval_collectBalanced, rawRowCheck9222]

theorem rawRowCheck9223 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form4 = rawRow9223 := by decide +kernel

theorem rowCheck9223 : row9223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9223 := by decide +kernel

theorem rowEval9223 (x : Key → ℝ) : Integer.Sparse.eval row9223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9223, Integer.Sparse.eval_collectBalanced, rawRowCheck9223]

theorem rawRowCheck9224 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form4 = rawRow9224 := by decide +kernel

theorem rowCheck9224 : row9224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9224 := by decide +kernel

theorem rowEval9224 (x : Key → ℝ) : Integer.Sparse.eval row9224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9224, Integer.Sparse.eval_collectBalanced, rawRowCheck9224]

theorem rawRowCheck9225 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form4 = rawRow9225 := by decide +kernel

theorem rowCheck9225 : row9225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9225 := by decide +kernel

theorem rowEval9225 (x : Key → ℝ) : Integer.Sparse.eval row9225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9225, Integer.Sparse.eval_collectBalanced, rawRowCheck9225]

theorem rawRowCheck9226 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form4 = rawRow9226 := by decide +kernel

theorem rowCheck9226 : row9226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9226 := by decide +kernel

theorem rowEval9226 (x : Key → ℝ) : Integer.Sparse.eval row9226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9226, Integer.Sparse.eval_collectBalanced, rawRowCheck9226]

theorem rawRowCheck9227 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form4 = rawRow9227 := by decide +kernel

theorem rowCheck9227 : row9227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9227 := by decide +kernel

theorem rowEval9227 (x : Key → ℝ) : Integer.Sparse.eval row9227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9227, Integer.Sparse.eval_collectBalanced, rawRowCheck9227]

theorem rawRowCheck9228 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form4 = rawRow9228 := by decide +kernel

theorem rowCheck9228 : row9228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9228 := by decide +kernel

theorem rowEval9228 (x : Key → ℝ) : Integer.Sparse.eval row9228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9228, Integer.Sparse.eval_collectBalanced, rawRowCheck9228]

theorem rawRowCheck9229 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form4 = rawRow9229 := by decide +kernel

theorem rowCheck9229 : row9229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9229 := by decide +kernel

theorem rowEval9229 (x : Key → ℝ) : Integer.Sparse.eval row9229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9229, Integer.Sparse.eval_collectBalanced, rawRowCheck9229]

theorem rawRowCheck9230 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form4 = rawRow9230 := by decide +kernel

theorem rowCheck9230 : row9230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9230 := by decide +kernel

theorem rowEval9230 (x : Key → ℝ) : Integer.Sparse.eval row9230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9230, Integer.Sparse.eval_collectBalanced, rawRowCheck9230]

theorem rawRowCheck9231 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form4 = rawRow9231 := by decide +kernel

theorem rowCheck9231 : row9231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9231 := by decide +kernel

theorem rowEval9231 (x : Key → ℝ) : Integer.Sparse.eval row9231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9231, Integer.Sparse.eval_collectBalanced, rawRowCheck9231]

theorem rawRowCheck9232 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form4 = rawRow9232 := by decide +kernel

theorem rowCheck9232 : row9232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9232 := by decide +kernel

theorem rowEval9232 (x : Key → ℝ) : Integer.Sparse.eval row9232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9232, Integer.Sparse.eval_collectBalanced, rawRowCheck9232]

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

theorem rawRowCheck9397 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9397 := by decide +kernel

theorem rowCheck9397 : row9397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9397 := by decide +kernel

theorem rowEval9397 (x : Key → ℝ) : Integer.Sparse.eval row9397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9397, Integer.Sparse.eval_collectBalanced, rawRowCheck9397]

theorem rawRowCheck9398 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form4 = rawRow9398 := by decide +kernel

theorem rowCheck9398 : row9398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9398 := by decide +kernel

theorem rowEval9398 (x : Key → ℝ) : Integer.Sparse.eval row9398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9398, Integer.Sparse.eval_collectBalanced, rawRowCheck9398]

theorem rawRowCheck9399 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form4 = rawRow9399 := by decide +kernel

theorem rowCheck9399 : row9399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9399 := by decide +kernel

theorem rowEval9399 (x : Key → ℝ) : Integer.Sparse.eval row9399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9399, Integer.Sparse.eval_collectBalanced, rawRowCheck9399]

theorem rawRowCheck9400 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form4 = rawRow9400 := by decide +kernel

theorem rowCheck9400 : row9400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9400 := by decide +kernel

theorem rowEval9400 (x : Key → ℝ) : Integer.Sparse.eval row9400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9400, Integer.Sparse.eval_collectBalanced, rawRowCheck9400]

theorem rawRowCheck9401 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9401 := by decide +kernel

theorem rowCheck9401 : row9401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9401 := by decide +kernel

theorem rowEval9401 (x : Key → ℝ) : Integer.Sparse.eval row9401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9401, Integer.Sparse.eval_collectBalanced, rawRowCheck9401]

theorem rawRowCheck9402 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4 = rawRow9402 := by decide +kernel

theorem rowCheck9402 : row9402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9402 := by decide +kernel

theorem rowEval9402 (x : Key → ℝ) : Integer.Sparse.eval row9402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9402, Integer.Sparse.eval_collectBalanced, rawRowCheck9402]

theorem rawRowCheck9403 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4 = rawRow9403 := by decide +kernel

theorem rowCheck9403 : row9403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9403 := by decide +kernel

theorem rowEval9403 (x : Key → ℝ) : Integer.Sparse.eval row9403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9403, Integer.Sparse.eval_collectBalanced, rawRowCheck9403]

theorem rawRowCheck9404 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4 = rawRow9404 := by decide +kernel

theorem rowCheck9404 : row9404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9404 := by decide +kernel

theorem rowEval9404 (x : Key → ℝ) : Integer.Sparse.eval row9404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9404, Integer.Sparse.eval_collectBalanced, rawRowCheck9404]

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

theorem entryCheck15_4 : entry15_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_4 k)) := by decide +kernel

theorem rowsSound15_4 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8693 x
  · exact rowEval8694 x
  · exact rowEval8695 x
  · exact rowEval8696 x
  · exact rowEval9221 x
  · exact rowEval9222 x
  · exact rowEval9223 x
  · exact rowEval9224 x
  · exact rowEval9225 x
  · exact rowEval9226 x
  · exact rowEval9227 x
  · exact rowEval9228 x
  · exact rowEval9229 x
  · exact rowEval9230 x
  · exact rowEval9231 x
  · exact rowEval9232 x

theorem entryEval15_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_4 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck15_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_4]

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

theorem entryCheck16_4 : entry16_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_4 k)) := by decide +kernel

theorem rowsSound16_4 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval9397 x
  · exact rowEval9398 x
  · exact rowEval9399 x
  · exact rowEval9400 x
  · exact rowEval9401 x
  · exact rowEval9402 x
  · exact rowEval9403 x
  · exact rowEval9404 x

theorem entryEval16_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_4 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck16_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_4]

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

theorem rawRowCheck10029 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4 = rawRow10029 := by decide +kernel

theorem rowCheck10029 : row10029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10029 := by decide +kernel

theorem rowEval10029 (x : Key → ℝ) : Integer.Sparse.eval row10029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10029, Integer.Sparse.eval_collectBalanced, rawRowCheck10029]

theorem rawRowCheck10030 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4 = rawRow10030 := by decide +kernel

theorem rowCheck10030 : row10030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10030 := by decide +kernel

theorem rowEval10030 (x : Key → ℝ) : Integer.Sparse.eval row10030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10030, Integer.Sparse.eval_collectBalanced, rawRowCheck10030]

theorem rawRowCheck10031 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4 = rawRow10031 := by decide +kernel

theorem rowCheck10031 : row10031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10031 := by decide +kernel

theorem rowEval10031 (x : Key → ℝ) : Integer.Sparse.eval row10031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10031, Integer.Sparse.eval_collectBalanced, rawRowCheck10031]

theorem rawRowCheck10032 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4 = rawRow10032 := by decide +kernel

theorem rowCheck10032 : row10032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10032 := by decide +kernel

theorem rowEval10032 (x : Key → ℝ) : Integer.Sparse.eval row10032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10032, Integer.Sparse.eval_collectBalanced, rawRowCheck10032]

theorem rawRowCheck10033 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4 = rawRow10033 := by decide +kernel

theorem rowCheck10033 : row10033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10033 := by decide +kernel

theorem rowEval10033 (x : Key → ℝ) : Integer.Sparse.eval row10033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10033, Integer.Sparse.eval_collectBalanced, rawRowCheck10033]

theorem rawRowCheck10034 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4 = rawRow10034 := by decide +kernel

theorem rowCheck10034 : row10034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10034 := by decide +kernel

theorem rowEval10034 (x : Key → ℝ) : Integer.Sparse.eval row10034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10034, Integer.Sparse.eval_collectBalanced, rawRowCheck10034]

theorem rawRowCheck10035 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4 = rawRow10035 := by decide +kernel

theorem rowCheck10035 : row10035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10035 := by decide +kernel

theorem rowEval10035 (x : Key → ℝ) : Integer.Sparse.eval row10035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10035, Integer.Sparse.eval_collectBalanced, rawRowCheck10035]

theorem rawRowCheck10036 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4 = rawRow10036 := by decide +kernel

theorem rowCheck10036 : row10036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10036 := by decide +kernel

theorem rowEval10036 (x : Key → ℝ) : Integer.Sparse.eval row10036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10036, Integer.Sparse.eval_collectBalanced, rawRowCheck10036]

theorem rawRowCheck10037 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4 = rawRow10037 := by decide +kernel

theorem rowCheck10037 : row10037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10037 := by decide +kernel

theorem rowEval10037 (x : Key → ℝ) : Integer.Sparse.eval row10037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10037, Integer.Sparse.eval_collectBalanced, rawRowCheck10037]

theorem rawRowCheck10038 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4 = rawRow10038 := by decide +kernel

theorem rowCheck10038 : row10038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10038 := by decide +kernel

theorem rowEval10038 (x : Key → ℝ) : Integer.Sparse.eval row10038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10038, Integer.Sparse.eval_collectBalanced, rawRowCheck10038]

theorem rawRowCheck10039 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4 = rawRow10039 := by decide +kernel

theorem rowCheck10039 : row10039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10039 := by decide +kernel

theorem rowEval10039 (x : Key → ℝ) : Integer.Sparse.eval row10039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10039, Integer.Sparse.eval_collectBalanced, rawRowCheck10039]

theorem rawRowCheck10040 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4 = rawRow10040 := by decide +kernel

theorem rowCheck10040 : row10040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10040 := by decide +kernel

theorem rowEval10040 (x : Key → ℝ) : Integer.Sparse.eval row10040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10040, Integer.Sparse.eval_collectBalanced, rawRowCheck10040]

theorem rawRowCheck10041 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form4 = rawRow10041 := by decide +kernel

theorem rowCheck10041 : row10041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10041 := by decide +kernel

theorem rowEval10041 (x : Key → ℝ) : Integer.Sparse.eval row10041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10041, Integer.Sparse.eval_collectBalanced, rawRowCheck10041]

theorem rawRowCheck10042 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form4 = rawRow10042 := by decide +kernel

theorem rowCheck10042 : row10042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10042 := by decide +kernel

theorem rowEval10042 (x : Key → ℝ) : Integer.Sparse.eval row10042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10042, Integer.Sparse.eval_collectBalanced, rawRowCheck10042]

theorem rawRowCheck10043 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form4 = rawRow10043 := by decide +kernel

theorem rowCheck10043 : row10043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10043 := by decide +kernel

theorem rowEval10043 (x : Key → ℝ) : Integer.Sparse.eval row10043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10043, Integer.Sparse.eval_collectBalanced, rawRowCheck10043]

theorem rawRowCheck10044 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form4 = rawRow10044 := by decide +kernel

theorem rowCheck10044 : row10044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10044 := by decide +kernel

theorem rowEval10044 (x : Key → ℝ) : Integer.Sparse.eval row10044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10044, Integer.Sparse.eval_collectBalanced, rawRowCheck10044]

theorem rawRowCheck10045 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form4 = rawRow10045 := by decide +kernel

theorem rowCheck10045 : row10045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10045 := by decide +kernel

theorem rowEval10045 (x : Key → ℝ) : Integer.Sparse.eval row10045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10045, Integer.Sparse.eval_collectBalanced, rawRowCheck10045]

theorem rawRowCheck10046 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form4 = rawRow10046 := by decide +kernel

theorem rowCheck10046 : row10046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10046 := by decide +kernel

theorem rowEval10046 (x : Key → ℝ) : Integer.Sparse.eval row10046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10046, Integer.Sparse.eval_collectBalanced, rawRowCheck10046]

theorem rawRowCheck10047 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form4 = rawRow10047 := by decide +kernel

theorem rowCheck10047 : row10047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10047 := by decide +kernel

theorem rowEval10047 (x : Key → ℝ) : Integer.Sparse.eval row10047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10047, Integer.Sparse.eval_collectBalanced, rawRowCheck10047]

theorem rawRowCheck10048 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form4 = rawRow10048 := by decide +kernel

theorem rowCheck10048 : row10048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10048 := by decide +kernel

theorem rowEval10048 (x : Key → ℝ) : Integer.Sparse.eval row10048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10048, Integer.Sparse.eval_collectBalanced, rawRowCheck10048]

theorem rawRowCheck10049 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form4 = rawRow10049 := by decide +kernel

theorem rowCheck10049 : row10049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10049 := by decide +kernel

theorem rowEval10049 (x : Key → ℝ) : Integer.Sparse.eval row10049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10049, Integer.Sparse.eval_collectBalanced, rawRowCheck10049]

theorem rawRowCheck10050 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form4 = rawRow10050 := by decide +kernel

theorem rowCheck10050 : row10050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10050 := by decide +kernel

theorem rowEval10050 (x : Key → ℝ) : Integer.Sparse.eval row10050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10050, Integer.Sparse.eval_collectBalanced, rawRowCheck10050]

theorem rawRowCheck10051 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form4 = rawRow10051 := by decide +kernel

theorem rowCheck10051 : row10051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10051 := by decide +kernel

theorem rowEval10051 (x : Key → ℝ) : Integer.Sparse.eval row10051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10051, Integer.Sparse.eval_collectBalanced, rawRowCheck10051]

theorem rawRowCheck10052 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form4 = rawRow10052 := by decide +kernel

theorem rowCheck10052 : row10052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10052 := by decide +kernel

theorem rowEval10052 (x : Key → ℝ) : Integer.Sparse.eval row10052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10052, Integer.Sparse.eval_collectBalanced, rawRowCheck10052]

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

theorem rawRowCheck10429 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form4 = rawRow10429 := by decide +kernel

theorem rowCheck10429 : row10429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10429 := by decide +kernel

theorem rowEval10429 (x : Key → ℝ) : Integer.Sparse.eval row10429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10429, Integer.Sparse.eval_collectBalanced, rawRowCheck10429]

theorem rawRowCheck10430 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form4 = rawRow10430 := by decide +kernel

theorem rowCheck10430 : row10430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10430 := by decide +kernel

theorem rowEval10430 (x : Key → ℝ) : Integer.Sparse.eval row10430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10430, Integer.Sparse.eval_collectBalanced, rawRowCheck10430]

theorem rawRowCheck10431 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form4 = rawRow10431 := by decide +kernel

theorem rowCheck10431 : row10431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10431 := by decide +kernel

theorem rowEval10431 (x : Key → ℝ) : Integer.Sparse.eval row10431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10431, Integer.Sparse.eval_collectBalanced, rawRowCheck10431]

theorem rawRowCheck10432 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form4 = rawRow10432 := by decide +kernel

theorem rowCheck10432 : row10432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10432 := by decide +kernel

theorem rowEval10432 (x : Key → ℝ) : Integer.Sparse.eval row10432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10432, Integer.Sparse.eval_collectBalanced, rawRowCheck10432]

theorem rawRowCheck10433 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form4 = rawRow10433 := by decide +kernel

theorem rowCheck10433 : row10433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10433 := by decide +kernel

theorem rowEval10433 (x : Key → ℝ) : Integer.Sparse.eval row10433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10433, Integer.Sparse.eval_collectBalanced, rawRowCheck10433]

theorem rawRowCheck10434 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form4 = rawRow10434 := by decide +kernel

theorem rowCheck10434 : row10434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10434 := by decide +kernel

theorem rowEval10434 (x : Key → ℝ) : Integer.Sparse.eval row10434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10434, Integer.Sparse.eval_collectBalanced, rawRowCheck10434]

theorem rawRowCheck10435 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form4 = rawRow10435 := by decide +kernel

theorem rowCheck10435 : row10435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10435 := by decide +kernel

theorem rowEval10435 (x : Key → ℝ) : Integer.Sparse.eval row10435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10435, Integer.Sparse.eval_collectBalanced, rawRowCheck10435]

theorem rawRowCheck10436 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form4 = rawRow10436 := by decide +kernel

theorem rowCheck10436 : row10436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10436 := by decide +kernel

theorem rowEval10436 (x : Key → ℝ) : Integer.Sparse.eval row10436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10436, Integer.Sparse.eval_collectBalanced, rawRowCheck10436]

theorem rawRowCheck10437 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form4 = rawRow10437 := by decide +kernel

theorem rowCheck10437 : row10437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10437 := by decide +kernel

theorem rowEval10437 (x : Key → ℝ) : Integer.Sparse.eval row10437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10437, Integer.Sparse.eval_collectBalanced, rawRowCheck10437]

theorem rawRowCheck10438 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form4 = rawRow10438 := by decide +kernel

theorem rowCheck10438 : row10438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10438 := by decide +kernel

theorem rowEval10438 (x : Key → ℝ) : Integer.Sparse.eval row10438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10438, Integer.Sparse.eval_collectBalanced, rawRowCheck10438]

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

theorem entryCheck18_4 : entry18_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_4 k)) := by decide +kernel

theorem rowsSound18_4 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval10029 x
  · exact rowEval10030 x
  · exact rowEval10031 x
  · exact rowEval10032 x
  · exact rowEval10033 x
  · exact rowEval10034 x
  · exact rowEval10035 x
  · exact rowEval10036 x
  · exact rowEval10037 x
  · exact rowEval10038 x
  · exact rowEval10039 x
  · exact rowEval10040 x
  · exact rowEval10041 x
  · exact rowEval10042 x
  · exact rowEval10043 x
  · exact rowEval10044 x
  · exact rowEval10045 x
  · exact rowEval10046 x
  · exact rowEval10047 x
  · exact rowEval10048 x
  · exact rowEval10049 x
  · exact rowEval10050 x
  · exact rowEval10051 x
  · exact rowEval10052 x

theorem entryEval18_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_4 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck18_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_4]

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

theorem rawRowCheck10609 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow10609 := by decide +kernel

theorem rowCheck10609 : row10609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10609 := by decide +kernel

theorem rowEval10609 (x : Key → ℝ) : Integer.Sparse.eval row10609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10609, Integer.Sparse.eval_collectBalanced, rawRowCheck10609]

theorem rawRowCheck10610 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow10610 := by decide +kernel

theorem rowCheck10610 : row10610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10610 := by decide +kernel

theorem rowEval10610 (x : Key → ℝ) : Integer.Sparse.eval row10610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10610, Integer.Sparse.eval_collectBalanced, rawRowCheck10610]

theorem rawRowCheck10611 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow10611 := by decide +kernel

theorem rowCheck10611 : row10611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10611 := by decide +kernel

theorem rowEval10611 (x : Key → ℝ) : Integer.Sparse.eval row10611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10611, Integer.Sparse.eval_collectBalanced, rawRowCheck10611]

theorem rawRowCheck10612 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow10612 := by decide +kernel

theorem rowCheck10612 : row10612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10612 := by decide +kernel

theorem rowEval10612 (x : Key → ℝ) : Integer.Sparse.eval row10612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10612, Integer.Sparse.eval_collectBalanced, rawRowCheck10612]

theorem rawRowCheck10613 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form4 = rawRow10613 := by decide +kernel

theorem rowCheck10613 : row10613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10613 := by decide +kernel

theorem rowEval10613 (x : Key → ℝ) : Integer.Sparse.eval row10613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10613, Integer.Sparse.eval_collectBalanced, rawRowCheck10613]

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

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval10429 x
  · exact rowEval10430 x
  · exact rowEval10431 x
  · exact rowEval10432 x
  · exact rowEval10433 x
  · exact rowEval10434 x
  · exact rowEval10435 x
  · exact rowEval10436 x
  · exact rowEval10437 x
  · exact rowEval10438 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

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

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval10609 x
  · exact rowEval10610 x
  · exact rowEval10611 x
  · exact rowEval10612 x
  · exact rowEval10613 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

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

theorem rawRowCheck11846 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form4 = rawRow11846 := by decide +kernel

theorem rowCheck11846 : row11846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11846 := by decide +kernel

theorem rowEval11846 (x : Key → ℝ) : Integer.Sparse.eval row11846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11846, Integer.Sparse.eval_collectBalanced, rawRowCheck11846]

theorem rawRowCheck11847 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form4 = rawRow11847 := by decide +kernel

theorem rowCheck11847 : row11847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11847 := by decide +kernel

theorem rowEval11847 (x : Key → ℝ) : Integer.Sparse.eval row11847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11847, Integer.Sparse.eval_collectBalanced, rawRowCheck11847]

theorem rawRowCheck11848 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form4 = rawRow11848 := by decide +kernel

theorem rowCheck11848 : row11848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11848 := by decide +kernel

theorem rowEval11848 (x : Key → ℝ) : Integer.Sparse.eval row11848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11848, Integer.Sparse.eval_collectBalanced, rawRowCheck11848]

theorem rawRowCheck11849 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form4 = rawRow11849 := by decide +kernel

theorem rowCheck11849 : row11849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11849 := by decide +kernel

theorem rowEval11849 (x : Key → ℝ) : Integer.Sparse.eval row11849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11849, Integer.Sparse.eval_collectBalanced, rawRowCheck11849]

theorem rawRowCheck11850 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form4 = rawRow11850 := by decide +kernel

theorem rowCheck11850 : row11850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11850 := by decide +kernel

theorem rowEval11850 (x : Key → ℝ) : Integer.Sparse.eval row11850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11850, Integer.Sparse.eval_collectBalanced, rawRowCheck11850]

theorem rawRowCheck11851 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form4 = rawRow11851 := by decide +kernel

theorem rowCheck11851 : row11851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11851 := by decide +kernel

theorem rowEval11851 (x : Key → ℝ) : Integer.Sparse.eval row11851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11851, Integer.Sparse.eval_collectBalanced, rawRowCheck11851]

theorem rawRowCheck11852 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4 = rawRow11852 := by decide +kernel

theorem rowCheck11852 : row11852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11852 := by decide +kernel

theorem rowEval11852 (x : Key → ℝ) : Integer.Sparse.eval row11852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11852, Integer.Sparse.eval_collectBalanced, rawRowCheck11852]

theorem rawRowCheck11853 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4 = rawRow11853 := by decide +kernel

theorem rowCheck11853 : row11853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11853 := by decide +kernel

theorem rowEval11853 (x : Key → ℝ) : Integer.Sparse.eval row11853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11853, Integer.Sparse.eval_collectBalanced, rawRowCheck11853]

theorem rawRowCheck11854 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4 = rawRow11854 := by decide +kernel

theorem rowCheck11854 : row11854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11854 := by decide +kernel

theorem rowEval11854 (x : Key → ℝ) : Integer.Sparse.eval row11854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11854, Integer.Sparse.eval_collectBalanced, rawRowCheck11854]

theorem rawRowCheck11855 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4 = rawRow11855 := by decide +kernel

theorem rowCheck11855 : row11855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11855 := by decide +kernel

theorem rowEval11855 (x : Key → ℝ) : Integer.Sparse.eval row11855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11855, Integer.Sparse.eval_collectBalanced, rawRowCheck11855]

theorem rawRowCheck11856 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4 = rawRow11856 := by decide +kernel

theorem rowCheck11856 : row11856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11856 := by decide +kernel

theorem rowEval11856 (x : Key → ℝ) : Integer.Sparse.eval row11856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11856, Integer.Sparse.eval_collectBalanced, rawRowCheck11856]

theorem rawRowCheck11857 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4 = rawRow11857 := by decide +kernel

theorem rowCheck11857 : row11857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11857 := by decide +kernel

theorem rowEval11857 (x : Key → ℝ) : Integer.Sparse.eval row11857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11857, Integer.Sparse.eval_collectBalanced, rawRowCheck11857]

theorem rawRowCheck11858 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4 = rawRow11858 := by decide +kernel

theorem rowCheck11858 : row11858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11858 := by decide +kernel

theorem rowEval11858 (x : Key → ℝ) : Integer.Sparse.eval row11858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11858, Integer.Sparse.eval_collectBalanced, rawRowCheck11858]

theorem rawRowCheck11859 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4 = rawRow11859 := by decide +kernel

theorem rowCheck11859 : row11859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11859 := by decide +kernel

theorem rowEval11859 (x : Key → ℝ) : Integer.Sparse.eval row11859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11859, Integer.Sparse.eval_collectBalanced, rawRowCheck11859]

theorem rawRowCheck11860 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4 = rawRow11860 := by decide +kernel

theorem rowCheck11860 : row11860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11860 := by decide +kernel

theorem rowEval11860 (x : Key → ℝ) : Integer.Sparse.eval row11860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11860, Integer.Sparse.eval_collectBalanced, rawRowCheck11860]

theorem rawRowCheck11861 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4 = rawRow11861 := by decide +kernel

theorem rowCheck11861 : row11861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11861 := by decide +kernel

theorem rowEval11861 (x : Key → ℝ) : Integer.Sparse.eval row11861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11861, Integer.Sparse.eval_collectBalanced, rawRowCheck11861]

theorem rawRowCheck11862 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4 = rawRow11862 := by decide +kernel

theorem rowCheck11862 : row11862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11862 := by decide +kernel

theorem rowEval11862 (x : Key → ℝ) : Integer.Sparse.eval row11862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11862, Integer.Sparse.eval_collectBalanced, rawRowCheck11862]

theorem rawRowCheck11863 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4 = rawRow11863 := by decide +kernel

theorem rowCheck11863 : row11863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11863 := by decide +kernel

theorem rowEval11863 (x : Key → ℝ) : Integer.Sparse.eval row11863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck11863, Integer.Sparse.eval_collectBalanced, rawRowCheck11863]

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

theorem rawRowCheck12226 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form4 = rawRow12226 := by decide +kernel

theorem rowCheck12226 : row12226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12226 := by decide +kernel

theorem rowEval12226 (x : Key → ℝ) : Integer.Sparse.eval row12226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12226, Integer.Sparse.eval_collectBalanced, rawRowCheck12226]

theorem rawRowCheck12227 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow12227 := by decide +kernel

theorem rowCheck12227 : row12227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12227 := by decide +kernel

theorem rowEval12227 (x : Key → ℝ) : Integer.Sparse.eval row12227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12227, Integer.Sparse.eval_collectBalanced, rawRowCheck12227]

theorem rawRowCheck12228 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form4 = rawRow12228 := by decide +kernel

theorem rowCheck12228 : row12228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12228 := by decide +kernel

theorem rowEval12228 (x : Key → ℝ) : Integer.Sparse.eval row12228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12228, Integer.Sparse.eval_collectBalanced, rawRowCheck12228]

theorem rawRowCheck12229 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form4 = rawRow12229 := by decide +kernel

theorem rowCheck12229 : row12229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12229 := by decide +kernel

theorem rowEval12229 (x : Key → ℝ) : Integer.Sparse.eval row12229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12229, Integer.Sparse.eval_collectBalanced, rawRowCheck12229]

theorem rawRowCheck12230 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form4 = rawRow12230 := by decide +kernel

theorem rowCheck12230 : row12230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12230 := by decide +kernel

theorem rowEval12230 (x : Key → ℝ) : Integer.Sparse.eval row12230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12230, Integer.Sparse.eval_collectBalanced, rawRowCheck12230]

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

theorem entryCheck23_4 : entry23_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_4 k)) := by decide +kernel

theorem rowsSound23_4 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval11846 x
  · exact rowEval11847 x
  · exact rowEval11848 x
  · exact rowEval11849 x
  · exact rowEval11850 x
  · exact rowEval11851 x
  · exact rowEval11852 x
  · exact rowEval11853 x
  · exact rowEval11854 x
  · exact rowEval11855 x
  · exact rowEval11856 x
  · exact rowEval11857 x
  · exact rowEval11858 x
  · exact rowEval11859 x
  · exact rowEval11860 x
  · exact rowEval11861 x
  · exact rowEval11862 x
  · exact rowEval11863 x

theorem entryEval23_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_4 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck23_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_4]

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

theorem rawRowCheck12363 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form4 = rawRow12363 := by decide +kernel

theorem rowCheck12363 : row12363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12363 := by decide +kernel

theorem rowEval12363 (x : Key → ℝ) : Integer.Sparse.eval row12363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12363, Integer.Sparse.eval_collectBalanced, rawRowCheck12363]

theorem rawRowCheck12364 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form4 = rawRow12364 := by decide +kernel

theorem rowCheck12364 : row12364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12364 := by decide +kernel

theorem rowEval12364 (x : Key → ℝ) : Integer.Sparse.eval row12364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12364, Integer.Sparse.eval_collectBalanced, rawRowCheck12364]

theorem rawRowCheck12365 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form4 = rawRow12365 := by decide +kernel

theorem rowCheck12365 : row12365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12365 := by decide +kernel

theorem rowEval12365 (x : Key → ℝ) : Integer.Sparse.eval row12365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12365, Integer.Sparse.eval_collectBalanced, rawRowCheck12365]

theorem rawRowCheck12366 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form4 = rawRow12366 := by decide +kernel

theorem rowCheck12366 : row12366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12366 := by decide +kernel

theorem rowEval12366 (x : Key → ℝ) : Integer.Sparse.eval row12366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12366, Integer.Sparse.eval_collectBalanced, rawRowCheck12366]

theorem rawRowCheck12367 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form4 = rawRow12367 := by decide +kernel

theorem rowCheck12367 : row12367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12367 := by decide +kernel

theorem rowEval12367 (x : Key → ℝ) : Integer.Sparse.eval row12367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12367, Integer.Sparse.eval_collectBalanced, rawRowCheck12367]

theorem rawRowCheck12368 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form4 = rawRow12368 := by decide +kernel

theorem rowCheck12368 : row12368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12368 := by decide +kernel

theorem rowEval12368 (x : Key → ℝ) : Integer.Sparse.eval row12368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12368, Integer.Sparse.eval_collectBalanced, rawRowCheck12368]

theorem rawRowCheck12369 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form4 = rawRow12369 := by decide +kernel

theorem rowCheck12369 : row12369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12369 := by decide +kernel

theorem rowEval12369 (x : Key → ℝ) : Integer.Sparse.eval row12369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12369, Integer.Sparse.eval_collectBalanced, rawRowCheck12369]

theorem rawRowCheck12370 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form4 = rawRow12370 := by decide +kernel

theorem rowCheck12370 : row12370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12370 := by decide +kernel

theorem rowEval12370 (x : Key → ℝ) : Integer.Sparse.eval row12370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12370, Integer.Sparse.eval_collectBalanced, rawRowCheck12370]

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

theorem entryCheck24_4 : entry24_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_4 k)) := by decide +kernel

theorem rowsSound24_4 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval12226 x
  · exact rowEval12227 x
  · exact rowEval12228 x
  · exact rowEval12229 x
  · exact rowEval12230 x

theorem entryEval24_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_4 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck24_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_4]

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

theorem entryCheck25_4 : entry25_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_4 k)) := by decide +kernel

theorem rowsSound25_4 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval12363 x
  · exact rowEval12364 x
  · exact rowEval12365 x
  · exact rowEval12366 x
  · exact rowEval12367 x
  · exact rowEval12368 x
  · exact rowEval12369 x
  · exact rowEval12370 x

theorem entryEval25_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_4 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck25_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_4]

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

theorem rawRowCheck12635 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form4 = rawRow12635 := by decide +kernel

theorem rowCheck12635 : row12635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12635 := by decide +kernel

theorem rowEval12635 (x : Key → ℝ) : Integer.Sparse.eval row12635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12635, Integer.Sparse.eval_collectBalanced, rawRowCheck12635]

theorem rawRowCheck12636 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form4 = rawRow12636 := by decide +kernel

theorem rowCheck12636 : row12636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12636 := by decide +kernel

theorem rowEval12636 (x : Key → ℝ) : Integer.Sparse.eval row12636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12636, Integer.Sparse.eval_collectBalanced, rawRowCheck12636]

theorem rawRowCheck12637 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form4 = rawRow12637 := by decide +kernel

theorem rowCheck12637 : row12637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12637 := by decide +kernel

theorem rowEval12637 (x : Key → ℝ) : Integer.Sparse.eval row12637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12637, Integer.Sparse.eval_collectBalanced, rawRowCheck12637]

theorem rawRowCheck12638 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form4 = rawRow12638 := by decide +kernel

theorem rowCheck12638 : row12638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12638 := by decide +kernel

theorem rowEval12638 (x : Key → ℝ) : Integer.Sparse.eval row12638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12638, Integer.Sparse.eval_collectBalanced, rawRowCheck12638]

theorem rawRowCheck12639 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form4 = rawRow12639 := by decide +kernel

theorem rowCheck12639 : row12639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12639 := by decide +kernel

theorem rowEval12639 (x : Key → ℝ) : Integer.Sparse.eval row12639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12639, Integer.Sparse.eval_collectBalanced, rawRowCheck12639]

theorem rawRowCheck12640 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form4 = rawRow12640 := by decide +kernel

theorem rowCheck12640 : row12640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12640 := by decide +kernel

theorem rowEval12640 (x : Key → ℝ) : Integer.Sparse.eval row12640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12640, Integer.Sparse.eval_collectBalanced, rawRowCheck12640]

theorem rawRowCheck12641 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form4 = rawRow12641 := by decide +kernel

theorem rowCheck12641 : row12641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12641 := by decide +kernel

theorem rowEval12641 (x : Key → ℝ) : Integer.Sparse.eval row12641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12641, Integer.Sparse.eval_collectBalanced, rawRowCheck12641]

theorem rawRowCheck12642 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form4 = rawRow12642 := by decide +kernel

theorem rowCheck12642 : row12642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12642 := by decide +kernel

theorem rowEval12642 (x : Key → ℝ) : Integer.Sparse.eval row12642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12642, Integer.Sparse.eval_collectBalanced, rawRowCheck12642]

theorem rawRowCheck12643 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form4 = rawRow12643 := by decide +kernel

theorem rowCheck12643 : row12643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12643 := by decide +kernel

theorem rowEval12643 (x : Key → ℝ) : Integer.Sparse.eval row12643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12643, Integer.Sparse.eval_collectBalanced, rawRowCheck12643]

theorem rawRowCheck12644 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form4 = rawRow12644 := by decide +kernel

theorem rowCheck12644 : row12644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12644 := by decide +kernel

theorem rowEval12644 (x : Key → ℝ) : Integer.Sparse.eval row12644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12644, Integer.Sparse.eval_collectBalanced, rawRowCheck12644]

theorem rawRowCheck12645 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form4 = rawRow12645 := by decide +kernel

theorem rowCheck12645 : row12645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12645 := by decide +kernel

theorem rowEval12645 (x : Key → ℝ) : Integer.Sparse.eval row12645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12645, Integer.Sparse.eval_collectBalanced, rawRowCheck12645]

theorem rawRowCheck12646 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form4 = rawRow12646 := by decide +kernel

theorem rowCheck12646 : row12646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12646 := by decide +kernel

theorem rowEval12646 (x : Key → ℝ) : Integer.Sparse.eval row12646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12646, Integer.Sparse.eval_collectBalanced, rawRowCheck12646]

theorem rawRowCheck12647 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form4 = rawRow12647 := by decide +kernel

theorem rowCheck12647 : row12647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12647 := by decide +kernel

theorem rowEval12647 (x : Key → ℝ) : Integer.Sparse.eval row12647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12647, Integer.Sparse.eval_collectBalanced, rawRowCheck12647]

theorem rawRowCheck12648 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form4 = rawRow12648 := by decide +kernel

theorem rowCheck12648 : row12648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12648 := by decide +kernel

theorem rowEval12648 (x : Key → ℝ) : Integer.Sparse.eval row12648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12648, Integer.Sparse.eval_collectBalanced, rawRowCheck12648]

theorem rawRowCheck12649 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form4 = rawRow12649 := by decide +kernel

theorem rowCheck12649 : row12649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12649 := by decide +kernel

theorem rowEval12649 (x : Key → ℝ) : Integer.Sparse.eval row12649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12649, Integer.Sparse.eval_collectBalanced, rawRowCheck12649]

theorem rawRowCheck12650 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form4 = rawRow12650 := by decide +kernel

theorem rowCheck12650 : row12650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12650 := by decide +kernel

theorem rowEval12650 (x : Key → ℝ) : Integer.Sparse.eval row12650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12650, Integer.Sparse.eval_collectBalanced, rawRowCheck12650]

theorem rawRowCheck12651 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form4 = rawRow12651 := by decide +kernel

theorem rowCheck12651 : row12651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12651 := by decide +kernel

theorem rowEval12651 (x : Key → ℝ) : Integer.Sparse.eval row12651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12651, Integer.Sparse.eval_collectBalanced, rawRowCheck12651]

theorem rawRowCheck12652 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form4 = rawRow12652 := by decide +kernel

theorem rowCheck12652 : row12652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12652 := by decide +kernel

theorem rowEval12652 (x : Key → ℝ) : Integer.Sparse.eval row12652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12652, Integer.Sparse.eval_collectBalanced, rawRowCheck12652]

theorem rawRowCheck12653 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form4 = rawRow12653 := by decide +kernel

theorem rowCheck12653 : row12653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12653 := by decide +kernel

theorem rowEval12653 (x : Key → ℝ) : Integer.Sparse.eval row12653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12653, Integer.Sparse.eval_collectBalanced, rawRowCheck12653]

theorem rawRowCheck12654 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form4 = rawRow12654 := by decide +kernel

theorem rowCheck12654 : row12654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12654 := by decide +kernel

theorem rowEval12654 (x : Key → ℝ) : Integer.Sparse.eval row12654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12654, Integer.Sparse.eval_collectBalanced, rawRowCheck12654]

theorem rawRowCheck12655 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form4 = rawRow12655 := by decide +kernel

theorem rowCheck12655 : row12655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12655 := by decide +kernel

theorem rowEval12655 (x : Key → ℝ) : Integer.Sparse.eval row12655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12655, Integer.Sparse.eval_collectBalanced, rawRowCheck12655]

theorem rawRowCheck12656 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow12656 := by decide +kernel

theorem rowCheck12656 : row12656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12656 := by decide +kernel

theorem rowEval12656 (x : Key → ℝ) : Integer.Sparse.eval row12656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12656, Integer.Sparse.eval_collectBalanced, rawRowCheck12656]

theorem rawRowCheck12657 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow12657 := by decide +kernel

theorem rowCheck12657 : row12657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12657 := by decide +kernel

theorem rowEval12657 (x : Key → ℝ) : Integer.Sparse.eval row12657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12657, Integer.Sparse.eval_collectBalanced, rawRowCheck12657]

theorem rawRowCheck12658 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow12658 := by decide +kernel

theorem rowCheck12658 : row12658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12658 := by decide +kernel

theorem rowEval12658 (x : Key → ℝ) : Integer.Sparse.eval row12658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12658, Integer.Sparse.eval_collectBalanced, rawRowCheck12658]

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

theorem entryCheck26_4 : entry26_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_4 k)) := by decide +kernel

theorem rowsSound26_4 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval12635 x
  · exact rowEval12636 x
  · exact rowEval12637 x
  · exact rowEval12638 x
  · exact rowEval12639 x
  · exact rowEval12640 x
  · exact rowEval12641 x
  · exact rowEval12642 x
  · exact rowEval12643 x
  · exact rowEval12644 x
  · exact rowEval12645 x
  · exact rowEval12646 x
  · exact rowEval12647 x
  · exact rowEval12648 x
  · exact rowEval12649 x
  · exact rowEval12650 x
  · exact rowEval12651 x
  · exact rowEval12652 x
  · exact rowEval12653 x
  · exact rowEval12654 x
  · exact rowEval12655 x
  · exact rowEval12656 x
  · exact rowEval12657 x
  · exact rowEval12658 x

theorem entryEval26_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_4 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck26_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_4]

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

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7494 x
  · exact rowEval7495 x
  · exact rowEval7496 x
  · exact rowEval7497 x
  · exact rowEval7498 x
  · exact rowEval7499 x
  · exact rowEval7500 x
  · exact rowEval7501 x
  · exact rowEval7502 x
  · exact rowEval7503 x
  · exact rowEval7504 x
  · exact rowEval7505 x
  · exact rowEval7506 x
  · exact rowEval7507 x
  · exact rowEval7508 x
  · exact rowEval7509 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

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

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7542 x
  · exact rowEval7543 x
  · exact rowEval7544 x
  · exact rowEval7545 x
  · exact rowEval7546 x
  · exact rowEval7547 x
  · exact rowEval7548 x
  · exact rowEval7549 x
  · exact rowEval7550 x
  · exact rowEval7551 x
  · exact rowEval7552 x
  · exact rowEval7553 x
  · exact rowEval7554 x
  · exact rowEval7555 x
  · exact rowEval7556 x
  · exact rowEval7557 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7558 x
  · exact rowEval7559 x
  · exact rowEval7560 x
  · exact rowEval7561 x
  · exact rowEval7562 x
  · exact rowEval7563 x
  · exact rowEval7564 x
  · exact rowEval7565 x
  · exact rowEval7566 x
  · exact rowEval7567 x
  · exact rowEval7568 x
  · exact rowEval7569 x
  · exact rowEval7570 x
  · exact rowEval7571 x
  · exact rowEval7572 x
  · exact rowEval7573 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

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

theorem rawRowCheck7810 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form4 = rawRow7810 := by decide +kernel

theorem rowCheck7810 : row7810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7810 := by decide +kernel

theorem rowEval7810 (x : Key → ℝ) : Integer.Sparse.eval row7810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7810, Integer.Sparse.eval_collectBalanced, rawRowCheck7810]

theorem rawRowCheck7811 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow7811 := by decide +kernel

theorem rowCheck7811 : row7811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7811 := by decide +kernel

theorem rowEval7811 (x : Key → ℝ) : Integer.Sparse.eval row7811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7811, Integer.Sparse.eval_collectBalanced, rawRowCheck7811]

theorem rawRowCheck7812 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow7812 := by decide +kernel

theorem rowCheck7812 : row7812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7812 := by decide +kernel

theorem rowEval7812 (x : Key → ℝ) : Integer.Sparse.eval row7812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7812, Integer.Sparse.eval_collectBalanced, rawRowCheck7812]

theorem rawRowCheck7813 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow7813 := by decide +kernel

theorem rowCheck7813 : row7813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7813 := by decide +kernel

theorem rowEval7813 (x : Key → ℝ) : Integer.Sparse.eval row7813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7813, Integer.Sparse.eval_collectBalanced, rawRowCheck7813]

theorem rawRowCheck7814 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow7814 := by decide +kernel

theorem rowCheck7814 : row7814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7814 := by decide +kernel

theorem rowEval7814 (x : Key → ℝ) : Integer.Sparse.eval row7814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck7814, Integer.Sparse.eval_collectBalanced, rawRowCheck7814]

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

theorem entryCheck6_4 : entry6_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_4 k)) := by decide +kernel

theorem rowsSound6_4 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7810 x
  · exact rowEval7811 x
  · exact rowEval7812 x
  · exact rowEval7813 x
  · exact rowEval7814 x

theorem entryEval6_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_4 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck6_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_4]

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

theorem entryEvalRow4_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 4).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval4_0 B hB
  · exact entryEval4_1 B hB
  · exact entryEval4_2 B hB
  · exact entryEval4_3 B hB
  · exact entryEval4_4 B hB
  · exact (entryEval5_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e_oai
