-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:52:51.588683+00:00
-- url     : https://prove2.me/submissions/ed00474b-258e-4b68-b9a8-789ced6fbe22

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval10_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval9_8_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck6598 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form6 = rawRow6598 := by decide +kernel

theorem rowCheck6598 : row6598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6598 := by decide +kernel

theorem rowEval6598 (x : Key → ℝ) : Integer.Sparse.eval row6598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6598, Integer.Sparse.eval_collectBalanced, rawRowCheck6598]

theorem rawRowCheck6599 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form6 = rawRow6599 := by decide +kernel

theorem rowCheck6599 : row6599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6599 := by decide +kernel

theorem rowEval6599 (x : Key → ℝ) : Integer.Sparse.eval row6599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6599, Integer.Sparse.eval_collectBalanced, rawRowCheck6599]

theorem rawRowCheck6600 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form6 = rawRow6600 := by decide +kernel

theorem rowCheck6600 : row6600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6600 := by decide +kernel

theorem rowEval6600 (x : Key → ℝ) : Integer.Sparse.eval row6600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6600, Integer.Sparse.eval_collectBalanced, rawRowCheck6600]

theorem rawRowCheck6601 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form6 = rawRow6601 := by decide +kernel

theorem rowCheck6601 : row6601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6601 := by decide +kernel

theorem rowEval6601 (x : Key → ℝ) : Integer.Sparse.eval row6601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6601, Integer.Sparse.eval_collectBalanced, rawRowCheck6601]

theorem rawRowCheck6602 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form6 = rawRow6602 := by decide +kernel

theorem rowCheck6602 : row6602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6602 := by decide +kernel

theorem rowEval6602 (x : Key → ℝ) : Integer.Sparse.eval row6602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6602, Integer.Sparse.eval_collectBalanced, rawRowCheck6602]

theorem rawRowCheck6603 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form6 = rawRow6603 := by decide +kernel

theorem rowCheck6603 : row6603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6603 := by decide +kernel

theorem rowEval6603 (x : Key → ℝ) : Integer.Sparse.eval row6603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6603, Integer.Sparse.eval_collectBalanced, rawRowCheck6603]

theorem rawRowCheck6604 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6604 := by decide +kernel

theorem rowCheck6604 : row6604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6604 := by decide +kernel

theorem rowEval6604 (x : Key → ℝ) : Integer.Sparse.eval row6604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6604, Integer.Sparse.eval_collectBalanced, rawRowCheck6604]

theorem rawRowCheck6605 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6605 := by decide +kernel

theorem rowCheck6605 : row6605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6605 := by decide +kernel

theorem rowEval6605 (x : Key → ℝ) : Integer.Sparse.eval row6605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6605, Integer.Sparse.eval_collectBalanced, rawRowCheck6605]

theorem rawRowCheck6606 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form6 = rawRow6606 := by decide +kernel

theorem rowCheck6606 : row6606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6606 := by decide +kernel

theorem rowEval6606 (x : Key → ℝ) : Integer.Sparse.eval row6606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6606, Integer.Sparse.eval_collectBalanced, rawRowCheck6606]

theorem rawRowCheck6607 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form6 = rawRow6607 := by decide +kernel

theorem rowCheck6607 : row6607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6607 := by decide +kernel

theorem rowEval6607 (x : Key → ℝ) : Integer.Sparse.eval row6607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6607, Integer.Sparse.eval_collectBalanced, rawRowCheck6607]

theorem rawRowCheck6608 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6608 := by decide +kernel

theorem rowCheck6608 : row6608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6608 := by decide +kernel

theorem rowEval6608 (x : Key → ℝ) : Integer.Sparse.eval row6608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6608, Integer.Sparse.eval_collectBalanced, rawRowCheck6608]

theorem rawRowCheck6609 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6609 := by decide +kernel

theorem rowCheck6609 : row6609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6609 := by decide +kernel

theorem rowEval6609 (x : Key → ℝ) : Integer.Sparse.eval row6609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6609, Integer.Sparse.eval_collectBalanced, rawRowCheck6609]

theorem rawRowCheck6610 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form6 = rawRow6610 := by decide +kernel

theorem rowCheck6610 : row6610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6610 := by decide +kernel

theorem rowEval6610 (x : Key → ℝ) : Integer.Sparse.eval row6610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6610, Integer.Sparse.eval_collectBalanced, rawRowCheck6610]

theorem rawRowCheck6611 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form6 = rawRow6611 := by decide +kernel

theorem rowCheck6611 : row6611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6611 := by decide +kernel

theorem rowEval6611 (x : Key → ℝ) : Integer.Sparse.eval row6611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6611, Integer.Sparse.eval_collectBalanced, rawRowCheck6611]

theorem rawRowCheck6612 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form6 = rawRow6612 := by decide +kernel

theorem rowCheck6612 : row6612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6612 := by decide +kernel

theorem rowEval6612 (x : Key → ℝ) : Integer.Sparse.eval row6612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6612, Integer.Sparse.eval_collectBalanced, rawRowCheck6612]

theorem rawRowCheck6613 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form6 = rawRow6613 := by decide +kernel

theorem rowCheck6613 : row6613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6613 := by decide +kernel

theorem rowEval6613 (x : Key → ℝ) : Integer.Sparse.eval row6613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6613, Integer.Sparse.eval_collectBalanced, rawRowCheck6613]

theorem rawRowCheck6614 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form6 = rawRow6614 := by decide +kernel

theorem rowCheck6614 : row6614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6614 := by decide +kernel

theorem rowEval6614 (x : Key → ℝ) : Integer.Sparse.eval row6614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6614, Integer.Sparse.eval_collectBalanced, rawRowCheck6614]

theorem rawRowCheck6615 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form6 = rawRow6615 := by decide +kernel

theorem rowCheck6615 : row6615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6615 := by decide +kernel

theorem rowEval6615 (x : Key → ℝ) : Integer.Sparse.eval row6615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6615, Integer.Sparse.eval_collectBalanced, rawRowCheck6615]

theorem rawRowCheck6616 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form6 = rawRow6616 := by decide +kernel

theorem rowCheck6616 : row6616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6616 := by decide +kernel

theorem rowEval6616 (x : Key → ℝ) : Integer.Sparse.eval row6616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6616, Integer.Sparse.eval_collectBalanced, rawRowCheck6616]

theorem rawRowCheck6617 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form6 = rawRow6617 := by decide +kernel

theorem rowCheck6617 : row6617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6617 := by decide +kernel

theorem rowEval6617 (x : Key → ℝ) : Integer.Sparse.eval row6617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6617, Integer.Sparse.eval_collectBalanced, rawRowCheck6617]

theorem rawRowCheck6618 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form6 = rawRow6618 := by decide +kernel

theorem rowCheck6618 : row6618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6618 := by decide +kernel

theorem rowEval6618 (x : Key → ℝ) : Integer.Sparse.eval row6618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6618, Integer.Sparse.eval_collectBalanced, rawRowCheck6618]

theorem rawRowCheck6619 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form6 = rawRow6619 := by decide +kernel

theorem rowCheck6619 : row6619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6619 := by decide +kernel

theorem rowEval6619 (x : Key → ℝ) : Integer.Sparse.eval row6619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6619, Integer.Sparse.eval_collectBalanced, rawRowCheck6619]

theorem rawRowCheck6620 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form6 = rawRow6620 := by decide +kernel

theorem rowCheck6620 : row6620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6620 := by decide +kernel

theorem rowEval6620 (x : Key → ℝ) : Integer.Sparse.eval row6620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6620, Integer.Sparse.eval_collectBalanced, rawRowCheck6620]

theorem rawRowCheck6621 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form6 = rawRow6621 := by decide +kernel

theorem rowCheck6621 : row6621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6621 := by decide +kernel

theorem rowEval6621 (x : Key → ℝ) : Integer.Sparse.eval row6621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6621, Integer.Sparse.eval_collectBalanced, rawRowCheck6621]

theorem rawRowCheck6622 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6622 := by decide +kernel

theorem rowCheck6622 : row6622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6622 := by decide +kernel

theorem rowEval6622 (x : Key → ℝ) : Integer.Sparse.eval row6622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6622, Integer.Sparse.eval_collectBalanced, rawRowCheck6622]

theorem rawRowCheck6623 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6623 := by decide +kernel

theorem rowCheck6623 : row6623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6623 := by decide +kernel

theorem rowEval6623 (x : Key → ℝ) : Integer.Sparse.eval row6623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6623, Integer.Sparse.eval_collectBalanced, rawRowCheck6623]

theorem rawRowCheck6624 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6624 := by decide +kernel

theorem rowCheck6624 : row6624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6624 := by decide +kernel

theorem rowEval6624 (x : Key → ℝ) : Integer.Sparse.eval row6624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6624, Integer.Sparse.eval_collectBalanced, rawRowCheck6624]

theorem rawRowCheck6625 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6625 := by decide +kernel

theorem rowCheck6625 : row6625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6625 := by decide +kernel

theorem rowEval6625 (x : Key → ℝ) : Integer.Sparse.eval row6625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6625, Integer.Sparse.eval_collectBalanced, rawRowCheck6625]

theorem rawRowCheck6626 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form6 = rawRow6626 := by decide +kernel

theorem rowCheck6626 : row6626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6626 := by decide +kernel

theorem rowEval6626 (x : Key → ℝ) : Integer.Sparse.eval row6626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6626, Integer.Sparse.eval_collectBalanced, rawRowCheck6626]

theorem rawRowCheck6627 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form6 = rawRow6627 := by decide +kernel

theorem rowCheck6627 : row6627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6627 := by decide +kernel

theorem rowEval6627 (x : Key → ℝ) : Integer.Sparse.eval row6627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6627, Integer.Sparse.eval_collectBalanced, rawRowCheck6627]

theorem rawRowCheck6628 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form6 = rawRow6628 := by decide +kernel

theorem rowCheck6628 : row6628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6628 := by decide +kernel

theorem rowEval6628 (x : Key → ℝ) : Integer.Sparse.eval row6628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6628, Integer.Sparse.eval_collectBalanced, rawRowCheck6628]

theorem rawRowCheck6629 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form6 = rawRow6629 := by decide +kernel

theorem rowCheck6629 : row6629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6629 := by decide +kernel

theorem rowEval6629 (x : Key → ℝ) : Integer.Sparse.eval row6629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6629, Integer.Sparse.eval_collectBalanced, rawRowCheck6629]

theorem rawRowCheck6630 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form6 = rawRow6630 := by decide +kernel

theorem rowCheck6630 : row6630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6630 := by decide +kernel

theorem rowEval6630 (x : Key → ℝ) : Integer.Sparse.eval row6630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6630, Integer.Sparse.eval_collectBalanced, rawRowCheck6630]

theorem rawRowCheck6631 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form6 = rawRow6631 := by decide +kernel

theorem rowCheck6631 : row6631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6631 := by decide +kernel

theorem rowEval6631 (x : Key → ℝ) : Integer.Sparse.eval row6631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6631, Integer.Sparse.eval_collectBalanced, rawRowCheck6631]

theorem rawRowCheck6632 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form6 = rawRow6632 := by decide +kernel

theorem rowCheck6632 : row6632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6632 := by decide +kernel

theorem rowEval6632 (x : Key → ℝ) : Integer.Sparse.eval row6632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6632, Integer.Sparse.eval_collectBalanced, rawRowCheck6632]

theorem rawRowCheck6633 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form6 = rawRow6633 := by decide +kernel

theorem rowCheck6633 : row6633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6633 := by decide +kernel

theorem rowEval6633 (x : Key → ℝ) : Integer.Sparse.eval row6633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6633, Integer.Sparse.eval_collectBalanced, rawRowCheck6633]

theorem rawRowCheck6634 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form6 = rawRow6634 := by decide +kernel

theorem rowCheck6634 : row6634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6634 := by decide +kernel

theorem rowEval6634 (x : Key → ℝ) : Integer.Sparse.eval row6634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6634, Integer.Sparse.eval_collectBalanced, rawRowCheck6634]

theorem rawRowCheck6635 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form6 = rawRow6635 := by decide +kernel

theorem rowCheck6635 : row6635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6635 := by decide +kernel

theorem rowEval6635 (x : Key → ℝ) : Integer.Sparse.eval row6635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6635, Integer.Sparse.eval_collectBalanced, rawRowCheck6635]

theorem rawRowCheck6636 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form6 = rawRow6636 := by decide +kernel

theorem rowCheck6636 : row6636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6636 := by decide +kernel

theorem rowEval6636 (x : Key → ℝ) : Integer.Sparse.eval row6636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6636, Integer.Sparse.eval_collectBalanced, rawRowCheck6636]

theorem rawRowCheck6637 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form6 = rawRow6637 := by decide +kernel

theorem rowCheck6637 : row6637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6637 := by decide +kernel

theorem rowEval6637 (x : Key → ℝ) : Integer.Sparse.eval row6637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6637, Integer.Sparse.eval_collectBalanced, rawRowCheck6637]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck6678 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form8 = rawRow6678 := by decide +kernel

theorem rowCheck6678 : row6678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6678 := by decide +kernel

theorem rowEval6678 (x : Key → ℝ) : Integer.Sparse.eval row6678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6678, Integer.Sparse.eval_collectBalanced, rawRowCheck6678]

theorem rawRowCheck6679 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form8 = rawRow6679 := by decide +kernel

theorem rowCheck6679 : row6679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6679 := by decide +kernel

theorem rowEval6679 (x : Key → ℝ) : Integer.Sparse.eval row6679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6679, Integer.Sparse.eval_collectBalanced, rawRowCheck6679]

theorem rawRowCheck6680 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form8 = rawRow6680 := by decide +kernel

theorem rowCheck6680 : row6680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6680 := by decide +kernel

theorem rowEval6680 (x : Key → ℝ) : Integer.Sparse.eval row6680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6680, Integer.Sparse.eval_collectBalanced, rawRowCheck6680]

theorem rawRowCheck6681 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form8 = rawRow6681 := by decide +kernel

theorem rowCheck6681 : row6681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6681 := by decide +kernel

theorem rowEval6681 (x : Key → ℝ) : Integer.Sparse.eval row6681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6681, Integer.Sparse.eval_collectBalanced, rawRowCheck6681]

theorem rawRowCheck6682 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form8 = rawRow6682 := by decide +kernel

theorem rowCheck6682 : row6682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6682 := by decide +kernel

theorem rowEval6682 (x : Key → ℝ) : Integer.Sparse.eval row6682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6682, Integer.Sparse.eval_collectBalanced, rawRowCheck6682]

theorem rawRowCheck6683 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form8 = rawRow6683 := by decide +kernel

theorem rowCheck6683 : row6683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6683 := by decide +kernel

theorem rowEval6683 (x : Key → ℝ) : Integer.Sparse.eval row6683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6683, Integer.Sparse.eval_collectBalanced, rawRowCheck6683]

theorem rawRowCheck6684 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form8 = rawRow6684 := by decide +kernel

theorem rowCheck6684 : row6684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6684 := by decide +kernel

theorem rowEval6684 (x : Key → ℝ) : Integer.Sparse.eval row6684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6684, Integer.Sparse.eval_collectBalanced, rawRowCheck6684]

theorem rawRowCheck6685 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form8 = rawRow6685 := by decide +kernel

theorem rowCheck6685 : row6685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6685 := by decide +kernel

theorem rowEval6685 (x : Key → ℝ) : Integer.Sparse.eval row6685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6685, Integer.Sparse.eval_collectBalanced, rawRowCheck6685]

theorem rawRowCheck6686 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form8 = rawRow6686 := by decide +kernel

theorem rowCheck6686 : row6686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6686 := by decide +kernel

theorem rowEval6686 (x : Key → ℝ) : Integer.Sparse.eval row6686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6686, Integer.Sparse.eval_collectBalanced, rawRowCheck6686]

theorem rawRowCheck6687 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form8 = rawRow6687 := by decide +kernel

theorem rowCheck6687 : row6687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6687 := by decide +kernel

theorem rowEval6687 (x : Key → ℝ) : Integer.Sparse.eval row6687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6687, Integer.Sparse.eval_collectBalanced, rawRowCheck6687]

theorem rawRowCheck6688 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form8 = rawRow6688 := by decide +kernel

theorem rowCheck6688 : row6688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6688 := by decide +kernel

theorem rowEval6688 (x : Key → ℝ) : Integer.Sparse.eval row6688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6688, Integer.Sparse.eval_collectBalanced, rawRowCheck6688]

theorem rawRowCheck6689 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form8 = rawRow6689 := by decide +kernel

theorem rowCheck6689 : row6689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6689 := by decide +kernel

theorem rowEval6689 (x : Key → ℝ) : Integer.Sparse.eval row6689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6689, Integer.Sparse.eval_collectBalanced, rawRowCheck6689]

theorem rawRowCheck6690 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form8 = rawRow6690 := by decide +kernel

theorem rowCheck6690 : row6690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6690 := by decide +kernel

theorem rowEval6690 (x : Key → ℝ) : Integer.Sparse.eval row6690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6690, Integer.Sparse.eval_collectBalanced, rawRowCheck6690]

theorem rawRowCheck6691 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form8 = rawRow6691 := by decide +kernel

theorem rowCheck6691 : row6691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6691 := by decide +kernel

theorem rowEval6691 (x : Key → ℝ) : Integer.Sparse.eval row6691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6691, Integer.Sparse.eval_collectBalanced, rawRowCheck6691]

theorem rawRowCheck6692 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form8 = rawRow6692 := by decide +kernel

theorem rowCheck6692 : row6692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6692 := by decide +kernel

theorem rowEval6692 (x : Key → ℝ) : Integer.Sparse.eval row6692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6692, Integer.Sparse.eval_collectBalanced, rawRowCheck6692]

theorem rawRowCheck6693 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form8 = rawRow6693 := by decide +kernel

theorem rowCheck6693 : row6693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6693 := by decide +kernel

theorem rowEval6693 (x : Key → ℝ) : Integer.Sparse.eval row6693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6693, Integer.Sparse.eval_collectBalanced, rawRowCheck6693]

theorem rawRowCheck6694 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form8 = rawRow6694 := by decide +kernel

theorem rowCheck6694 : row6694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6694 := by decide +kernel

theorem rowEval6694 (x : Key → ℝ) : Integer.Sparse.eval row6694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6694, Integer.Sparse.eval_collectBalanced, rawRowCheck6694]

theorem rawRowCheck6695 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form8 = rawRow6695 := by decide +kernel

theorem rowCheck6695 : row6695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6695 := by decide +kernel

theorem rowEval6695 (x : Key → ℝ) : Integer.Sparse.eval row6695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6695, Integer.Sparse.eval_collectBalanced, rawRowCheck6695]

theorem rawRowCheck6696 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form8 = rawRow6696 := by decide +kernel

theorem rowCheck6696 : row6696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6696 := by decide +kernel

theorem rowEval6696 (x : Key → ℝ) : Integer.Sparse.eval row6696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6696, Integer.Sparse.eval_collectBalanced, rawRowCheck6696]

theorem rawRowCheck6697 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form8 = rawRow6697 := by decide +kernel

theorem rowCheck6697 : row6697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6697 := by decide +kernel

theorem rowEval6697 (x : Key → ℝ) : Integer.Sparse.eval row6697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6697, Integer.Sparse.eval_collectBalanced, rawRowCheck6697]

theorem rawRowCheck6698 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form8 = rawRow6698 := by decide +kernel

theorem rowCheck6698 : row6698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6698 := by decide +kernel

theorem rowEval6698 (x : Key → ℝ) : Integer.Sparse.eval row6698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6698, Integer.Sparse.eval_collectBalanced, rawRowCheck6698]

theorem rawRowCheck6699 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form8 = rawRow6699 := by decide +kernel

theorem rowCheck6699 : row6699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6699 := by decide +kernel

theorem rowEval6699 (x : Key → ℝ) : Integer.Sparse.eval row6699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6699, Integer.Sparse.eval_collectBalanced, rawRowCheck6699]

theorem rawRowCheck6700 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form8 = rawRow6700 := by decide +kernel

theorem rowCheck6700 : row6700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6700 := by decide +kernel

theorem rowEval6700 (x : Key → ℝ) : Integer.Sparse.eval row6700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6700, Integer.Sparse.eval_collectBalanced, rawRowCheck6700]

theorem rawRowCheck6701 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form8 = rawRow6701 := by decide +kernel

theorem rowCheck6701 : row6701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6701 := by decide +kernel

theorem rowEval6701 (x : Key → ℝ) : Integer.Sparse.eval row6701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6701, Integer.Sparse.eval_collectBalanced, rawRowCheck6701]

theorem rawRowCheck6702 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form8 = rawRow6702 := by decide +kernel

theorem rowCheck6702 : row6702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6702 := by decide +kernel

theorem rowEval6702 (x : Key → ℝ) : Integer.Sparse.eval row6702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6702, Integer.Sparse.eval_collectBalanced, rawRowCheck6702]

theorem rawRowCheck6703 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form8 = rawRow6703 := by decide +kernel

theorem rowCheck6703 : row6703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6703 := by decide +kernel

theorem rowEval6703 (x : Key → ℝ) : Integer.Sparse.eval row6703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6703, Integer.Sparse.eval_collectBalanced, rawRowCheck6703]

theorem rawRowCheck6704 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form8 = rawRow6704 := by decide +kernel

theorem rowCheck6704 : row6704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6704 := by decide +kernel

theorem rowEval6704 (x : Key → ℝ) : Integer.Sparse.eval row6704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6704, Integer.Sparse.eval_collectBalanced, rawRowCheck6704]

theorem rawRowCheck6705 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form8 = rawRow6705 := by decide +kernel

theorem rowCheck6705 : row6705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6705 := by decide +kernel

theorem rowEval6705 (x : Key → ℝ) : Integer.Sparse.eval row6705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6705, Integer.Sparse.eval_collectBalanced, rawRowCheck6705]

theorem rawRowCheck6706 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form8 = rawRow6706 := by decide +kernel

theorem rowCheck6706 : row6706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6706 := by decide +kernel

theorem rowEval6706 (x : Key → ℝ) : Integer.Sparse.eval row6706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6706, Integer.Sparse.eval_collectBalanced, rawRowCheck6706]

theorem rawRowCheck6707 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form8 = rawRow6707 := by decide +kernel

theorem rowCheck6707 : row6707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6707 := by decide +kernel

theorem rowEval6707 (x : Key → ℝ) : Integer.Sparse.eval row6707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6707, Integer.Sparse.eval_collectBalanced, rawRowCheck6707]

theorem rawRowCheck6708 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form8 = rawRow6708 := by decide +kernel

theorem rowCheck6708 : row6708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6708 := by decide +kernel

theorem rowEval6708 (x : Key → ℝ) : Integer.Sparse.eval row6708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6708, Integer.Sparse.eval_collectBalanced, rawRowCheck6708]

theorem rawRowCheck6709 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form8 = rawRow6709 := by decide +kernel

theorem rowCheck6709 : row6709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6709 := by decide +kernel

theorem rowEval6709 (x : Key → ℝ) : Integer.Sparse.eval row6709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6709, Integer.Sparse.eval_collectBalanced, rawRowCheck6709]

theorem rawRowCheck6710 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form8 = rawRow6710 := by decide +kernel

theorem rowCheck6710 : row6710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6710 := by decide +kernel

theorem rowEval6710 (x : Key → ℝ) : Integer.Sparse.eval row6710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6710, Integer.Sparse.eval_collectBalanced, rawRowCheck6710]

theorem rawRowCheck6711 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form8 = rawRow6711 := by decide +kernel

theorem rowCheck6711 : row6711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6711 := by decide +kernel

theorem rowEval6711 (x : Key → ℝ) : Integer.Sparse.eval row6711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6711, Integer.Sparse.eval_collectBalanced, rawRowCheck6711]

theorem rawRowCheck6712 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form8 = rawRow6712 := by decide +kernel

theorem rowCheck6712 : row6712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6712 := by decide +kernel

theorem rowEval6712 (x : Key → ℝ) : Integer.Sparse.eval row6712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6712, Integer.Sparse.eval_collectBalanced, rawRowCheck6712]

theorem rawRowCheck6713 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form8 = rawRow6713 := by decide +kernel

theorem rowCheck6713 : row6713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6713 := by decide +kernel

theorem rowEval6713 (x : Key → ℝ) : Integer.Sparse.eval row6713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6713, Integer.Sparse.eval_collectBalanced, rawRowCheck6713]

theorem rawRowCheck6714 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form8 = rawRow6714 := by decide +kernel

theorem rowCheck6714 : row6714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6714 := by decide +kernel

theorem rowEval6714 (x : Key → ℝ) : Integer.Sparse.eval row6714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6714, Integer.Sparse.eval_collectBalanced, rawRowCheck6714]

theorem rawRowCheck6715 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form8 = rawRow6715 := by decide +kernel

theorem rowCheck6715 : row6715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6715 := by decide +kernel

theorem rowEval6715 (x : Key → ℝ) : Integer.Sparse.eval row6715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6715, Integer.Sparse.eval_collectBalanced, rawRowCheck6715]

theorem rawRowCheck6716 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form8 = rawRow6716 := by decide +kernel

theorem rowCheck6716 : row6716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6716 := by decide +kernel

theorem rowEval6716 (x : Key → ℝ) : Integer.Sparse.eval row6716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6716, Integer.Sparse.eval_collectBalanced, rawRowCheck6716]

theorem rawRowCheck6717 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form8 = rawRow6717 := by decide +kernel

theorem rowCheck6717 : row6717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6717 := by decide +kernel

theorem rowEval6717 (x : Key → ℝ) : Integer.Sparse.eval row6717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6717, Integer.Sparse.eval_collectBalanced, rawRowCheck6717]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_6 : entry8_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_6 k)) := by decide +kernel

theorem rowsSound8_6 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form6) x := by
  fin_cases k
  · exact rowEval6598 x
  · exact rowEval6599 x
  · exact rowEval6600 x
  · exact rowEval6601 x
  · exact rowEval6602 x
  · exact rowEval6603 x
  · exact rowEval6604 x
  · exact rowEval6605 x
  · exact rowEval6606 x
  · exact rowEval6607 x
  · exact rowEval6608 x
  · exact rowEval6609 x
  · exact rowEval6610 x
  · exact rowEval6611 x
  · exact rowEval6612 x
  · exact rowEval6613 x
  · exact rowEval6614 x
  · exact rowEval6615 x
  · exact rowEval6616 x
  · exact rowEval6617 x
  · exact rowEval6618 x
  · exact rowEval6619 x
  · exact rowEval6620 x
  · exact rowEval6621 x
  · exact rowEval6622 x
  · exact rowEval6623 x
  · exact rowEval6624 x
  · exact rowEval6625 x
  · exact rowEval6626 x
  · exact rowEval6627 x
  · exact rowEval6628 x
  · exact rowEval6629 x
  · exact rowEval6630 x
  · exact rowEval6631 x
  · exact rowEval6632 x
  · exact rowEval6633 x
  · exact rowEval6634 x
  · exact rowEval6635 x
  · exact rowEval6636 x
  · exact rowEval6637 x

theorem entryEval8_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_6 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form6 B := by
  rw [entryCheck8_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_6]

theorem entryCheck8_8 : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

theorem rowsSound8_8 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form8) x := by
  fin_cases k
  · exact rowEval6678 x
  · exact rowEval6679 x
  · exact rowEval6680 x
  · exact rowEval6681 x
  · exact rowEval6682 x
  · exact rowEval6683 x
  · exact rowEval6684 x
  · exact rowEval6685 x
  · exact rowEval6686 x
  · exact rowEval6687 x
  · exact rowEval6688 x
  · exact rowEval6689 x
  · exact rowEval6690 x
  · exact rowEval6691 x
  · exact rowEval6692 x
  · exact rowEval6693 x
  · exact rowEval6694 x
  · exact rowEval6695 x
  · exact rowEval6696 x
  · exact rowEval6697 x
  · exact rowEval6698 x
  · exact rowEval6699 x
  · exact rowEval6700 x
  · exact rowEval6701 x
  · exact rowEval6702 x
  · exact rowEval6703 x
  · exact rowEval6704 x
  · exact rowEval6705 x
  · exact rowEval6706 x
  · exact rowEval6707 x
  · exact rowEval6708 x
  · exact rowEval6709 x
  · exact rowEval6710 x
  · exact rowEval6711 x
  · exact rowEval6712 x
  · exact rowEval6713 x
  · exact rowEval6714 x
  · exact rowEval6715 x
  · exact rowEval6716 x
  · exact rowEval6717 x

theorem entryEval8_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_8 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form8 B := by
  rw [entryCheck8_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_8]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

theorem entryEvalRow8_e_oai (j : Fin 11) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 8 j) (GramNormalization.eval B) =
      (GramFunctions.Block2.forms 8).mixedGram (GramFunctions.Block2.forms j) B := by
  fin_cases j
  · exact entryEval8_0_e B hB
  · exact entryEval8_1_e B hB
  · exact entryEval8_2_e B hB
  · exact entryEval8_3_e B hB
  · exact entryEval8_4_e B hB
  · exact entryEval8_5_e B hB
  · exact entryEval8_6 B hB
  · exact entryEval8_7_e B hB
  · exact entryEval8_8 B hB
  · exact (entryEval9_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow8_e_oai := @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow8_e_oai
