-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:19:56.321623+00:00
-- url     : https://prove2.me/submissions/85505a16-6cbe-481d-9146-63ad661d3854

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval23_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval5_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval8_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval9_0_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7348 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form0 = rawRow7348 := by decide +kernel

theorem rowCheck7348 : row7348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7348 := by decide +kernel

theorem rowEval7348 (x : Key → ℝ) : Integer.Sparse.eval row7348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7348, Integer.Sparse.eval_collectBalanced, rawRowCheck7348]

theorem rawRowCheck7349 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form0 = rawRow7349 := by decide +kernel

theorem rowCheck7349 : row7349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7349 := by decide +kernel

theorem rowEval7349 (x : Key → ℝ) : Integer.Sparse.eval row7349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7349, Integer.Sparse.eval_collectBalanced, rawRowCheck7349]

theorem rawRowCheck7350 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form0 = rawRow7350 := by decide +kernel

theorem rowCheck7350 : row7350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7350 := by decide +kernel

theorem rowEval7350 (x : Key → ℝ) : Integer.Sparse.eval row7350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7350, Integer.Sparse.eval_collectBalanced, rawRowCheck7350]

theorem rawRowCheck7351 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form0 = rawRow7351 := by decide +kernel

theorem rowCheck7351 : row7351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7351 := by decide +kernel

theorem rowEval7351 (x : Key → ℝ) : Integer.Sparse.eval row7351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7351, Integer.Sparse.eval_collectBalanced, rawRowCheck7351]

theorem rawRowCheck7352 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form0 = rawRow7352 := by decide +kernel

theorem rowCheck7352 : row7352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7352 := by decide +kernel

theorem rowEval7352 (x : Key → ℝ) : Integer.Sparse.eval row7352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7352, Integer.Sparse.eval_collectBalanced, rawRowCheck7352]

theorem rawRowCheck7353 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form0 = rawRow7353 := by decide +kernel

theorem rowCheck7353 : row7353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7353 := by decide +kernel

theorem rowEval7353 (x : Key → ℝ) : Integer.Sparse.eval row7353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7353, Integer.Sparse.eval_collectBalanced, rawRowCheck7353]

theorem rawRowCheck7354 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form0 = rawRow7354 := by decide +kernel

theorem rowCheck7354 : row7354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7354 := by decide +kernel

theorem rowEval7354 (x : Key → ℝ) : Integer.Sparse.eval row7354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7354, Integer.Sparse.eval_collectBalanced, rawRowCheck7354]

theorem rawRowCheck7355 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form0 = rawRow7355 := by decide +kernel

theorem rowCheck7355 : row7355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7355 := by decide +kernel

theorem rowEval7355 (x : Key → ℝ) : Integer.Sparse.eval row7355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7355, Integer.Sparse.eval_collectBalanced, rawRowCheck7355]

theorem rawRowCheck7356 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form0 = rawRow7356 := by decide +kernel

theorem rowCheck7356 : row7356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7356 := by decide +kernel

theorem rowEval7356 (x : Key → ℝ) : Integer.Sparse.eval row7356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7356, Integer.Sparse.eval_collectBalanced, rawRowCheck7356]

theorem rawRowCheck7357 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form0 = rawRow7357 := by decide +kernel

theorem rowCheck7357 : row7357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7357 := by decide +kernel

theorem rowEval7357 (x : Key → ℝ) : Integer.Sparse.eval row7357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7357, Integer.Sparse.eval_collectBalanced, rawRowCheck7357]

theorem rawRowCheck7358 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form0 = rawRow7358 := by decide +kernel

theorem rowCheck7358 : row7358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7358 := by decide +kernel

theorem rowEval7358 (x : Key → ℝ) : Integer.Sparse.eval row7358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7358, Integer.Sparse.eval_collectBalanced, rawRowCheck7358]

theorem rawRowCheck7359 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form0 = rawRow7359 := by decide +kernel

theorem rowCheck7359 : row7359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7359 := by decide +kernel

theorem rowEval7359 (x : Key → ℝ) : Integer.Sparse.eval row7359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7359, Integer.Sparse.eval_collectBalanced, rawRowCheck7359]

theorem rawRowCheck7360 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form0 = rawRow7360 := by decide +kernel

theorem rowCheck7360 : row7360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7360 := by decide +kernel

theorem rowEval7360 (x : Key → ℝ) : Integer.Sparse.eval row7360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7360, Integer.Sparse.eval_collectBalanced, rawRowCheck7360]

theorem rawRowCheck7361 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form0 = rawRow7361 := by decide +kernel

theorem rowCheck7361 : row7361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7361 := by decide +kernel

theorem rowEval7361 (x : Key → ℝ) : Integer.Sparse.eval row7361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7361, Integer.Sparse.eval_collectBalanced, rawRowCheck7361]

theorem rawRowCheck7362 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form0 = rawRow7362 := by decide +kernel

theorem rowCheck7362 : row7362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7362 := by decide +kernel

theorem rowEval7362 (x : Key → ℝ) : Integer.Sparse.eval row7362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7362, Integer.Sparse.eval_collectBalanced, rawRowCheck7362]

theorem rawRowCheck7363 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form0 = rawRow7363 := by decide +kernel

theorem rowCheck7363 : row7363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7363 := by decide +kernel

theorem rowEval7363 (x : Key → ℝ) : Integer.Sparse.eval row7363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7363, Integer.Sparse.eval_collectBalanced, rawRowCheck7363]

theorem rawRowCheck7364 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form0 = rawRow7364 := by decide +kernel

theorem rowCheck7364 : row7364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7364 := by decide +kernel

theorem rowEval7364 (x : Key → ℝ) : Integer.Sparse.eval row7364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7364, Integer.Sparse.eval_collectBalanced, rawRowCheck7364]

theorem rawRowCheck7365 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form0 = rawRow7365 := by decide +kernel

theorem rowCheck7365 : row7365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7365 := by decide +kernel

theorem rowEval7365 (x : Key → ℝ) : Integer.Sparse.eval row7365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7365, Integer.Sparse.eval_collectBalanced, rawRowCheck7365]

theorem rawRowCheck7366 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form0 = rawRow7366 := by decide +kernel

theorem rowCheck7366 : row7366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7366 := by decide +kernel

theorem rowEval7366 (x : Key → ℝ) : Integer.Sparse.eval row7366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7366, Integer.Sparse.eval_collectBalanced, rawRowCheck7366]

theorem rawRowCheck7367 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form0 = rawRow7367 := by decide +kernel

theorem rowCheck7367 : row7367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7367 := by decide +kernel

theorem rowEval7367 (x : Key → ℝ) : Integer.Sparse.eval row7367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7367, Integer.Sparse.eval_collectBalanced, rawRowCheck7367]

theorem rawRowCheck7368 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form0 = rawRow7368 := by decide +kernel

theorem rowCheck7368 : row7368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7368 := by decide +kernel

theorem rowEval7368 (x : Key → ℝ) : Integer.Sparse.eval row7368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7368, Integer.Sparse.eval_collectBalanced, rawRowCheck7368]

theorem rawRowCheck7369 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7369 := by decide +kernel

theorem rowCheck7369 : row7369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7369 := by decide +kernel

theorem rowEval7369 (x : Key → ℝ) : Integer.Sparse.eval row7369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7369, Integer.Sparse.eval_collectBalanced, rawRowCheck7369]

theorem rawRowCheck7370 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7370 := by decide +kernel

theorem rowCheck7370 : row7370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7370 := by decide +kernel

theorem rowEval7370 (x : Key → ℝ) : Integer.Sparse.eval row7370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7370, Integer.Sparse.eval_collectBalanced, rawRowCheck7370]

theorem rawRowCheck7371 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7371 := by decide +kernel

theorem rowCheck7371 : row7371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7371 := by decide +kernel

theorem rowEval7371 (x : Key → ℝ) : Integer.Sparse.eval row7371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7371, Integer.Sparse.eval_collectBalanced, rawRowCheck7371]

theorem rawRowCheck7372 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7372 := by decide +kernel

theorem rowCheck7372 : row7372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7372 := by decide +kernel

theorem rowEval7372 (x : Key → ℝ) : Integer.Sparse.eval row7372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7372, Integer.Sparse.eval_collectBalanced, rawRowCheck7372]

theorem rawRowCheck7373 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7373 := by decide +kernel

theorem rowCheck7373 : row7373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7373 := by decide +kernel

theorem rowEval7373 (x : Key → ℝ) : Integer.Sparse.eval row7373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7373, Integer.Sparse.eval_collectBalanced, rawRowCheck7373]

theorem rawRowCheck7374 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7374 := by decide +kernel

theorem rowCheck7374 : row7374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7374 := by decide +kernel

theorem rowEval7374 (x : Key → ℝ) : Integer.Sparse.eval row7374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7374, Integer.Sparse.eval_collectBalanced, rawRowCheck7374]

theorem rawRowCheck7375 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7375 := by decide +kernel

theorem rowCheck7375 : row7375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7375 := by decide +kernel

theorem rowEval7375 (x : Key → ℝ) : Integer.Sparse.eval row7375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7375, Integer.Sparse.eval_collectBalanced, rawRowCheck7375]

theorem rawRowCheck7376 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7376 := by decide +kernel

theorem rowCheck7376 : row7376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7376 := by decide +kernel

theorem rowEval7376 (x : Key → ℝ) : Integer.Sparse.eval row7376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7376, Integer.Sparse.eval_collectBalanced, rawRowCheck7376]

theorem rawRowCheck7382 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7382 := by decide +kernel

theorem rowCheck7382 : row7382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7382 := by decide +kernel

theorem rowEval7382 (x : Key → ℝ) : Integer.Sparse.eval row7382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7382, Integer.Sparse.eval_collectBalanced, rawRowCheck7382]

theorem rawRowCheck7383 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7383 := by decide +kernel

theorem rowCheck7383 : row7383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7383 := by decide +kernel

theorem rowEval7383 (x : Key → ℝ) : Integer.Sparse.eval row7383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7383, Integer.Sparse.eval_collectBalanced, rawRowCheck7383]

theorem rawRowCheck7384 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7384 := by decide +kernel

theorem rowCheck7384 : row7384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7384 := by decide +kernel

theorem rowEval7384 (x : Key → ℝ) : Integer.Sparse.eval row7384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7384, Integer.Sparse.eval_collectBalanced, rawRowCheck7384]

theorem rawRowCheck7385 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7385 := by decide +kernel

theorem rowCheck7385 : row7385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7385 := by decide +kernel

theorem rowEval7385 (x : Key → ℝ) : Integer.Sparse.eval row7385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7385, Integer.Sparse.eval_collectBalanced, rawRowCheck7385]

theorem rawRowCheck7386 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7386 := by decide +kernel

theorem rowCheck7386 : row7386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7386 := by decide +kernel

theorem rowEval7386 (x : Key → ℝ) : Integer.Sparse.eval row7386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7386, Integer.Sparse.eval_collectBalanced, rawRowCheck7386]

theorem rawRowCheck7387 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7387 := by decide +kernel

theorem rowCheck7387 : row7387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7387 := by decide +kernel

theorem rowEval7387 (x : Key → ℝ) : Integer.Sparse.eval row7387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7387, Integer.Sparse.eval_collectBalanced, rawRowCheck7387]

theorem rawRowCheck7388 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7388 := by decide +kernel

theorem rowCheck7388 : row7388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7388 := by decide +kernel

theorem rowEval7388 (x : Key → ℝ) : Integer.Sparse.eval row7388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7388, Integer.Sparse.eval_collectBalanced, rawRowCheck7388]

theorem rawRowCheck7389 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0 = rawRow7389 := by decide +kernel

theorem rowCheck7389 : row7389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7389 := by decide +kernel

theorem rowEval7389 (x : Key → ℝ) : Integer.Sparse.eval row7389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7389, Integer.Sparse.eval_collectBalanced, rawRowCheck7389]

theorem rawRowCheck7390 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0 = rawRow7390 := by decide +kernel

theorem rowCheck7390 : row7390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7390 := by decide +kernel

theorem rowEval7390 (x : Key → ℝ) : Integer.Sparse.eval row7390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7390, Integer.Sparse.eval_collectBalanced, rawRowCheck7390]

theorem rawRowCheck7391 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0 = rawRow7391 := by decide +kernel

theorem rowCheck7391 : row7391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7391 := by decide +kernel

theorem rowEval7391 (x : Key → ℝ) : Integer.Sparse.eval row7391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7391, Integer.Sparse.eval_collectBalanced, rawRowCheck7391]

theorem rawRowCheck7392 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0 = rawRow7392 := by decide +kernel

theorem rowCheck7392 : row7392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7392 := by decide +kernel

theorem rowEval7392 (x : Key → ℝ) : Integer.Sparse.eval row7392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7392, Integer.Sparse.eval_collectBalanced, rawRowCheck7392]

theorem rawRowCheck7393 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0 = rawRow7393 := by decide +kernel

theorem rowCheck7393 : row7393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7393 := by decide +kernel

theorem rowEval7393 (x : Key → ℝ) : Integer.Sparse.eval row7393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7393, Integer.Sparse.eval_collectBalanced, rawRowCheck7393]

theorem rawRowCheck7394 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0 = rawRow7394 := by decide +kernel

theorem rowCheck7394 : row7394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7394 := by decide +kernel

theorem rowEval7394 (x : Key → ℝ) : Integer.Sparse.eval row7394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7394, Integer.Sparse.eval_collectBalanced, rawRowCheck7394]

theorem rawRowCheck7395 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7395 := by decide +kernel

theorem rowCheck7395 : row7395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7395 := by decide +kernel

theorem rowEval7395 (x : Key → ℝ) : Integer.Sparse.eval row7395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7395, Integer.Sparse.eval_collectBalanced, rawRowCheck7395]

theorem rawRowCheck7396 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7396 := by decide +kernel

theorem rowCheck7396 : row7396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7396 := by decide +kernel

theorem rowEval7396 (x : Key → ℝ) : Integer.Sparse.eval row7396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7396, Integer.Sparse.eval_collectBalanced, rawRowCheck7396]

theorem rawRowCheck7397 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7397 := by decide +kernel

theorem rowCheck7397 : row7397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7397 := by decide +kernel

theorem rowEval7397 (x : Key → ℝ) : Integer.Sparse.eval row7397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7397, Integer.Sparse.eval_collectBalanced, rawRowCheck7397]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block3.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form0.terms k).tag (GramFunctions.Block3.form0.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7348 x
  · exact rowEval7349 x
  · exact rowEval7350 x
  · exact rowEval7351 x
  · exact rowEval7352 x
  · exact rowEval7353 x
  · exact rowEval7354 x
  · exact rowEval7355 x
  · exact rowEval7356 x
  · exact rowEval7357 x
  · exact rowEval7358 x
  · exact rowEval7359 x
  · exact rowEval7360 x
  · exact rowEval7361 x
  · exact rowEval7362 x
  · exact rowEval7363 x
  · exact rowEval7364 x
  · exact rowEval7365 x
  · exact rowEval7366 x
  · exact rowEval7367 x
  · exact rowEval7368 x
  · exact rowEval7369 x
  · exact rowEval7370 x
  · exact rowEval7371 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block3.form0.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form0 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block3.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form1.terms k).tag (GramFunctions.Block3.form1.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7372 x
  · exact rowEval7373 x
  · exact rowEval7374 x
  · exact rowEval7375 x
  · exact rowEval7376 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block3.form1.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form1 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck8485 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8485 := by decide +kernel

theorem rowCheck8485 : row8485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8485 := by decide +kernel

theorem rowEval8485 (x : Key → ℝ) : Integer.Sparse.eval row8485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8485, Integer.Sparse.eval_collectBalanced, rawRowCheck8485]

theorem rawRowCheck8486 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow8486 := by decide +kernel

theorem rowCheck8486 : row8486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8486 := by decide +kernel

theorem rowEval8486 (x : Key → ℝ) : Integer.Sparse.eval row8486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8486, Integer.Sparse.eval_collectBalanced, rawRowCheck8486]

theorem rawRowCheck8487 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow8487 := by decide +kernel

theorem rowCheck8487 : row8487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8487 := by decide +kernel

theorem rowEval8487 (x : Key → ℝ) : Integer.Sparse.eval row8487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8487, Integer.Sparse.eval_collectBalanced, rawRowCheck8487]

theorem rawRowCheck8488 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow8488 := by decide +kernel

theorem rowCheck8488 : row8488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8488 := by decide +kernel

theorem rowEval8488 (x : Key → ℝ) : Integer.Sparse.eval row8488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8488, Integer.Sparse.eval_collectBalanced, rawRowCheck8488]

theorem rawRowCheck8489 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow8489 := by decide +kernel

theorem rowCheck8489 : row8489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8489 := by decide +kernel

theorem rowEval8489 (x : Key → ℝ) : Integer.Sparse.eval row8489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8489, Integer.Sparse.eval_collectBalanced, rawRowCheck8489]

theorem rawRowCheck8490 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow8490 := by decide +kernel

theorem rowCheck8490 : row8490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8490 := by decide +kernel

theorem rowEval8490 (x : Key → ℝ) : Integer.Sparse.eval row8490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8490, Integer.Sparse.eval_collectBalanced, rawRowCheck8490]

theorem rawRowCheck8491 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow8491 := by decide +kernel

theorem rowCheck8491 : row8491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8491 := by decide +kernel

theorem rowEval8491 (x : Key → ℝ) : Integer.Sparse.eval row8491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8491, Integer.Sparse.eval_collectBalanced, rawRowCheck8491]

theorem rawRowCheck8492 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow8492 := by decide +kernel

theorem rowCheck8492 : row8492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8492 := by decide +kernel

theorem rowEval8492 (x : Key → ℝ) : Integer.Sparse.eval row8492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8492, Integer.Sparse.eval_collectBalanced, rawRowCheck8492]

theorem rawRowCheck8493 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow8493 := by decide +kernel

theorem rowCheck8493 : row8493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8493 := by decide +kernel

theorem rowEval8493 (x : Key → ℝ) : Integer.Sparse.eval row8493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8493, Integer.Sparse.eval_collectBalanced, rawRowCheck8493]

theorem rawRowCheck8494 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow8494 := by decide +kernel

theorem rowCheck8494 : row8494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8494 := by decide +kernel

theorem rowEval8494 (x : Key → ℝ) : Integer.Sparse.eval row8494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8494, Integer.Sparse.eval_collectBalanced, rawRowCheck8494]

theorem rawRowCheck8495 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0 = rawRow8495 := by decide +kernel

theorem rowCheck8495 : row8495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8495 := by decide +kernel

theorem rowEval8495 (x : Key → ℝ) : Integer.Sparse.eval row8495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8495, Integer.Sparse.eval_collectBalanced, rawRowCheck8495]

theorem rawRowCheck8496 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0 = rawRow8496 := by decide +kernel

theorem rowCheck8496 : row8496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8496 := by decide +kernel

theorem rowEval8496 (x : Key → ℝ) : Integer.Sparse.eval row8496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8496, Integer.Sparse.eval_collectBalanced, rawRowCheck8496]

theorem rawRowCheck8497 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0 = rawRow8497 := by decide +kernel

theorem rowCheck8497 : row8497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8497 := by decide +kernel

theorem rowEval8497 (x : Key → ℝ) : Integer.Sparse.eval row8497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8497, Integer.Sparse.eval_collectBalanced, rawRowCheck8497]

theorem rawRowCheck8498 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0 = rawRow8498 := by decide +kernel

theorem rowCheck8498 : row8498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8498 := by decide +kernel

theorem rowEval8498 (x : Key → ℝ) : Integer.Sparse.eval row8498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8498, Integer.Sparse.eval_collectBalanced, rawRowCheck8498]

theorem rawRowCheck8499 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0 = rawRow8499 := by decide +kernel

theorem rowCheck8499 : row8499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8499 := by decide +kernel

theorem rowEval8499 (x : Key → ℝ) : Integer.Sparse.eval row8499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8499, Integer.Sparse.eval_collectBalanced, rawRowCheck8499]

theorem rawRowCheck8500 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0 = rawRow8500 := by decide +kernel

theorem rowCheck8500 : row8500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8500 := by decide +kernel

theorem rowEval8500 (x : Key → ℝ) : Integer.Sparse.eval row8500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8500, Integer.Sparse.eval_collectBalanced, rawRowCheck8500]

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

theorem rawRowCheck8661 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form0 = rawRow8661 := by decide +kernel

theorem rowCheck8661 : row8661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8661 := by decide +kernel

theorem rowEval8661 (x : Key → ℝ) : Integer.Sparse.eval row8661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8661, Integer.Sparse.eval_collectBalanced, rawRowCheck8661]

theorem rawRowCheck8662 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form0 = rawRow8662 := by decide +kernel

theorem rowCheck8662 : row8662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8662 := by decide +kernel

theorem rowEval8662 (x : Key → ℝ) : Integer.Sparse.eval row8662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8662, Integer.Sparse.eval_collectBalanced, rawRowCheck8662]

theorem rawRowCheck8663 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form0 = rawRow8663 := by decide +kernel

theorem rowCheck8663 : row8663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8663 := by decide +kernel

theorem rowEval8663 (x : Key → ℝ) : Integer.Sparse.eval row8663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8663, Integer.Sparse.eval_collectBalanced, rawRowCheck8663]

theorem rawRowCheck8664 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8664 := by decide +kernel

theorem rowCheck8664 : row8664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8664 := by decide +kernel

theorem rowEval8664 (x : Key → ℝ) : Integer.Sparse.eval row8664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8664, Integer.Sparse.eval_collectBalanced, rawRowCheck8664]

theorem rawRowCheck8665 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8665 := by decide +kernel

theorem rowCheck8665 : row8665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8665 := by decide +kernel

theorem rowEval8665 (x : Key → ℝ) : Integer.Sparse.eval row8665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8665, Integer.Sparse.eval_collectBalanced, rawRowCheck8665]

theorem rawRowCheck8666 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow8666 := by decide +kernel

theorem rowCheck8666 : row8666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8666 := by decide +kernel

theorem rowEval8666 (x : Key → ℝ) : Integer.Sparse.eval row8666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8666, Integer.Sparse.eval_collectBalanced, rawRowCheck8666]

theorem rawRowCheck8667 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow8667 := by decide +kernel

theorem rowCheck8667 : row8667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8667 := by decide +kernel

theorem rowEval8667 (x : Key → ℝ) : Integer.Sparse.eval row8667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8667, Integer.Sparse.eval_collectBalanced, rawRowCheck8667]

theorem rawRowCheck8668 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow8668 := by decide +kernel

theorem rowCheck8668 : row8668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8668 := by decide +kernel

theorem rowEval8668 (x : Key → ℝ) : Integer.Sparse.eval row8668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck8668, Integer.Sparse.eval_collectBalanced, rawRowCheck8668]

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

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8485 x
  · exact rowEval8486 x
  · exact rowEval8487 x
  · exact rowEval8488 x
  · exact rowEval8489 x
  · exact rowEval8490 x
  · exact rowEval8491 x
  · exact rowEval8492 x
  · exact rowEval8493 x
  · exact rowEval8494 x
  · exact rowEval8495 x
  · exact rowEval8496 x
  · exact rowEval8497 x
  · exact rowEval8498 x
  · exact rowEval8499 x
  · exact rowEval8500 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

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

theorem rawRowCheck8757 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8757 := by decide +kernel

theorem rowCheck8757 : row8757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8757 := by decide +kernel

theorem rowEval8757 (x : Key → ℝ) : Integer.Sparse.eval row8757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8757, Integer.Sparse.eval_collectBalanced, rawRowCheck8757]

theorem rawRowCheck8758 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow8758 := by decide +kernel

theorem rowCheck8758 : row8758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8758 := by decide +kernel

theorem rowEval8758 (x : Key → ℝ) : Integer.Sparse.eval row8758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8758, Integer.Sparse.eval_collectBalanced, rawRowCheck8758]

theorem rawRowCheck8759 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow8759 := by decide +kernel

theorem rowCheck8759 : row8759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8759 := by decide +kernel

theorem rowEval8759 (x : Key → ℝ) : Integer.Sparse.eval row8759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8759, Integer.Sparse.eval_collectBalanced, rawRowCheck8759]

theorem rawRowCheck8760 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow8760 := by decide +kernel

theorem rowCheck8760 : row8760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8760 := by decide +kernel

theorem rowEval8760 (x : Key → ℝ) : Integer.Sparse.eval row8760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck8760, Integer.Sparse.eval_collectBalanced, rawRowCheck8760]

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

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8661 x
  · exact rowEval8662 x
  · exact rowEval8663 x
  · exact rowEval8664 x
  · exact rowEval8665 x
  · exact rowEval8666 x
  · exact rowEval8667 x
  · exact rowEval8668 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

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

theorem rawRowCheck7430 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7430 := by decide +kernel

theorem rowCheck7430 : row7430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7430 := by decide +kernel

theorem rowEval7430 (x : Key → ℝ) : Integer.Sparse.eval row7430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7430, Integer.Sparse.eval_collectBalanced, rawRowCheck7430]

theorem rawRowCheck7431 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7431 := by decide +kernel

theorem rowCheck7431 : row7431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7431 := by decide +kernel

theorem rowEval7431 (x : Key → ℝ) : Integer.Sparse.eval row7431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7431, Integer.Sparse.eval_collectBalanced, rawRowCheck7431]

theorem rawRowCheck7432 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7432 := by decide +kernel

theorem rowCheck7432 : row7432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7432 := by decide +kernel

theorem rowEval7432 (x : Key → ℝ) : Integer.Sparse.eval row7432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7432, Integer.Sparse.eval_collectBalanced, rawRowCheck7432]

theorem rawRowCheck7433 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7433 := by decide +kernel

theorem rowCheck7433 : row7433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7433 := by decide +kernel

theorem rowEval7433 (x : Key → ℝ) : Integer.Sparse.eval row7433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7433, Integer.Sparse.eval_collectBalanced, rawRowCheck7433]

theorem rawRowCheck7434 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow7434 := by decide +kernel

theorem rowCheck7434 : row7434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7434 := by decide +kernel

theorem rowEval7434 (x : Key → ℝ) : Integer.Sparse.eval row7434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7434, Integer.Sparse.eval_collectBalanced, rawRowCheck7434]

theorem rawRowCheck7435 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow7435 := by decide +kernel

theorem rowCheck7435 : row7435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7435 := by decide +kernel

theorem rowEval7435 (x : Key → ℝ) : Integer.Sparse.eval row7435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7435, Integer.Sparse.eval_collectBalanced, rawRowCheck7435]

theorem rawRowCheck7436 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow7436 := by decide +kernel

theorem rowCheck7436 : row7436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7436 := by decide +kernel

theorem rowEval7436 (x : Key → ℝ) : Integer.Sparse.eval row7436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7436, Integer.Sparse.eval_collectBalanced, rawRowCheck7436]

theorem rawRowCheck7437 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7437 := by decide +kernel

theorem rowCheck7437 : row7437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7437 := by decide +kernel

theorem rowEval7437 (x : Key → ℝ) : Integer.Sparse.eval row7437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7437, Integer.Sparse.eval_collectBalanced, rawRowCheck7437]

theorem rawRowCheck7438 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7438 := by decide +kernel

theorem rowCheck7438 : row7438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7438 := by decide +kernel

theorem rowEval7438 (x : Key → ℝ) : Integer.Sparse.eval row7438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7438, Integer.Sparse.eval_collectBalanced, rawRowCheck7438]

theorem rawRowCheck7439 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7439 := by decide +kernel

theorem rowCheck7439 : row7439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7439 := by decide +kernel

theorem rowEval7439 (x : Key → ℝ) : Integer.Sparse.eval row7439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7439, Integer.Sparse.eval_collectBalanced, rawRowCheck7439]

theorem rawRowCheck7440 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0 = rawRow7440 := by decide +kernel

theorem rowCheck7440 : row7440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7440 := by decide +kernel

theorem rowEval7440 (x : Key → ℝ) : Integer.Sparse.eval row7440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7440, Integer.Sparse.eval_collectBalanced, rawRowCheck7440]

theorem rawRowCheck7441 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0 = rawRow7441 := by decide +kernel

theorem rowCheck7441 : row7441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7441 := by decide +kernel

theorem rowEval7441 (x : Key → ℝ) : Integer.Sparse.eval row7441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7441, Integer.Sparse.eval_collectBalanced, rawRowCheck7441]

theorem rawRowCheck7442 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0 = rawRow7442 := by decide +kernel

theorem rowCheck7442 : row7442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7442 := by decide +kernel

theorem rowEval7442 (x : Key → ℝ) : Integer.Sparse.eval row7442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7442, Integer.Sparse.eval_collectBalanced, rawRowCheck7442]

theorem rawRowCheck7443 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0 = rawRow7443 := by decide +kernel

theorem rowCheck7443 : row7443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7443 := by decide +kernel

theorem rowEval7443 (x : Key → ℝ) : Integer.Sparse.eval row7443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7443, Integer.Sparse.eval_collectBalanced, rawRowCheck7443]

theorem rawRowCheck7444 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0 = rawRow7444 := by decide +kernel

theorem rowCheck7444 : row7444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7444 := by decide +kernel

theorem rowEval7444 (x : Key → ℝ) : Integer.Sparse.eval row7444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7444, Integer.Sparse.eval_collectBalanced, rawRowCheck7444]

theorem rawRowCheck7445 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0 = rawRow7445 := by decide +kernel

theorem rowCheck7445 : row7445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7445 := by decide +kernel

theorem rowEval7445 (x : Key → ℝ) : Integer.Sparse.eval row7445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7445, Integer.Sparse.eval_collectBalanced, rawRowCheck7445]

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

theorem rawRowCheck8841 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow8841 := by decide +kernel

theorem rowCheck8841 : row8841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8841 := by decide +kernel

theorem rowEval8841 (x : Key → ℝ) : Integer.Sparse.eval row8841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8841, Integer.Sparse.eval_collectBalanced, rawRowCheck8841]

theorem rawRowCheck8842 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow8842 := by decide +kernel

theorem rowCheck8842 : row8842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8842 := by decide +kernel

theorem rowEval8842 (x : Key → ℝ) : Integer.Sparse.eval row8842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8842, Integer.Sparse.eval_collectBalanced, rawRowCheck8842]

theorem rawRowCheck8843 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow8843 := by decide +kernel

theorem rowCheck8843 : row8843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8843 := by decide +kernel

theorem rowEval8843 (x : Key → ℝ) : Integer.Sparse.eval row8843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8843, Integer.Sparse.eval_collectBalanced, rawRowCheck8843]

theorem rawRowCheck8844 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8844 := by decide +kernel

theorem rowCheck8844 : row8844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8844 := by decide +kernel

theorem rowEval8844 (x : Key → ℝ) : Integer.Sparse.eval row8844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8844, Integer.Sparse.eval_collectBalanced, rawRowCheck8844]

theorem rawRowCheck8845 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form0 = rawRow8845 := by decide +kernel

theorem rowCheck8845 : row8845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8845 := by decide +kernel

theorem rowEval8845 (x : Key → ℝ) : Integer.Sparse.eval row8845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8845, Integer.Sparse.eval_collectBalanced, rawRowCheck8845]

theorem rawRowCheck8846 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form0 = rawRow8846 := by decide +kernel

theorem rowCheck8846 : row8846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8846 := by decide +kernel

theorem rowEval8846 (x : Key → ℝ) : Integer.Sparse.eval row8846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8846, Integer.Sparse.eval_collectBalanced, rawRowCheck8846]

theorem rawRowCheck8847 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form0 = rawRow8847 := by decide +kernel

theorem rowCheck8847 : row8847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8847 := by decide +kernel

theorem rowEval8847 (x : Key → ℝ) : Integer.Sparse.eval row8847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8847, Integer.Sparse.eval_collectBalanced, rawRowCheck8847]

theorem rawRowCheck8848 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form0 = rawRow8848 := by decide +kernel

theorem rowCheck8848 : row8848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8848 := by decide +kernel

theorem rowEval8848 (x : Key → ℝ) : Integer.Sparse.eval row8848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8848, Integer.Sparse.eval_collectBalanced, rawRowCheck8848]

theorem rawRowCheck8849 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form0 = rawRow8849 := by decide +kernel

theorem rowCheck8849 : row8849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8849 := by decide +kernel

theorem rowEval8849 (x : Key → ℝ) : Integer.Sparse.eval row8849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8849, Integer.Sparse.eval_collectBalanced, rawRowCheck8849]

theorem rawRowCheck8850 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form0 = rawRow8850 := by decide +kernel

theorem rowCheck8850 : row8850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8850 := by decide +kernel

theorem rowEval8850 (x : Key → ℝ) : Integer.Sparse.eval row8850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8850, Integer.Sparse.eval_collectBalanced, rawRowCheck8850]

theorem rawRowCheck8851 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form0 = rawRow8851 := by decide +kernel

theorem rowCheck8851 : row8851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8851 := by decide +kernel

theorem rowEval8851 (x : Key → ℝ) : Integer.Sparse.eval row8851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8851, Integer.Sparse.eval_collectBalanced, rawRowCheck8851]

theorem rawRowCheck8852 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form0 = rawRow8852 := by decide +kernel

theorem rowCheck8852 : row8852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8852 := by decide +kernel

theorem rowEval8852 (x : Key → ℝ) : Integer.Sparse.eval row8852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8852, Integer.Sparse.eval_collectBalanced, rawRowCheck8852]

theorem rawRowCheck8853 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form0 = rawRow8853 := by decide +kernel

theorem rowCheck8853 : row8853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8853 := by decide +kernel

theorem rowEval8853 (x : Key → ℝ) : Integer.Sparse.eval row8853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8853, Integer.Sparse.eval_collectBalanced, rawRowCheck8853]

theorem rawRowCheck8854 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow8854 := by decide +kernel

theorem rowCheck8854 : row8854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8854 := by decide +kernel

theorem rowEval8854 (x : Key → ℝ) : Integer.Sparse.eval row8854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8854, Integer.Sparse.eval_collectBalanced, rawRowCheck8854]

theorem rawRowCheck8855 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow8855 := by decide +kernel

theorem rowCheck8855 : row8855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8855 := by decide +kernel

theorem rowEval8855 (x : Key → ℝ) : Integer.Sparse.eval row8855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8855, Integer.Sparse.eval_collectBalanced, rawRowCheck8855]

theorem rawRowCheck8856 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow8856 := by decide +kernel

theorem rowCheck8856 : row8856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8856 := by decide +kernel

theorem rowEval8856 (x : Key → ℝ) : Integer.Sparse.eval row8856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8856, Integer.Sparse.eval_collectBalanced, rawRowCheck8856]

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

theorem entryCheck12_0 : entry12_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_0 k)) := by decide +kernel

theorem rowsSound12_0 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7494 x
  · exact rowEval7495 x
  · exact rowEval7496 x
  · exact rowEval7497 x
  · exact rowEval8757 x
  · exact rowEval8758 x
  · exact rowEval8759 x
  · exact rowEval8760 x

theorem entryEval12_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_0 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck12_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_0]

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

theorem rawRowCheck9065 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow9065 := by decide +kernel

theorem rowCheck9065 : row9065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9065 := by decide +kernel

theorem rowEval9065 (x : Key → ℝ) : Integer.Sparse.eval row9065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9065, Integer.Sparse.eval_collectBalanced, rawRowCheck9065]

theorem rawRowCheck9066 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow9066 := by decide +kernel

theorem rowCheck9066 : row9066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9066 := by decide +kernel

theorem rowEval9066 (x : Key → ℝ) : Integer.Sparse.eval row9066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9066, Integer.Sparse.eval_collectBalanced, rawRowCheck9066]

theorem rawRowCheck9067 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow9067 := by decide +kernel

theorem rowCheck9067 : row9067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9067 := by decide +kernel

theorem rowEval9067 (x : Key → ℝ) : Integer.Sparse.eval row9067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9067, Integer.Sparse.eval_collectBalanced, rawRowCheck9067]

theorem rawRowCheck9068 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow9068 := by decide +kernel

theorem rowCheck9068 : row9068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9068 := by decide +kernel

theorem rowEval9068 (x : Key → ℝ) : Integer.Sparse.eval row9068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9068, Integer.Sparse.eval_collectBalanced, rawRowCheck9068]

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

theorem entryCheck13_0 : entry13_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_0 k)) := by decide +kernel

theorem rowsSound13_0 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8841 x
  · exact rowEval8842 x
  · exact rowEval8843 x
  · exact rowEval8844 x
  · exact rowEval8845 x
  · exact rowEval8846 x
  · exact rowEval8847 x
  · exact rowEval8848 x
  · exact rowEval8849 x
  · exact rowEval8850 x
  · exact rowEval8851 x
  · exact rowEval8852 x
  · exact rowEval8853 x
  · exact rowEval8854 x
  · exact rowEval8855 x
  · exact rowEval8856 x

theorem entryEval13_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_0 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck13_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_0]

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

theorem rawRowCheck9173 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form0 = rawRow9173 := by decide +kernel

theorem rowCheck9173 : row9173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9173 := by decide +kernel

theorem rowEval9173 (x : Key → ℝ) : Integer.Sparse.eval row9173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9173, Integer.Sparse.eval_collectBalanced, rawRowCheck9173]

theorem rawRowCheck9174 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form0 = rawRow9174 := by decide +kernel

theorem rowCheck9174 : row9174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9174 := by decide +kernel

theorem rowEval9174 (x : Key → ℝ) : Integer.Sparse.eval row9174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9174, Integer.Sparse.eval_collectBalanced, rawRowCheck9174]

theorem rawRowCheck9175 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form0 = rawRow9175 := by decide +kernel

theorem rowCheck9175 : row9175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9175 := by decide +kernel

theorem rowEval9175 (x : Key → ℝ) : Integer.Sparse.eval row9175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9175, Integer.Sparse.eval_collectBalanced, rawRowCheck9175]

theorem rawRowCheck9176 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form0 = rawRow9176 := by decide +kernel

theorem rowCheck9176 : row9176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9176 := by decide +kernel

theorem rowEval9176 (x : Key → ℝ) : Integer.Sparse.eval row9176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9176, Integer.Sparse.eval_collectBalanced, rawRowCheck9176]

theorem rawRowCheck9177 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form0 = rawRow9177 := by decide +kernel

theorem rowCheck9177 : row9177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9177 := by decide +kernel

theorem rowEval9177 (x : Key → ℝ) : Integer.Sparse.eval row9177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9177, Integer.Sparse.eval_collectBalanced, rawRowCheck9177]

theorem rawRowCheck9178 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form0 = rawRow9178 := by decide +kernel

theorem rowCheck9178 : row9178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9178 := by decide +kernel

theorem rowEval9178 (x : Key → ℝ) : Integer.Sparse.eval row9178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9178, Integer.Sparse.eval_collectBalanced, rawRowCheck9178]

theorem rawRowCheck9179 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form0 = rawRow9179 := by decide +kernel

theorem rowCheck9179 : row9179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9179 := by decide +kernel

theorem rowEval9179 (x : Key → ℝ) : Integer.Sparse.eval row9179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9179, Integer.Sparse.eval_collectBalanced, rawRowCheck9179]

theorem rawRowCheck9180 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form0 = rawRow9180 := by decide +kernel

theorem rowCheck9180 : row9180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9180 := by decide +kernel

theorem rowEval9180 (x : Key → ℝ) : Integer.Sparse.eval row9180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9180, Integer.Sparse.eval_collectBalanced, rawRowCheck9180]

theorem rawRowCheck9181 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form0 = rawRow9181 := by decide +kernel

theorem rowCheck9181 : row9181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9181 := by decide +kernel

theorem rowEval9181 (x : Key → ℝ) : Integer.Sparse.eval row9181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9181, Integer.Sparse.eval_collectBalanced, rawRowCheck9181]

theorem rawRowCheck9182 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form0 = rawRow9182 := by decide +kernel

theorem rowCheck9182 : row9182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9182 := by decide +kernel

theorem rowEval9182 (x : Key → ℝ) : Integer.Sparse.eval row9182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9182, Integer.Sparse.eval_collectBalanced, rawRowCheck9182]

theorem rawRowCheck9183 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form0 = rawRow9183 := by decide +kernel

theorem rowCheck9183 : row9183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9183 := by decide +kernel

theorem rowEval9183 (x : Key → ℝ) : Integer.Sparse.eval row9183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9183, Integer.Sparse.eval_collectBalanced, rawRowCheck9183]

theorem rawRowCheck9184 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form0 = rawRow9184 := by decide +kernel

theorem rowCheck9184 : row9184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9184 := by decide +kernel

theorem rowEval9184 (x : Key → ℝ) : Integer.Sparse.eval row9184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9184, Integer.Sparse.eval_collectBalanced, rawRowCheck9184]

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

theorem entryCheck14_0 : entry14_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_0 k)) := by decide +kernel

theorem rowsSound14_0 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7382 x
  · exact rowEval7383 x
  · exact rowEval7384 x
  · exact rowEval7385 x
  · exact rowEval9065 x
  · exact rowEval9066 x
  · exact rowEval9067 x
  · exact rowEval9068 x

theorem entryEval14_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_0 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck14_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_0]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck9381 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form0 = rawRow9381 := by decide +kernel

theorem rowCheck9381 : row9381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9381 := by decide +kernel

theorem rowEval9381 (x : Key → ℝ) : Integer.Sparse.eval row9381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9381, Integer.Sparse.eval_collectBalanced, rawRowCheck9381]

theorem rawRowCheck9382 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form0 = rawRow9382 := by decide +kernel

theorem rowCheck9382 : row9382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9382 := by decide +kernel

theorem rowEval9382 (x : Key → ℝ) : Integer.Sparse.eval row9382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9382, Integer.Sparse.eval_collectBalanced, rawRowCheck9382]

theorem rawRowCheck9383 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form0 = rawRow9383 := by decide +kernel

theorem rowCheck9383 : row9383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9383 := by decide +kernel

theorem rowEval9383 (x : Key → ℝ) : Integer.Sparse.eval row9383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9383, Integer.Sparse.eval_collectBalanced, rawRowCheck9383]

theorem rawRowCheck9384 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form0 = rawRow9384 := by decide +kernel

theorem rowCheck9384 : row9384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9384 := by decide +kernel

theorem rowEval9384 (x : Key → ℝ) : Integer.Sparse.eval row9384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9384, Integer.Sparse.eval_collectBalanced, rawRowCheck9384]

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

theorem entryCheck15_0 : entry15_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_0 k)) := by decide +kernel

theorem rowsSound15_0 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8661 x
  · exact rowEval8662 x
  · exact rowEval8663 x
  · exact rowEval8664 x
  · exact rowEval9173 x
  · exact rowEval9174 x
  · exact rowEval9175 x
  · exact rowEval9176 x
  · exact rowEval9177 x
  · exact rowEval9178 x
  · exact rowEval9179 x
  · exact rowEval9180 x
  · exact rowEval9181 x
  · exact rowEval9182 x
  · exact rowEval9183 x
  · exact rowEval9184 x

theorem entryEval15_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_0 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck15_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_0]

end MUB6.Certificate.GramEntries.Block3

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

end MUB6.Certificate.GramRows

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

theorem entryCheck16_0 : entry16_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_0 k)) := by decide +kernel

theorem rowsSound16_0 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval9381 x
  · exact rowEval9382 x
  · exact rowEval9383 x
  · exact rowEval9384 x
  · exact rowEval7430 x
  · exact rowEval7431 x
  · exact rowEval7432 x
  · exact rowEval7433 x

theorem entryEval16_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_0 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck16_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_0]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck9933 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form0 = rawRow9933 := by decide +kernel

theorem rowCheck9933 : row9933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9933 := by decide +kernel

theorem rowEval9933 (x : Key → ℝ) : Integer.Sparse.eval row9933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9933, Integer.Sparse.eval_collectBalanced, rawRowCheck9933]

theorem rawRowCheck9934 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form0 = rawRow9934 := by decide +kernel

theorem rowCheck9934 : row9934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9934 := by decide +kernel

theorem rowEval9934 (x : Key → ℝ) : Integer.Sparse.eval row9934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9934, Integer.Sparse.eval_collectBalanced, rawRowCheck9934]

theorem rawRowCheck9935 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form0 = rawRow9935 := by decide +kernel

theorem rowCheck9935 : row9935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9935 := by decide +kernel

theorem rowEval9935 (x : Key → ℝ) : Integer.Sparse.eval row9935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9935, Integer.Sparse.eval_collectBalanced, rawRowCheck9935]

theorem rawRowCheck9936 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form0 = rawRow9936 := by decide +kernel

theorem rowCheck9936 : row9936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9936 := by decide +kernel

theorem rowEval9936 (x : Key → ℝ) : Integer.Sparse.eval row9936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9936, Integer.Sparse.eval_collectBalanced, rawRowCheck9936]

theorem rawRowCheck9937 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form0 = rawRow9937 := by decide +kernel

theorem rowCheck9937 : row9937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9937 := by decide +kernel

theorem rowEval9937 (x : Key → ℝ) : Integer.Sparse.eval row9937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9937, Integer.Sparse.eval_collectBalanced, rawRowCheck9937]

theorem rawRowCheck9938 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form0 = rawRow9938 := by decide +kernel

theorem rowCheck9938 : row9938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9938 := by decide +kernel

theorem rowEval9938 (x : Key → ℝ) : Integer.Sparse.eval row9938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9938, Integer.Sparse.eval_collectBalanced, rawRowCheck9938]

theorem rawRowCheck9939 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form0 = rawRow9939 := by decide +kernel

theorem rowCheck9939 : row9939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9939 := by decide +kernel

theorem rowEval9939 (x : Key → ℝ) : Integer.Sparse.eval row9939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9939, Integer.Sparse.eval_collectBalanced, rawRowCheck9939]

theorem rawRowCheck9940 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form0 = rawRow9940 := by decide +kernel

theorem rowCheck9940 : row9940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9940 := by decide +kernel

theorem rowEval9940 (x : Key → ℝ) : Integer.Sparse.eval row9940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9940, Integer.Sparse.eval_collectBalanced, rawRowCheck9940]

theorem rawRowCheck9941 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form0 = rawRow9941 := by decide +kernel

theorem rowCheck9941 : row9941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9941 := by decide +kernel

theorem rowEval9941 (x : Key → ℝ) : Integer.Sparse.eval row9941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9941, Integer.Sparse.eval_collectBalanced, rawRowCheck9941]

theorem rawRowCheck9942 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form0 = rawRow9942 := by decide +kernel

theorem rowCheck9942 : row9942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9942 := by decide +kernel

theorem rowEval9942 (x : Key → ℝ) : Integer.Sparse.eval row9942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9942, Integer.Sparse.eval_collectBalanced, rawRowCheck9942]

theorem rawRowCheck9943 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form0 = rawRow9943 := by decide +kernel

theorem rowCheck9943 : row9943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9943 := by decide +kernel

theorem rowEval9943 (x : Key → ℝ) : Integer.Sparse.eval row9943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9943, Integer.Sparse.eval_collectBalanced, rawRowCheck9943]

theorem rawRowCheck9944 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form0 = rawRow9944 := by decide +kernel

theorem rowCheck9944 : row9944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9944 := by decide +kernel

theorem rowEval9944 (x : Key → ℝ) : Integer.Sparse.eval row9944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9944, Integer.Sparse.eval_collectBalanced, rawRowCheck9944]

theorem rawRowCheck9945 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form0 = rawRow9945 := by decide +kernel

theorem rowCheck9945 : row9945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9945 := by decide +kernel

theorem rowEval9945 (x : Key → ℝ) : Integer.Sparse.eval row9945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9945, Integer.Sparse.eval_collectBalanced, rawRowCheck9945]

theorem rawRowCheck9946 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form0 = rawRow9946 := by decide +kernel

theorem rowCheck9946 : row9946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9946 := by decide +kernel

theorem rowEval9946 (x : Key → ℝ) : Integer.Sparse.eval row9946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9946, Integer.Sparse.eval_collectBalanced, rawRowCheck9946]

theorem rawRowCheck9947 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form0 = rawRow9947 := by decide +kernel

theorem rowCheck9947 : row9947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9947 := by decide +kernel

theorem rowEval9947 (x : Key → ℝ) : Integer.Sparse.eval row9947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9947, Integer.Sparse.eval_collectBalanced, rawRowCheck9947]

theorem rawRowCheck9948 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form0 = rawRow9948 := by decide +kernel

theorem rowCheck9948 : row9948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9948 := by decide +kernel

theorem rowEval9948 (x : Key → ℝ) : Integer.Sparse.eval row9948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9948, Integer.Sparse.eval_collectBalanced, rawRowCheck9948]

theorem rawRowCheck9949 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form0 = rawRow9949 := by decide +kernel

theorem rowCheck9949 : row9949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9949 := by decide +kernel

theorem rowEval9949 (x : Key → ℝ) : Integer.Sparse.eval row9949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9949, Integer.Sparse.eval_collectBalanced, rawRowCheck9949]

theorem rawRowCheck9950 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form0 = rawRow9950 := by decide +kernel

theorem rowCheck9950 : row9950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9950 := by decide +kernel

theorem rowEval9950 (x : Key → ℝ) : Integer.Sparse.eval row9950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9950, Integer.Sparse.eval_collectBalanced, rawRowCheck9950]

theorem rawRowCheck9951 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form0 = rawRow9951 := by decide +kernel

theorem rowCheck9951 : row9951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9951 := by decide +kernel

theorem rowEval9951 (x : Key → ℝ) : Integer.Sparse.eval row9951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9951, Integer.Sparse.eval_collectBalanced, rawRowCheck9951]

theorem rawRowCheck9952 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form0 = rawRow9952 := by decide +kernel

theorem rowCheck9952 : row9952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9952 := by decide +kernel

theorem rowEval9952 (x : Key → ℝ) : Integer.Sparse.eval row9952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9952, Integer.Sparse.eval_collectBalanced, rawRowCheck9952]

theorem rawRowCheck9953 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form0 = rawRow9953 := by decide +kernel

theorem rowCheck9953 : row9953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9953 := by decide +kernel

theorem rowEval9953 (x : Key → ℝ) : Integer.Sparse.eval row9953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9953, Integer.Sparse.eval_collectBalanced, rawRowCheck9953]

theorem rawRowCheck9954 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form0 = rawRow9954 := by decide +kernel

theorem rowCheck9954 : row9954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9954 := by decide +kernel

theorem rowEval9954 (x : Key → ℝ) : Integer.Sparse.eval row9954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9954, Integer.Sparse.eval_collectBalanced, rawRowCheck9954]

theorem rawRowCheck9955 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form0 = rawRow9955 := by decide +kernel

theorem rowCheck9955 : row9955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9955 := by decide +kernel

theorem rowEval9955 (x : Key → ℝ) : Integer.Sparse.eval row9955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9955, Integer.Sparse.eval_collectBalanced, rawRowCheck9955]

theorem rawRowCheck9956 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form0 = rawRow9956 := by decide +kernel

theorem rowCheck9956 : row9956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9956 := by decide +kernel

theorem rowEval9956 (x : Key → ℝ) : Integer.Sparse.eval row9956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9956, Integer.Sparse.eval_collectBalanced, rawRowCheck9956]

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

theorem rawRowCheck10389 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form0 = rawRow10389 := by decide +kernel

theorem rowCheck10389 : row10389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10389 := by decide +kernel

theorem rowEval10389 (x : Key → ℝ) : Integer.Sparse.eval row10389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10389, Integer.Sparse.eval_collectBalanced, rawRowCheck10389]

theorem rawRowCheck10390 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form0 = rawRow10390 := by decide +kernel

theorem rowCheck10390 : row10390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10390 := by decide +kernel

theorem rowEval10390 (x : Key → ℝ) : Integer.Sparse.eval row10390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10390, Integer.Sparse.eval_collectBalanced, rawRowCheck10390]

theorem rawRowCheck10391 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form0 = rawRow10391 := by decide +kernel

theorem rowCheck10391 : row10391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10391 := by decide +kernel

theorem rowEval10391 (x : Key → ℝ) : Integer.Sparse.eval row10391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10391, Integer.Sparse.eval_collectBalanced, rawRowCheck10391]

theorem rawRowCheck10392 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form0 = rawRow10392 := by decide +kernel

theorem rowCheck10392 : row10392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10392 := by decide +kernel

theorem rowEval10392 (x : Key → ℝ) : Integer.Sparse.eval row10392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10392, Integer.Sparse.eval_collectBalanced, rawRowCheck10392]

theorem rawRowCheck10393 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form0 = rawRow10393 := by decide +kernel

theorem rowCheck10393 : row10393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10393 := by decide +kernel

theorem rowEval10393 (x : Key → ℝ) : Integer.Sparse.eval row10393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10393, Integer.Sparse.eval_collectBalanced, rawRowCheck10393]

theorem rawRowCheck10394 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form0 = rawRow10394 := by decide +kernel

theorem rowCheck10394 : row10394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10394 := by decide +kernel

theorem rowEval10394 (x : Key → ℝ) : Integer.Sparse.eval row10394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10394, Integer.Sparse.eval_collectBalanced, rawRowCheck10394]

theorem rawRowCheck10395 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form0 = rawRow10395 := by decide +kernel

theorem rowCheck10395 : row10395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10395 := by decide +kernel

theorem rowEval10395 (x : Key → ℝ) : Integer.Sparse.eval row10395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10395, Integer.Sparse.eval_collectBalanced, rawRowCheck10395]

theorem rawRowCheck10396 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form0 = rawRow10396 := by decide +kernel

theorem rowCheck10396 : row10396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10396 := by decide +kernel

theorem rowEval10396 (x : Key → ℝ) : Integer.Sparse.eval row10396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10396, Integer.Sparse.eval_collectBalanced, rawRowCheck10396]

theorem rawRowCheck10397 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form0 = rawRow10397 := by decide +kernel

theorem rowCheck10397 : row10397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10397 := by decide +kernel

theorem rowEval10397 (x : Key → ℝ) : Integer.Sparse.eval row10397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10397, Integer.Sparse.eval_collectBalanced, rawRowCheck10397]

theorem rawRowCheck10398 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form0 = rawRow10398 := by decide +kernel

theorem rowCheck10398 : row10398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10398 := by decide +kernel

theorem rowEval10398 (x : Key → ℝ) : Integer.Sparse.eval row10398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10398, Integer.Sparse.eval_collectBalanced, rawRowCheck10398]

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

theorem entryCheck18_0 : entry18_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_0 k)) := by decide +kernel

theorem rowsSound18_0 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval9933 x
  · exact rowEval9934 x
  · exact rowEval9935 x
  · exact rowEval9936 x
  · exact rowEval9937 x
  · exact rowEval9938 x
  · exact rowEval9939 x
  · exact rowEval9940 x
  · exact rowEval9941 x
  · exact rowEval9942 x
  · exact rowEval9943 x
  · exact rowEval9944 x
  · exact rowEval9945 x
  · exact rowEval9946 x
  · exact rowEval9947 x
  · exact rowEval9948 x
  · exact rowEval9949 x
  · exact rowEval9950 x
  · exact rowEval9951 x
  · exact rowEval9952 x
  · exact rowEval9953 x
  · exact rowEval9954 x
  · exact rowEval9955 x
  · exact rowEval9956 x

theorem entryEval18_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_0 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck18_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_0]

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

theorem rawRowCheck10589 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow10589 := by decide +kernel

theorem rowCheck10589 : row10589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10589 := by decide +kernel

theorem rowEval10589 (x : Key → ℝ) : Integer.Sparse.eval row10589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10589, Integer.Sparse.eval_collectBalanced, rawRowCheck10589]

theorem rawRowCheck10590 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow10590 := by decide +kernel

theorem rowCheck10590 : row10590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10590 := by decide +kernel

theorem rowEval10590 (x : Key → ℝ) : Integer.Sparse.eval row10590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10590, Integer.Sparse.eval_collectBalanced, rawRowCheck10590]

theorem rawRowCheck10591 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow10591 := by decide +kernel

theorem rowCheck10591 : row10591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10591 := by decide +kernel

theorem rowEval10591 (x : Key → ℝ) : Integer.Sparse.eval row10591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10591, Integer.Sparse.eval_collectBalanced, rawRowCheck10591]

theorem rawRowCheck10592 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow10592 := by decide +kernel

theorem rowCheck10592 : row10592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10592 := by decide +kernel

theorem rowEval10592 (x : Key → ℝ) : Integer.Sparse.eval row10592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10592, Integer.Sparse.eval_collectBalanced, rawRowCheck10592]

theorem rawRowCheck10593 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow10593 := by decide +kernel

theorem rowCheck10593 : row10593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10593 := by decide +kernel

theorem rowEval10593 (x : Key → ℝ) : Integer.Sparse.eval row10593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10593, Integer.Sparse.eval_collectBalanced, rawRowCheck10593]

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

theorem entryCheck19_0 : entry19_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_0 k)) := by decide +kernel

theorem rowsSound19_0 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval10389 x
  · exact rowEval10390 x
  · exact rowEval10391 x
  · exact rowEval10392 x
  · exact rowEval10393 x
  · exact rowEval10394 x
  · exact rowEval10395 x
  · exact rowEval10396 x
  · exact rowEval10397 x
  · exact rowEval10398 x

theorem entryEval19_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_0 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck19_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_0]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block3.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form2.terms k).tag (GramFunctions.Block3.form2.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7382 x
  · exact rowEval7383 x
  · exact rowEval7384 x
  · exact rowEval7385 x
  · exact rowEval7386 x
  · exact rowEval7387 x
  · exact rowEval7388 x
  · exact rowEval7389 x
  · exact rowEval7390 x
  · exact rowEval7391 x
  · exact rowEval7392 x
  · exact rowEval7393 x
  · exact rowEval7394 x
  · exact rowEval7395 x
  · exact rowEval7396 x
  · exact rowEval7397 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block3.form2.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form2 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

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

theorem entryCheck20_0 : entry20_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_0 k)) := by decide +kernel

theorem rowsSound20_0 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval10589 x
  · exact rowEval10590 x
  · exact rowEval10591 x
  · exact rowEval10592 x
  · exact rowEval10593 x

theorem entryEval20_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_0 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck20_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_0]

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

theorem rawRowCheck12206 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow12206 := by decide +kernel

theorem rowCheck12206 : row12206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12206 := by decide +kernel

theorem rowEval12206 (x : Key → ℝ) : Integer.Sparse.eval row12206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12206, Integer.Sparse.eval_collectBalanced, rawRowCheck12206]

theorem rawRowCheck12207 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow12207 := by decide +kernel

theorem rowCheck12207 : row12207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12207 := by decide +kernel

theorem rowEval12207 (x : Key → ℝ) : Integer.Sparse.eval row12207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12207, Integer.Sparse.eval_collectBalanced, rawRowCheck12207]

theorem rawRowCheck12208 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow12208 := by decide +kernel

theorem rowCheck12208 : row12208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12208 := by decide +kernel

theorem rowEval12208 (x : Key → ℝ) : Integer.Sparse.eval row12208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12208, Integer.Sparse.eval_collectBalanced, rawRowCheck12208]

theorem rawRowCheck12209 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow12209 := by decide +kernel

theorem rowCheck12209 : row12209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12209 := by decide +kernel

theorem rowEval12209 (x : Key → ℝ) : Integer.Sparse.eval row12209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12209, Integer.Sparse.eval_collectBalanced, rawRowCheck12209]

theorem rawRowCheck12210 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow12210 := by decide +kernel

theorem rowCheck12210 : row12210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12210 := by decide +kernel

theorem rowEval12210 (x : Key → ℝ) : Integer.Sparse.eval row12210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12210, Integer.Sparse.eval_collectBalanced, rawRowCheck12210]

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

theorem rawRowCheck12331 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form0 = rawRow12331 := by decide +kernel

theorem rowCheck12331 : row12331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12331 := by decide +kernel

theorem rowEval12331 (x : Key → ℝ) : Integer.Sparse.eval row12331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12331, Integer.Sparse.eval_collectBalanced, rawRowCheck12331]

theorem rawRowCheck12332 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form0 = rawRow12332 := by decide +kernel

theorem rowCheck12332 : row12332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12332 := by decide +kernel

theorem rowEval12332 (x : Key → ℝ) : Integer.Sparse.eval row12332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12332, Integer.Sparse.eval_collectBalanced, rawRowCheck12332]

theorem rawRowCheck12333 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form0 = rawRow12333 := by decide +kernel

theorem rowCheck12333 : row12333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12333 := by decide +kernel

theorem rowEval12333 (x : Key → ℝ) : Integer.Sparse.eval row12333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12333, Integer.Sparse.eval_collectBalanced, rawRowCheck12333]

theorem rawRowCheck12334 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form0 = rawRow12334 := by decide +kernel

theorem rowCheck12334 : row12334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12334 := by decide +kernel

theorem rowEval12334 (x : Key → ℝ) : Integer.Sparse.eval row12334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12334, Integer.Sparse.eval_collectBalanced, rawRowCheck12334]

theorem rawRowCheck12335 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form0 = rawRow12335 := by decide +kernel

theorem rowCheck12335 : row12335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12335 := by decide +kernel

theorem rowEval12335 (x : Key → ℝ) : Integer.Sparse.eval row12335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12335, Integer.Sparse.eval_collectBalanced, rawRowCheck12335]

theorem rawRowCheck12336 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form0 = rawRow12336 := by decide +kernel

theorem rowCheck12336 : row12336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12336 := by decide +kernel

theorem rowEval12336 (x : Key → ℝ) : Integer.Sparse.eval row12336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12336, Integer.Sparse.eval_collectBalanced, rawRowCheck12336]

theorem rawRowCheck12337 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form0 = rawRow12337 := by decide +kernel

theorem rowCheck12337 : row12337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12337 := by decide +kernel

theorem rowEval12337 (x : Key → ℝ) : Integer.Sparse.eval row12337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12337, Integer.Sparse.eval_collectBalanced, rawRowCheck12337]

theorem rawRowCheck12338 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form0 = rawRow12338 := by decide +kernel

theorem rowCheck12338 : row12338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12338 := by decide +kernel

theorem rowEval12338 (x : Key → ℝ) : Integer.Sparse.eval row12338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12338, Integer.Sparse.eval_collectBalanced, rawRowCheck12338]

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

theorem entryCheck24_0 : entry24_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_0 k)) := by decide +kernel

theorem rowsSound24_0 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval12206 x
  · exact rowEval12207 x
  · exact rowEval12208 x
  · exact rowEval12209 x
  · exact rowEval12210 x

theorem entryEval24_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_0 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck24_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_0]

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

theorem entryCheck25_0 : entry25_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_0 k)) := by decide +kernel

theorem rowsSound25_0 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval12331 x
  · exact rowEval12332 x
  · exact rowEval12333 x
  · exact rowEval12334 x
  · exact rowEval12335 x
  · exact rowEval12336 x
  · exact rowEval12337 x
  · exact rowEval12338 x

theorem entryEval25_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_0 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck25_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_0]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7430 x
  · exact rowEval7431 x
  · exact rowEval7432 x
  · exact rowEval7433 x
  · exact rowEval7434 x
  · exact rowEval7435 x
  · exact rowEval7436 x
  · exact rowEval7437 x
  · exact rowEval7438 x
  · exact rowEval7439 x
  · exact rowEval7440 x
  · exact rowEval7441 x
  · exact rowEval7442 x
  · exact rowEval7443 x
  · exact rowEval7444 x
  · exact rowEval7445 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

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

theorem rawRowCheck7790 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7790 := by decide +kernel

theorem rowCheck7790 : row7790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7790 := by decide +kernel

theorem rowEval7790 (x : Key → ℝ) : Integer.Sparse.eval row7790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7790, Integer.Sparse.eval_collectBalanced, rawRowCheck7790]

theorem rawRowCheck7791 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7791 := by decide +kernel

theorem rowCheck7791 : row7791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7791 := by decide +kernel

theorem rowEval7791 (x : Key → ℝ) : Integer.Sparse.eval row7791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7791, Integer.Sparse.eval_collectBalanced, rawRowCheck7791]

theorem rawRowCheck7792 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7792 := by decide +kernel

theorem rowCheck7792 : row7792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7792 := by decide +kernel

theorem rowEval7792 (x : Key → ℝ) : Integer.Sparse.eval row7792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7792, Integer.Sparse.eval_collectBalanced, rawRowCheck7792]

theorem rawRowCheck7793 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7793 := by decide +kernel

theorem rowCheck7793 : row7793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7793 := by decide +kernel

theorem rowEval7793 (x : Key → ℝ) : Integer.Sparse.eval row7793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7793, Integer.Sparse.eval_collectBalanced, rawRowCheck7793]

theorem rawRowCheck7794 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7794 := by decide +kernel

theorem rowCheck7794 : row7794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7794 := by decide +kernel

theorem rowEval7794 (x : Key → ℝ) : Integer.Sparse.eval row7794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7794, Integer.Sparse.eval_collectBalanced, rawRowCheck7794]

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

theorem entryCheck6_0 : entry6_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_0 k)) := by decide +kernel

theorem rowsSound6_0 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7790 x
  · exact rowEval7791 x
  · exact rowEval7792 x
  · exact rowEval7793 x
  · exact rowEval7794 x

theorem entryEval6_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_0 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck6_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_0]

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

theorem entryEvalRow0_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 0).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval0_0 B hB
  · exact (entryEval1_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval2_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e_oai
