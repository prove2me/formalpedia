-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:13:48.867436+00:00
-- url     : https://prove2.me/submissions/8328de08-625e-4a96-81d2-ec43fec53e2e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E030
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E057
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_18_e

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

theorem rawRowCheck9957 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1 = rawRow9957 := by decide +kernel

theorem rowCheck9957 : row9957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9957 := by decide +kernel

theorem rowEval9957 (x : Key → ℝ) : Integer.Sparse.eval row9957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9957, Integer.Sparse.eval_collectBalanced, rawRowCheck9957]

theorem rawRowCheck9958 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1 = rawRow9958 := by decide +kernel

theorem rowCheck9958 : row9958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9958 := by decide +kernel

theorem rowEval9958 (x : Key → ℝ) : Integer.Sparse.eval row9958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9958, Integer.Sparse.eval_collectBalanced, rawRowCheck9958]

theorem rawRowCheck9959 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1 = rawRow9959 := by decide +kernel

theorem rowCheck9959 : row9959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9959 := by decide +kernel

theorem rowEval9959 (x : Key → ℝ) : Integer.Sparse.eval row9959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9959, Integer.Sparse.eval_collectBalanced, rawRowCheck9959]

theorem rawRowCheck9960 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1 = rawRow9960 := by decide +kernel

theorem rowCheck9960 : row9960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9960 := by decide +kernel

theorem rowEval9960 (x : Key → ℝ) : Integer.Sparse.eval row9960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9960, Integer.Sparse.eval_collectBalanced, rawRowCheck9960]

theorem rawRowCheck9961 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1 = rawRow9961 := by decide +kernel

theorem rowCheck9961 : row9961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9961 := by decide +kernel

theorem rowEval9961 (x : Key → ℝ) : Integer.Sparse.eval row9961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9961, Integer.Sparse.eval_collectBalanced, rawRowCheck9961]

theorem rawRowCheck9962 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1 = rawRow9962 := by decide +kernel

theorem rowCheck9962 : row9962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9962 := by decide +kernel

theorem rowEval9962 (x : Key → ℝ) : Integer.Sparse.eval row9962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9962, Integer.Sparse.eval_collectBalanced, rawRowCheck9962]

theorem rawRowCheck9963 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9963 := by decide +kernel

theorem rowCheck9963 : row9963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9963 := by decide +kernel

theorem rowEval9963 (x : Key → ℝ) : Integer.Sparse.eval row9963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9963, Integer.Sparse.eval_collectBalanced, rawRowCheck9963]

theorem rawRowCheck9964 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9964 := by decide +kernel

theorem rowCheck9964 : row9964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9964 := by decide +kernel

theorem rowEval9964 (x : Key → ℝ) : Integer.Sparse.eval row9964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9964, Integer.Sparse.eval_collectBalanced, rawRowCheck9964]

theorem rawRowCheck9965 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9965 := by decide +kernel

theorem rowCheck9965 : row9965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9965 := by decide +kernel

theorem rowEval9965 (x : Key → ℝ) : Integer.Sparse.eval row9965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9965, Integer.Sparse.eval_collectBalanced, rawRowCheck9965]

theorem rawRowCheck9966 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9966 := by decide +kernel

theorem rowCheck9966 : row9966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9966 := by decide +kernel

theorem rowEval9966 (x : Key → ℝ) : Integer.Sparse.eval row9966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9966, Integer.Sparse.eval_collectBalanced, rawRowCheck9966]

theorem rawRowCheck9967 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9967 := by decide +kernel

theorem rowCheck9967 : row9967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9967 := by decide +kernel

theorem rowEval9967 (x : Key → ℝ) : Integer.Sparse.eval row9967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9967, Integer.Sparse.eval_collectBalanced, rawRowCheck9967]

theorem rawRowCheck9968 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9968 := by decide +kernel

theorem rowCheck9968 : row9968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9968 := by decide +kernel

theorem rowEval9968 (x : Key → ℝ) : Integer.Sparse.eval row9968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9968, Integer.Sparse.eval_collectBalanced, rawRowCheck9968]

theorem rawRowCheck9969 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form1 = rawRow9969 := by decide +kernel

theorem rowCheck9969 : row9969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9969 := by decide +kernel

theorem rowEval9969 (x : Key → ℝ) : Integer.Sparse.eval row9969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9969, Integer.Sparse.eval_collectBalanced, rawRowCheck9969]

theorem rawRowCheck9970 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form1 = rawRow9970 := by decide +kernel

theorem rowCheck9970 : row9970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9970 := by decide +kernel

theorem rowEval9970 (x : Key → ℝ) : Integer.Sparse.eval row9970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9970, Integer.Sparse.eval_collectBalanced, rawRowCheck9970]

theorem rawRowCheck9971 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form1 = rawRow9971 := by decide +kernel

theorem rowCheck9971 : row9971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9971 := by decide +kernel

theorem rowEval9971 (x : Key → ℝ) : Integer.Sparse.eval row9971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9971, Integer.Sparse.eval_collectBalanced, rawRowCheck9971]

theorem rawRowCheck9972 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form1 = rawRow9972 := by decide +kernel

theorem rowCheck9972 : row9972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9972 := by decide +kernel

theorem rowEval9972 (x : Key → ℝ) : Integer.Sparse.eval row9972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9972, Integer.Sparse.eval_collectBalanced, rawRowCheck9972]

theorem rawRowCheck9973 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form1 = rawRow9973 := by decide +kernel

theorem rowCheck9973 : row9973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9973 := by decide +kernel

theorem rowEval9973 (x : Key → ℝ) : Integer.Sparse.eval row9973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9973, Integer.Sparse.eval_collectBalanced, rawRowCheck9973]

theorem rawRowCheck9974 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form1 = rawRow9974 := by decide +kernel

theorem rowCheck9974 : row9974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9974 := by decide +kernel

theorem rowEval9974 (x : Key → ℝ) : Integer.Sparse.eval row9974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9974, Integer.Sparse.eval_collectBalanced, rawRowCheck9974]

theorem rawRowCheck9975 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form1 = rawRow9975 := by decide +kernel

theorem rowCheck9975 : row9975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9975 := by decide +kernel

theorem rowEval9975 (x : Key → ℝ) : Integer.Sparse.eval row9975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9975, Integer.Sparse.eval_collectBalanced, rawRowCheck9975]

theorem rawRowCheck9976 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form1 = rawRow9976 := by decide +kernel

theorem rowCheck9976 : row9976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9976 := by decide +kernel

theorem rowEval9976 (x : Key → ℝ) : Integer.Sparse.eval row9976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9976, Integer.Sparse.eval_collectBalanced, rawRowCheck9976]

theorem rawRowCheck9977 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form1 = rawRow9977 := by decide +kernel

theorem rowCheck9977 : row9977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9977 := by decide +kernel

theorem rowEval9977 (x : Key → ℝ) : Integer.Sparse.eval row9977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9977, Integer.Sparse.eval_collectBalanced, rawRowCheck9977]

theorem rawRowCheck9978 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9978 := by decide +kernel

theorem rowCheck9978 : row9978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9978 := by decide +kernel

theorem rowEval9978 (x : Key → ℝ) : Integer.Sparse.eval row9978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9978, Integer.Sparse.eval_collectBalanced, rawRowCheck9978]

theorem rawRowCheck9979 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9979 := by decide +kernel

theorem rowCheck9979 : row9979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9979 := by decide +kernel

theorem rowEval9979 (x : Key → ℝ) : Integer.Sparse.eval row9979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9979, Integer.Sparse.eval_collectBalanced, rawRowCheck9979]

theorem rawRowCheck9980 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9980 := by decide +kernel

theorem rowCheck9980 : row9980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9980 := by decide +kernel

theorem rowEval9980 (x : Key → ℝ) : Integer.Sparse.eval row9980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9980, Integer.Sparse.eval_collectBalanced, rawRowCheck9980]

theorem rawRowCheck9981 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2 = rawRow9981 := by decide +kernel

theorem rowCheck9981 : row9981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9981 := by decide +kernel

theorem rowEval9981 (x : Key → ℝ) : Integer.Sparse.eval row9981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9981, Integer.Sparse.eval_collectBalanced, rawRowCheck9981]

theorem rawRowCheck9982 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2 = rawRow9982 := by decide +kernel

theorem rowCheck9982 : row9982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9982 := by decide +kernel

theorem rowEval9982 (x : Key → ℝ) : Integer.Sparse.eval row9982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9982, Integer.Sparse.eval_collectBalanced, rawRowCheck9982]

theorem rawRowCheck9983 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2 = rawRow9983 := by decide +kernel

theorem rowCheck9983 : row9983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9983 := by decide +kernel

theorem rowEval9983 (x : Key → ℝ) : Integer.Sparse.eval row9983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9983, Integer.Sparse.eval_collectBalanced, rawRowCheck9983]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck9984 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2 = rawRow9984 := by decide +kernel

theorem rowCheck9984 : row9984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9984 := by decide +kernel

theorem rowEval9984 (x : Key → ℝ) : Integer.Sparse.eval row9984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9984, Integer.Sparse.eval_collectBalanced, rawRowCheck9984]

theorem rawRowCheck9985 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2 = rawRow9985 := by decide +kernel

theorem rowCheck9985 : row9985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9985 := by decide +kernel

theorem rowEval9985 (x : Key → ℝ) : Integer.Sparse.eval row9985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9985, Integer.Sparse.eval_collectBalanced, rawRowCheck9985]

theorem rawRowCheck9986 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2 = rawRow9986 := by decide +kernel

theorem rowCheck9986 : row9986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9986 := by decide +kernel

theorem rowEval9986 (x : Key → ℝ) : Integer.Sparse.eval row9986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9986, Integer.Sparse.eval_collectBalanced, rawRowCheck9986]

theorem rawRowCheck9987 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9987 := by decide +kernel

theorem rowCheck9987 : row9987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9987 := by decide +kernel

theorem rowEval9987 (x : Key → ℝ) : Integer.Sparse.eval row9987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9987, Integer.Sparse.eval_collectBalanced, rawRowCheck9987]

theorem rawRowCheck9988 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9988 := by decide +kernel

theorem rowCheck9988 : row9988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9988 := by decide +kernel

theorem rowEval9988 (x : Key → ℝ) : Integer.Sparse.eval row9988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9988, Integer.Sparse.eval_collectBalanced, rawRowCheck9988]

theorem rawRowCheck9989 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9989 := by decide +kernel

theorem rowCheck9989 : row9989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9989 := by decide +kernel

theorem rowEval9989 (x : Key → ℝ) : Integer.Sparse.eval row9989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9989, Integer.Sparse.eval_collectBalanced, rawRowCheck9989]

theorem rawRowCheck9990 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9990 := by decide +kernel

theorem rowCheck9990 : row9990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9990 := by decide +kernel

theorem rowEval9990 (x : Key → ℝ) : Integer.Sparse.eval row9990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9990, Integer.Sparse.eval_collectBalanced, rawRowCheck9990]

theorem rawRowCheck9991 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2 = rawRow9991 := by decide +kernel

theorem rowCheck9991 : row9991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9991 := by decide +kernel

theorem rowEval9991 (x : Key → ℝ) : Integer.Sparse.eval row9991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9991, Integer.Sparse.eval_collectBalanced, rawRowCheck9991]

theorem rawRowCheck9992 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2 = rawRow9992 := by decide +kernel

theorem rowCheck9992 : row9992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9992 := by decide +kernel

theorem rowEval9992 (x : Key → ℝ) : Integer.Sparse.eval row9992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9992, Integer.Sparse.eval_collectBalanced, rawRowCheck9992]

theorem rawRowCheck9993 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form2 = rawRow9993 := by decide +kernel

theorem rowCheck9993 : row9993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9993 := by decide +kernel

theorem rowEval9993 (x : Key → ℝ) : Integer.Sparse.eval row9993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9993, Integer.Sparse.eval_collectBalanced, rawRowCheck9993]

theorem rawRowCheck9994 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form2 = rawRow9994 := by decide +kernel

theorem rowCheck9994 : row9994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9994 := by decide +kernel

theorem rowEval9994 (x : Key → ℝ) : Integer.Sparse.eval row9994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9994, Integer.Sparse.eval_collectBalanced, rawRowCheck9994]

theorem rawRowCheck9995 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form2 = rawRow9995 := by decide +kernel

theorem rowCheck9995 : row9995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9995 := by decide +kernel

theorem rowEval9995 (x : Key → ℝ) : Integer.Sparse.eval row9995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9995, Integer.Sparse.eval_collectBalanced, rawRowCheck9995]

theorem rawRowCheck9996 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9996 := by decide +kernel

theorem rowCheck9996 : row9996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9996 := by decide +kernel

theorem rowEval9996 (x : Key → ℝ) : Integer.Sparse.eval row9996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9996, Integer.Sparse.eval_collectBalanced, rawRowCheck9996]

theorem rawRowCheck9997 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9997 := by decide +kernel

theorem rowCheck9997 : row9997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9997 := by decide +kernel

theorem rowEval9997 (x : Key → ℝ) : Integer.Sparse.eval row9997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9997, Integer.Sparse.eval_collectBalanced, rawRowCheck9997]

theorem rawRowCheck9998 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9998 := by decide +kernel

theorem rowCheck9998 : row9998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9998 := by decide +kernel

theorem rowEval9998 (x : Key → ℝ) : Integer.Sparse.eval row9998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9998, Integer.Sparse.eval_collectBalanced, rawRowCheck9998]

theorem rawRowCheck9999 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9999 := by decide +kernel

theorem rowCheck9999 : row9999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9999 := by decide +kernel

theorem rowEval9999 (x : Key → ℝ) : Integer.Sparse.eval row9999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9999, Integer.Sparse.eval_collectBalanced, rawRowCheck9999]

theorem rawRowCheck10000 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form2 = rawRow10000 := by decide +kernel

theorem rowCheck10000 : row10000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10000 := by decide +kernel

theorem rowEval10000 (x : Key → ℝ) : Integer.Sparse.eval row10000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10000, Integer.Sparse.eval_collectBalanced, rawRowCheck10000]

theorem rawRowCheck10001 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form2 = rawRow10001 := by decide +kernel

theorem rowCheck10001 : row10001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10001 := by decide +kernel

theorem rowEval10001 (x : Key → ℝ) : Integer.Sparse.eval row10001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck10001, Integer.Sparse.eval_collectBalanced, rawRowCheck10001]

theorem rawRowCheck10002 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form2 = rawRow10002 := by decide +kernel

theorem rowCheck10002 : row10002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10002 := by decide +kernel

theorem rowEval10002 (x : Key → ℝ) : Integer.Sparse.eval row10002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10002, Integer.Sparse.eval_collectBalanced, rawRowCheck10002]

theorem rawRowCheck10003 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form2 = rawRow10003 := by decide +kernel

theorem rowCheck10003 : row10003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10003 := by decide +kernel

theorem rowEval10003 (x : Key → ℝ) : Integer.Sparse.eval row10003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10003, Integer.Sparse.eval_collectBalanced, rawRowCheck10003]

theorem rawRowCheck10004 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form2 = rawRow10004 := by decide +kernel

theorem rowCheck10004 : row10004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10004 := by decide +kernel

theorem rowEval10004 (x : Key → ℝ) : Integer.Sparse.eval row10004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck10004, Integer.Sparse.eval_collectBalanced, rawRowCheck10004]

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

theorem rawRowCheck10077 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6 = rawRow10077 := by decide +kernel

theorem rowCheck10077 : row10077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10077 := by decide +kernel

theorem rowEval10077 (x : Key → ℝ) : Integer.Sparse.eval row10077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10077, Integer.Sparse.eval_collectBalanced, rawRowCheck10077]

theorem rawRowCheck10078 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6 = rawRow10078 := by decide +kernel

theorem rowCheck10078 : row10078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10078 := by decide +kernel

theorem rowEval10078 (x : Key → ℝ) : Integer.Sparse.eval row10078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10078, Integer.Sparse.eval_collectBalanced, rawRowCheck10078]

theorem rawRowCheck10079 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6 = rawRow10079 := by decide +kernel

theorem rowCheck10079 : row10079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10079 := by decide +kernel

theorem rowEval10079 (x : Key → ℝ) : Integer.Sparse.eval row10079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10079, Integer.Sparse.eval_collectBalanced, rawRowCheck10079]

theorem rawRowCheck10080 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6 = rawRow10080 := by decide +kernel

theorem rowCheck10080 : row10080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10080 := by decide +kernel

theorem rowEval10080 (x : Key → ℝ) : Integer.Sparse.eval row10080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10080, Integer.Sparse.eval_collectBalanced, rawRowCheck10080]

theorem rawRowCheck10081 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6 = rawRow10081 := by decide +kernel

theorem rowCheck10081 : row10081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10081 := by decide +kernel

theorem rowEval10081 (x : Key → ℝ) : Integer.Sparse.eval row10081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10081, Integer.Sparse.eval_collectBalanced, rawRowCheck10081]

theorem rawRowCheck10082 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6 = rawRow10082 := by decide +kernel

theorem rowCheck10082 : row10082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10082 := by decide +kernel

theorem rowEval10082 (x : Key → ℝ) : Integer.Sparse.eval row10082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10082, Integer.Sparse.eval_collectBalanced, rawRowCheck10082]

theorem rawRowCheck10083 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6 = rawRow10083 := by decide +kernel

theorem rowCheck10083 : row10083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10083 := by decide +kernel

theorem rowEval10083 (x : Key → ℝ) : Integer.Sparse.eval row10083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10083, Integer.Sparse.eval_collectBalanced, rawRowCheck10083]

theorem rawRowCheck10084 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6 = rawRow10084 := by decide +kernel

theorem rowCheck10084 : row10084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10084 := by decide +kernel

theorem rowEval10084 (x : Key → ℝ) : Integer.Sparse.eval row10084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10084, Integer.Sparse.eval_collectBalanced, rawRowCheck10084]

theorem rawRowCheck10085 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6 = rawRow10085 := by decide +kernel

theorem rowCheck10085 : row10085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10085 := by decide +kernel

theorem rowEval10085 (x : Key → ℝ) : Integer.Sparse.eval row10085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10085, Integer.Sparse.eval_collectBalanced, rawRowCheck10085]

theorem rawRowCheck10086 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6 = rawRow10086 := by decide +kernel

theorem rowCheck10086 : row10086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10086 := by decide +kernel

theorem rowEval10086 (x : Key → ℝ) : Integer.Sparse.eval row10086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10086, Integer.Sparse.eval_collectBalanced, rawRowCheck10086]

theorem rawRowCheck10087 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6 = rawRow10087 := by decide +kernel

theorem rowCheck10087 : row10087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10087 := by decide +kernel

theorem rowEval10087 (x : Key → ℝ) : Integer.Sparse.eval row10087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10087, Integer.Sparse.eval_collectBalanced, rawRowCheck10087]

theorem rawRowCheck10088 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6 = rawRow10088 := by decide +kernel

theorem rowCheck10088 : row10088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10088 := by decide +kernel

theorem rowEval10088 (x : Key → ℝ) : Integer.Sparse.eval row10088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10088, Integer.Sparse.eval_collectBalanced, rawRowCheck10088]

theorem rawRowCheck10089 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form6 = rawRow10089 := by decide +kernel

theorem rowCheck10089 : row10089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10089 := by decide +kernel

theorem rowEval10089 (x : Key → ℝ) : Integer.Sparse.eval row10089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10089, Integer.Sparse.eval_collectBalanced, rawRowCheck10089]

theorem rawRowCheck10090 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form6 = rawRow10090 := by decide +kernel

theorem rowCheck10090 : row10090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10090 := by decide +kernel

theorem rowEval10090 (x : Key → ℝ) : Integer.Sparse.eval row10090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10090, Integer.Sparse.eval_collectBalanced, rawRowCheck10090]

theorem rawRowCheck10091 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form6 = rawRow10091 := by decide +kernel

theorem rowCheck10091 : row10091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10091 := by decide +kernel

theorem rowEval10091 (x : Key → ℝ) : Integer.Sparse.eval row10091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10091, Integer.Sparse.eval_collectBalanced, rawRowCheck10091]

theorem rawRowCheck10092 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form6 = rawRow10092 := by decide +kernel

theorem rowCheck10092 : row10092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10092 := by decide +kernel

theorem rowEval10092 (x : Key → ℝ) : Integer.Sparse.eval row10092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10092, Integer.Sparse.eval_collectBalanced, rawRowCheck10092]

theorem rawRowCheck10093 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form6 = rawRow10093 := by decide +kernel

theorem rowCheck10093 : row10093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10093 := by decide +kernel

theorem rowEval10093 (x : Key → ℝ) : Integer.Sparse.eval row10093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10093, Integer.Sparse.eval_collectBalanced, rawRowCheck10093]

theorem rawRowCheck10094 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form6 = rawRow10094 := by decide +kernel

theorem rowCheck10094 : row10094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10094 := by decide +kernel

theorem rowEval10094 (x : Key → ℝ) : Integer.Sparse.eval row10094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10094, Integer.Sparse.eval_collectBalanced, rawRowCheck10094]

theorem rawRowCheck10095 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form6 = rawRow10095 := by decide +kernel

theorem rowCheck10095 : row10095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10095 := by decide +kernel

theorem rowEval10095 (x : Key → ℝ) : Integer.Sparse.eval row10095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10095, Integer.Sparse.eval_collectBalanced, rawRowCheck10095]

theorem rawRowCheck10096 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form6 = rawRow10096 := by decide +kernel

theorem rowCheck10096 : row10096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10096 := by decide +kernel

theorem rowEval10096 (x : Key → ℝ) : Integer.Sparse.eval row10096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10096, Integer.Sparse.eval_collectBalanced, rawRowCheck10096]

theorem rawRowCheck10097 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form6 = rawRow10097 := by decide +kernel

theorem rowCheck10097 : row10097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10097 := by decide +kernel

theorem rowEval10097 (x : Key → ℝ) : Integer.Sparse.eval row10097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10097, Integer.Sparse.eval_collectBalanced, rawRowCheck10097]

theorem rawRowCheck10098 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form6 = rawRow10098 := by decide +kernel

theorem rowCheck10098 : row10098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10098 := by decide +kernel

theorem rowEval10098 (x : Key → ℝ) : Integer.Sparse.eval row10098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10098, Integer.Sparse.eval_collectBalanced, rawRowCheck10098]

theorem rawRowCheck10099 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form6 = rawRow10099 := by decide +kernel

theorem rowCheck10099 : row10099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10099 := by decide +kernel

theorem rowEval10099 (x : Key → ℝ) : Integer.Sparse.eval row10099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10099, Integer.Sparse.eval_collectBalanced, rawRowCheck10099]

theorem rawRowCheck10100 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form6 = rawRow10100 := by decide +kernel

theorem rowCheck10100 : row10100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10100 := by decide +kernel

theorem rowEval10100 (x : Key → ℝ) : Integer.Sparse.eval row10100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10100, Integer.Sparse.eval_collectBalanced, rawRowCheck10100]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10221 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12 = rawRow10221 := by decide +kernel

theorem rowCheck10221 : row10221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10221 := by decide +kernel

theorem rowEval10221 (x : Key → ℝ) : Integer.Sparse.eval row10221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10221, Integer.Sparse.eval_collectBalanced, rawRowCheck10221]

theorem rawRowCheck10222 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12 = rawRow10222 := by decide +kernel

theorem rowCheck10222 : row10222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10222 := by decide +kernel

theorem rowEval10222 (x : Key → ℝ) : Integer.Sparse.eval row10222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10222, Integer.Sparse.eval_collectBalanced, rawRowCheck10222]

theorem rawRowCheck10223 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12 = rawRow10223 := by decide +kernel

theorem rowCheck10223 : row10223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10223 := by decide +kernel

theorem rowEval10223 (x : Key → ℝ) : Integer.Sparse.eval row10223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10223, Integer.Sparse.eval_collectBalanced, rawRowCheck10223]

theorem rawRowCheck10224 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12 = rawRow10224 := by decide +kernel

theorem rowCheck10224 : row10224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10224 := by decide +kernel

theorem rowEval10224 (x : Key → ℝ) : Integer.Sparse.eval row10224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10224, Integer.Sparse.eval_collectBalanced, rawRowCheck10224]

theorem rawRowCheck10225 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12 = rawRow10225 := by decide +kernel

theorem rowCheck10225 : row10225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10225 := by decide +kernel

theorem rowEval10225 (x : Key → ℝ) : Integer.Sparse.eval row10225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10225, Integer.Sparse.eval_collectBalanced, rawRowCheck10225]

theorem rawRowCheck10226 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12 = rawRow10226 := by decide +kernel

theorem rowCheck10226 : row10226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10226 := by decide +kernel

theorem rowEval10226 (x : Key → ℝ) : Integer.Sparse.eval row10226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10226, Integer.Sparse.eval_collectBalanced, rawRowCheck10226]

theorem rawRowCheck10227 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12 = rawRow10227 := by decide +kernel

theorem rowCheck10227 : row10227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10227 := by decide +kernel

theorem rowEval10227 (x : Key → ℝ) : Integer.Sparse.eval row10227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10227, Integer.Sparse.eval_collectBalanced, rawRowCheck10227]

theorem rawRowCheck10228 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12 = rawRow10228 := by decide +kernel

theorem rowCheck10228 : row10228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10228 := by decide +kernel

theorem rowEval10228 (x : Key → ℝ) : Integer.Sparse.eval row10228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10228, Integer.Sparse.eval_collectBalanced, rawRowCheck10228]

theorem rawRowCheck10229 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12 = rawRow10229 := by decide +kernel

theorem rowCheck10229 : row10229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10229 := by decide +kernel

theorem rowEval10229 (x : Key → ℝ) : Integer.Sparse.eval row10229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10229, Integer.Sparse.eval_collectBalanced, rawRowCheck10229]

theorem rawRowCheck10230 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12 = rawRow10230 := by decide +kernel

theorem rowCheck10230 : row10230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10230 := by decide +kernel

theorem rowEval10230 (x : Key → ℝ) : Integer.Sparse.eval row10230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10230, Integer.Sparse.eval_collectBalanced, rawRowCheck10230]

theorem rawRowCheck10231 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12 = rawRow10231 := by decide +kernel

theorem rowCheck10231 : row10231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10231 := by decide +kernel

theorem rowEval10231 (x : Key → ℝ) : Integer.Sparse.eval row10231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10231, Integer.Sparse.eval_collectBalanced, rawRowCheck10231]

theorem rawRowCheck10232 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12 = rawRow10232 := by decide +kernel

theorem rowCheck10232 : row10232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10232 := by decide +kernel

theorem rowEval10232 (x : Key → ℝ) : Integer.Sparse.eval row10232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10232, Integer.Sparse.eval_collectBalanced, rawRowCheck10232]

theorem rawRowCheck10233 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form12 = rawRow10233 := by decide +kernel

theorem rowCheck10233 : row10233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10233 := by decide +kernel

theorem rowEval10233 (x : Key → ℝ) : Integer.Sparse.eval row10233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10233, Integer.Sparse.eval_collectBalanced, rawRowCheck10233]

theorem rawRowCheck10234 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form12 = rawRow10234 := by decide +kernel

theorem rowCheck10234 : row10234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10234 := by decide +kernel

theorem rowEval10234 (x : Key → ℝ) : Integer.Sparse.eval row10234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10234, Integer.Sparse.eval_collectBalanced, rawRowCheck10234]

theorem rawRowCheck10235 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form12 = rawRow10235 := by decide +kernel

theorem rowCheck10235 : row10235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10235 := by decide +kernel

theorem rowEval10235 (x : Key → ℝ) : Integer.Sparse.eval row10235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10235, Integer.Sparse.eval_collectBalanced, rawRowCheck10235]

theorem rawRowCheck10236 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form12 = rawRow10236 := by decide +kernel

theorem rowCheck10236 : row10236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10236 := by decide +kernel

theorem rowEval10236 (x : Key → ℝ) : Integer.Sparse.eval row10236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10236, Integer.Sparse.eval_collectBalanced, rawRowCheck10236]

theorem rawRowCheck10237 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form12 = rawRow10237 := by decide +kernel

theorem rowCheck10237 : row10237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10237 := by decide +kernel

theorem rowEval10237 (x : Key → ℝ) : Integer.Sparse.eval row10237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10237, Integer.Sparse.eval_collectBalanced, rawRowCheck10237]

theorem rawRowCheck10238 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form12 = rawRow10238 := by decide +kernel

theorem rowCheck10238 : row10238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10238 := by decide +kernel

theorem rowEval10238 (x : Key → ℝ) : Integer.Sparse.eval row10238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10238, Integer.Sparse.eval_collectBalanced, rawRowCheck10238]

theorem rawRowCheck10239 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form12 = rawRow10239 := by decide +kernel

theorem rowCheck10239 : row10239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10239 := by decide +kernel

theorem rowEval10239 (x : Key → ℝ) : Integer.Sparse.eval row10239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10239, Integer.Sparse.eval_collectBalanced, rawRowCheck10239]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck10240 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form12 = rawRow10240 := by decide +kernel

theorem rowCheck10240 : row10240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10240 := by decide +kernel

theorem rowEval10240 (x : Key → ℝ) : Integer.Sparse.eval row10240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10240, Integer.Sparse.eval_collectBalanced, rawRowCheck10240]

theorem rawRowCheck10241 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form12 = rawRow10241 := by decide +kernel

theorem rowCheck10241 : row10241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10241 := by decide +kernel

theorem rowEval10241 (x : Key → ℝ) : Integer.Sparse.eval row10241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10241, Integer.Sparse.eval_collectBalanced, rawRowCheck10241]

theorem rawRowCheck10242 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form12 = rawRow10242 := by decide +kernel

theorem rowCheck10242 : row10242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10242 := by decide +kernel

theorem rowEval10242 (x : Key → ℝ) : Integer.Sparse.eval row10242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10242, Integer.Sparse.eval_collectBalanced, rawRowCheck10242]

theorem rawRowCheck10243 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form12 = rawRow10243 := by decide +kernel

theorem rowCheck10243 : row10243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10243 := by decide +kernel

theorem rowEval10243 (x : Key → ℝ) : Integer.Sparse.eval row10243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10243, Integer.Sparse.eval_collectBalanced, rawRowCheck10243]

theorem rawRowCheck10244 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form12 = rawRow10244 := by decide +kernel

theorem rowCheck10244 : row10244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10244 := by decide +kernel

theorem rowEval10244 (x : Key → ℝ) : Integer.Sparse.eval row10244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10244, Integer.Sparse.eval_collectBalanced, rawRowCheck10244]

theorem rawRowCheck10269 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14 = rawRow10269 := by decide +kernel

theorem rowCheck10269 : row10269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10269 := by decide +kernel

theorem rowEval10269 (x : Key → ℝ) : Integer.Sparse.eval row10269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10269, Integer.Sparse.eval_collectBalanced, rawRowCheck10269]

theorem rawRowCheck10270 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14 = rawRow10270 := by decide +kernel

theorem rowCheck10270 : row10270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10270 := by decide +kernel

theorem rowEval10270 (x : Key → ℝ) : Integer.Sparse.eval row10270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10270, Integer.Sparse.eval_collectBalanced, rawRowCheck10270]

theorem rawRowCheck10271 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14 = rawRow10271 := by decide +kernel

theorem rowCheck10271 : row10271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10271 := by decide +kernel

theorem rowEval10271 (x : Key → ℝ) : Integer.Sparse.eval row10271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10271, Integer.Sparse.eval_collectBalanced, rawRowCheck10271]

theorem rawRowCheck10272 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14 = rawRow10272 := by decide +kernel

theorem rowCheck10272 : row10272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10272 := by decide +kernel

theorem rowEval10272 (x : Key → ℝ) : Integer.Sparse.eval row10272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10272, Integer.Sparse.eval_collectBalanced, rawRowCheck10272]

theorem rawRowCheck10273 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14 = rawRow10273 := by decide +kernel

theorem rowCheck10273 : row10273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10273 := by decide +kernel

theorem rowEval10273 (x : Key → ℝ) : Integer.Sparse.eval row10273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10273, Integer.Sparse.eval_collectBalanced, rawRowCheck10273]

theorem rawRowCheck10274 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14 = rawRow10274 := by decide +kernel

theorem rowCheck10274 : row10274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10274 := by decide +kernel

theorem rowEval10274 (x : Key → ℝ) : Integer.Sparse.eval row10274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10274, Integer.Sparse.eval_collectBalanced, rawRowCheck10274]

theorem rawRowCheck10275 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14 = rawRow10275 := by decide +kernel

theorem rowCheck10275 : row10275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10275 := by decide +kernel

theorem rowEval10275 (x : Key → ℝ) : Integer.Sparse.eval row10275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10275, Integer.Sparse.eval_collectBalanced, rawRowCheck10275]

theorem rawRowCheck10276 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14 = rawRow10276 := by decide +kernel

theorem rowCheck10276 : row10276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10276 := by decide +kernel

theorem rowEval10276 (x : Key → ℝ) : Integer.Sparse.eval row10276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10276, Integer.Sparse.eval_collectBalanced, rawRowCheck10276]

theorem rawRowCheck10277 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14 = rawRow10277 := by decide +kernel

theorem rowCheck10277 : row10277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10277 := by decide +kernel

theorem rowEval10277 (x : Key → ℝ) : Integer.Sparse.eval row10277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10277, Integer.Sparse.eval_collectBalanced, rawRowCheck10277]

theorem rawRowCheck10278 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14 = rawRow10278 := by decide +kernel

theorem rowCheck10278 : row10278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10278 := by decide +kernel

theorem rowEval10278 (x : Key → ℝ) : Integer.Sparse.eval row10278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10278, Integer.Sparse.eval_collectBalanced, rawRowCheck10278]

theorem rawRowCheck10279 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14 = rawRow10279 := by decide +kernel

theorem rowCheck10279 : row10279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10279 := by decide +kernel

theorem rowEval10279 (x : Key → ℝ) : Integer.Sparse.eval row10279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10279, Integer.Sparse.eval_collectBalanced, rawRowCheck10279]

theorem rawRowCheck10280 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14 = rawRow10280 := by decide +kernel

theorem rowCheck10280 : row10280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10280 := by decide +kernel

theorem rowEval10280 (x : Key → ℝ) : Integer.Sparse.eval row10280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10280, Integer.Sparse.eval_collectBalanced, rawRowCheck10280]

theorem rawRowCheck10281 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form14 = rawRow10281 := by decide +kernel

theorem rowCheck10281 : row10281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10281 := by decide +kernel

theorem rowEval10281 (x : Key → ℝ) : Integer.Sparse.eval row10281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10281, Integer.Sparse.eval_collectBalanced, rawRowCheck10281]

theorem rawRowCheck10282 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form14 = rawRow10282 := by decide +kernel

theorem rowCheck10282 : row10282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10282 := by decide +kernel

theorem rowEval10282 (x : Key → ℝ) : Integer.Sparse.eval row10282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10282, Integer.Sparse.eval_collectBalanced, rawRowCheck10282]

theorem rawRowCheck10283 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form14 = rawRow10283 := by decide +kernel

theorem rowCheck10283 : row10283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10283 := by decide +kernel

theorem rowEval10283 (x : Key → ℝ) : Integer.Sparse.eval row10283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10283, Integer.Sparse.eval_collectBalanced, rawRowCheck10283]

theorem rawRowCheck10284 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form14 = rawRow10284 := by decide +kernel

theorem rowCheck10284 : row10284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10284 := by decide +kernel

theorem rowEval10284 (x : Key → ℝ) : Integer.Sparse.eval row10284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10284, Integer.Sparse.eval_collectBalanced, rawRowCheck10284]

theorem rawRowCheck10285 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form14 = rawRow10285 := by decide +kernel

theorem rowCheck10285 : row10285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10285 := by decide +kernel

theorem rowEval10285 (x : Key → ℝ) : Integer.Sparse.eval row10285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10285, Integer.Sparse.eval_collectBalanced, rawRowCheck10285]

theorem rawRowCheck10286 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form14 = rawRow10286 := by decide +kernel

theorem rowCheck10286 : row10286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10286 := by decide +kernel

theorem rowEval10286 (x : Key → ℝ) : Integer.Sparse.eval row10286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10286, Integer.Sparse.eval_collectBalanced, rawRowCheck10286]

theorem rawRowCheck10287 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form14 = rawRow10287 := by decide +kernel

theorem rowCheck10287 : row10287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10287 := by decide +kernel

theorem rowEval10287 (x : Key → ℝ) : Integer.Sparse.eval row10287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10287, Integer.Sparse.eval_collectBalanced, rawRowCheck10287]

theorem rawRowCheck10288 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form14 = rawRow10288 := by decide +kernel

theorem rowCheck10288 : row10288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10288 := by decide +kernel

theorem rowEval10288 (x : Key → ℝ) : Integer.Sparse.eval row10288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10288, Integer.Sparse.eval_collectBalanced, rawRowCheck10288]

theorem rawRowCheck10289 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form14 = rawRow10289 := by decide +kernel

theorem rowCheck10289 : row10289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10289 := by decide +kernel

theorem rowEval10289 (x : Key → ℝ) : Integer.Sparse.eval row10289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10289, Integer.Sparse.eval_collectBalanced, rawRowCheck10289]

theorem rawRowCheck10290 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form14 = rawRow10290 := by decide +kernel

theorem rowCheck10290 : row10290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10290 := by decide +kernel

theorem rowEval10290 (x : Key → ℝ) : Integer.Sparse.eval row10290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10290, Integer.Sparse.eval_collectBalanced, rawRowCheck10290]

theorem rawRowCheck10291 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form14 = rawRow10291 := by decide +kernel

theorem rowCheck10291 : row10291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10291 := by decide +kernel

theorem rowEval10291 (x : Key → ℝ) : Integer.Sparse.eval row10291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10291, Integer.Sparse.eval_collectBalanced, rawRowCheck10291]

theorem rawRowCheck10292 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form14 = rawRow10292 := by decide +kernel

theorem rowCheck10292 : row10292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10292 := by decide +kernel

theorem rowEval10292 (x : Key → ℝ) : Integer.Sparse.eval row10292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10292, Integer.Sparse.eval_collectBalanced, rawRowCheck10292]

theorem rawRowCheck10293 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15 = rawRow10293 := by decide +kernel

theorem rowCheck10293 : row10293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10293 := by decide +kernel

theorem rowEval10293 (x : Key → ℝ) : Integer.Sparse.eval row10293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10293, Integer.Sparse.eval_collectBalanced, rawRowCheck10293]

theorem rawRowCheck10294 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15 = rawRow10294 := by decide +kernel

theorem rowCheck10294 : row10294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10294 := by decide +kernel

theorem rowEval10294 (x : Key → ℝ) : Integer.Sparse.eval row10294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10294, Integer.Sparse.eval_collectBalanced, rawRowCheck10294]

theorem rawRowCheck10295 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15 = rawRow10295 := by decide +kernel

theorem rowCheck10295 : row10295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10295 := by decide +kernel

theorem rowEval10295 (x : Key → ℝ) : Integer.Sparse.eval row10295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10295, Integer.Sparse.eval_collectBalanced, rawRowCheck10295]

theorem rawRowCheck10296 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15 = rawRow10296 := by decide +kernel

theorem rowCheck10296 : row10296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10296 := by decide +kernel

theorem rowEval10296 (x : Key → ℝ) : Integer.Sparse.eval row10296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10296, Integer.Sparse.eval_collectBalanced, rawRowCheck10296]

theorem rawRowCheck10297 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15 = rawRow10297 := by decide +kernel

theorem rowCheck10297 : row10297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10297 := by decide +kernel

theorem rowEval10297 (x : Key → ℝ) : Integer.Sparse.eval row10297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10297, Integer.Sparse.eval_collectBalanced, rawRowCheck10297]

theorem rawRowCheck10298 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15 = rawRow10298 := by decide +kernel

theorem rowCheck10298 : row10298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10298 := by decide +kernel

theorem rowEval10298 (x : Key → ℝ) : Integer.Sparse.eval row10298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10298, Integer.Sparse.eval_collectBalanced, rawRowCheck10298]

theorem rawRowCheck10299 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15 = rawRow10299 := by decide +kernel

theorem rowCheck10299 : row10299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10299 := by decide +kernel

theorem rowEval10299 (x : Key → ℝ) : Integer.Sparse.eval row10299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10299, Integer.Sparse.eval_collectBalanced, rawRowCheck10299]

theorem rawRowCheck10300 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15 = rawRow10300 := by decide +kernel

theorem rowCheck10300 : row10300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10300 := by decide +kernel

theorem rowEval10300 (x : Key → ℝ) : Integer.Sparse.eval row10300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10300, Integer.Sparse.eval_collectBalanced, rawRowCheck10300]

theorem rawRowCheck10301 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15 = rawRow10301 := by decide +kernel

theorem rowCheck10301 : row10301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10301 := by decide +kernel

theorem rowEval10301 (x : Key → ℝ) : Integer.Sparse.eval row10301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10301, Integer.Sparse.eval_collectBalanced, rawRowCheck10301]

theorem rawRowCheck10302 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15 = rawRow10302 := by decide +kernel

theorem rowCheck10302 : row10302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10302 := by decide +kernel

theorem rowEval10302 (x : Key → ℝ) : Integer.Sparse.eval row10302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10302, Integer.Sparse.eval_collectBalanced, rawRowCheck10302]

theorem rawRowCheck10303 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15 = rawRow10303 := by decide +kernel

theorem rowCheck10303 : row10303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10303 := by decide +kernel

theorem rowEval10303 (x : Key → ℝ) : Integer.Sparse.eval row10303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10303, Integer.Sparse.eval_collectBalanced, rawRowCheck10303]

theorem rawRowCheck10304 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15 = rawRow10304 := by decide +kernel

theorem rowCheck10304 : row10304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10304 := by decide +kernel

theorem rowEval10304 (x : Key → ℝ) : Integer.Sparse.eval row10304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10304, Integer.Sparse.eval_collectBalanced, rawRowCheck10304]

theorem rawRowCheck10305 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form15 = rawRow10305 := by decide +kernel

theorem rowCheck10305 : row10305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10305 := by decide +kernel

theorem rowEval10305 (x : Key → ℝ) : Integer.Sparse.eval row10305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10305, Integer.Sparse.eval_collectBalanced, rawRowCheck10305]

theorem rawRowCheck10306 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form15 = rawRow10306 := by decide +kernel

theorem rowCheck10306 : row10306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10306 := by decide +kernel

theorem rowEval10306 (x : Key → ℝ) : Integer.Sparse.eval row10306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10306, Integer.Sparse.eval_collectBalanced, rawRowCheck10306]

theorem rawRowCheck10307 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form15 = rawRow10307 := by decide +kernel

theorem rowCheck10307 : row10307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10307 := by decide +kernel

theorem rowEval10307 (x : Key → ℝ) : Integer.Sparse.eval row10307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10307, Integer.Sparse.eval_collectBalanced, rawRowCheck10307]

theorem rawRowCheck10308 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form15 = rawRow10308 := by decide +kernel

theorem rowCheck10308 : row10308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10308 := by decide +kernel

theorem rowEval10308 (x : Key → ℝ) : Integer.Sparse.eval row10308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10308, Integer.Sparse.eval_collectBalanced, rawRowCheck10308]

theorem rawRowCheck10309 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form15 = rawRow10309 := by decide +kernel

theorem rowCheck10309 : row10309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10309 := by decide +kernel

theorem rowEval10309 (x : Key → ℝ) : Integer.Sparse.eval row10309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10309, Integer.Sparse.eval_collectBalanced, rawRowCheck10309]

theorem rawRowCheck10310 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form15 = rawRow10310 := by decide +kernel

theorem rowCheck10310 : row10310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10310 := by decide +kernel

theorem rowEval10310 (x : Key → ℝ) : Integer.Sparse.eval row10310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10310, Integer.Sparse.eval_collectBalanced, rawRowCheck10310]

theorem rawRowCheck10311 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form15 = rawRow10311 := by decide +kernel

theorem rowCheck10311 : row10311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10311 := by decide +kernel

theorem rowEval10311 (x : Key → ℝ) : Integer.Sparse.eval row10311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10311, Integer.Sparse.eval_collectBalanced, rawRowCheck10311]

theorem rawRowCheck10312 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form15 = rawRow10312 := by decide +kernel

theorem rowCheck10312 : row10312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10312 := by decide +kernel

theorem rowEval10312 (x : Key → ℝ) : Integer.Sparse.eval row10312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10312, Integer.Sparse.eval_collectBalanced, rawRowCheck10312]

theorem rawRowCheck10313 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form15 = rawRow10313 := by decide +kernel

theorem rowCheck10313 : row10313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10313 := by decide +kernel

theorem rowEval10313 (x : Key → ℝ) : Integer.Sparse.eval row10313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10313, Integer.Sparse.eval_collectBalanced, rawRowCheck10313]

theorem rawRowCheck10314 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form15 = rawRow10314 := by decide +kernel

theorem rowCheck10314 : row10314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10314 := by decide +kernel

theorem rowEval10314 (x : Key → ℝ) : Integer.Sparse.eval row10314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10314, Integer.Sparse.eval_collectBalanced, rawRowCheck10314]

theorem rawRowCheck10315 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form15 = rawRow10315 := by decide +kernel

theorem rowCheck10315 : row10315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10315 := by decide +kernel

theorem rowEval10315 (x : Key → ℝ) : Integer.Sparse.eval row10315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10315, Integer.Sparse.eval_collectBalanced, rawRowCheck10315]

theorem rawRowCheck10316 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form15 = rawRow10316 := by decide +kernel

theorem rowCheck10316 : row10316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10316 := by decide +kernel

theorem rowEval10316 (x : Key → ℝ) : Integer.Sparse.eval row10316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10316, Integer.Sparse.eval_collectBalanced, rawRowCheck10316]

theorem rawRowCheck10317 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16 = rawRow10317 := by decide +kernel

theorem rowCheck10317 : row10317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10317 := by decide +kernel

theorem rowEval10317 (x : Key → ℝ) : Integer.Sparse.eval row10317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10317, Integer.Sparse.eval_collectBalanced, rawRowCheck10317]

theorem rawRowCheck10318 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16 = rawRow10318 := by decide +kernel

theorem rowCheck10318 : row10318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10318 := by decide +kernel

theorem rowEval10318 (x : Key → ℝ) : Integer.Sparse.eval row10318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10318, Integer.Sparse.eval_collectBalanced, rawRowCheck10318]

theorem rawRowCheck10319 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16 = rawRow10319 := by decide +kernel

theorem rowCheck10319 : row10319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10319 := by decide +kernel

theorem rowEval10319 (x : Key → ℝ) : Integer.Sparse.eval row10319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10319, Integer.Sparse.eval_collectBalanced, rawRowCheck10319]

theorem rawRowCheck10320 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16 = rawRow10320 := by decide +kernel

theorem rowCheck10320 : row10320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10320 := by decide +kernel

theorem rowEval10320 (x : Key → ℝ) : Integer.Sparse.eval row10320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10320, Integer.Sparse.eval_collectBalanced, rawRowCheck10320]

theorem rawRowCheck10321 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16 = rawRow10321 := by decide +kernel

theorem rowCheck10321 : row10321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10321 := by decide +kernel

theorem rowEval10321 (x : Key → ℝ) : Integer.Sparse.eval row10321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10321, Integer.Sparse.eval_collectBalanced, rawRowCheck10321]

theorem rawRowCheck10322 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16 = rawRow10322 := by decide +kernel

theorem rowCheck10322 : row10322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10322 := by decide +kernel

theorem rowEval10322 (x : Key → ℝ) : Integer.Sparse.eval row10322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10322, Integer.Sparse.eval_collectBalanced, rawRowCheck10322]

theorem rawRowCheck10323 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16 = rawRow10323 := by decide +kernel

theorem rowCheck10323 : row10323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10323 := by decide +kernel

theorem rowEval10323 (x : Key → ℝ) : Integer.Sparse.eval row10323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10323, Integer.Sparse.eval_collectBalanced, rawRowCheck10323]

theorem rawRowCheck10324 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16 = rawRow10324 := by decide +kernel

theorem rowCheck10324 : row10324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10324 := by decide +kernel

theorem rowEval10324 (x : Key → ℝ) : Integer.Sparse.eval row10324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10324, Integer.Sparse.eval_collectBalanced, rawRowCheck10324]

theorem rawRowCheck10325 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16 = rawRow10325 := by decide +kernel

theorem rowCheck10325 : row10325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10325 := by decide +kernel

theorem rowEval10325 (x : Key → ℝ) : Integer.Sparse.eval row10325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10325, Integer.Sparse.eval_collectBalanced, rawRowCheck10325]

theorem rawRowCheck10326 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16 = rawRow10326 := by decide +kernel

theorem rowCheck10326 : row10326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10326 := by decide +kernel

theorem rowEval10326 (x : Key → ℝ) : Integer.Sparse.eval row10326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10326, Integer.Sparse.eval_collectBalanced, rawRowCheck10326]

theorem rawRowCheck10327 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16 = rawRow10327 := by decide +kernel

theorem rowCheck10327 : row10327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10327 := by decide +kernel

theorem rowEval10327 (x : Key → ℝ) : Integer.Sparse.eval row10327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10327, Integer.Sparse.eval_collectBalanced, rawRowCheck10327]

theorem rawRowCheck10328 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16 = rawRow10328 := by decide +kernel

theorem rowCheck10328 : row10328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10328 := by decide +kernel

theorem rowEval10328 (x : Key → ℝ) : Integer.Sparse.eval row10328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10328, Integer.Sparse.eval_collectBalanced, rawRowCheck10328]

theorem rawRowCheck10329 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form16 = rawRow10329 := by decide +kernel

theorem rowCheck10329 : row10329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10329 := by decide +kernel

theorem rowEval10329 (x : Key → ℝ) : Integer.Sparse.eval row10329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10329, Integer.Sparse.eval_collectBalanced, rawRowCheck10329]

theorem rawRowCheck10330 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form16 = rawRow10330 := by decide +kernel

theorem rowCheck10330 : row10330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10330 := by decide +kernel

theorem rowEval10330 (x : Key → ℝ) : Integer.Sparse.eval row10330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10330, Integer.Sparse.eval_collectBalanced, rawRowCheck10330]

theorem rawRowCheck10331 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form16 = rawRow10331 := by decide +kernel

theorem rowCheck10331 : row10331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10331 := by decide +kernel

theorem rowEval10331 (x : Key → ℝ) : Integer.Sparse.eval row10331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10331, Integer.Sparse.eval_collectBalanced, rawRowCheck10331]

theorem rawRowCheck10332 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form16 = rawRow10332 := by decide +kernel

theorem rowCheck10332 : row10332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10332 := by decide +kernel

theorem rowEval10332 (x : Key → ℝ) : Integer.Sparse.eval row10332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10332, Integer.Sparse.eval_collectBalanced, rawRowCheck10332]

theorem rawRowCheck10333 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form16 = rawRow10333 := by decide +kernel

theorem rowCheck10333 : row10333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10333 := by decide +kernel

theorem rowEval10333 (x : Key → ℝ) : Integer.Sparse.eval row10333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10333, Integer.Sparse.eval_collectBalanced, rawRowCheck10333]

theorem rawRowCheck10334 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form16 = rawRow10334 := by decide +kernel

theorem rowCheck10334 : row10334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10334 := by decide +kernel

theorem rowEval10334 (x : Key → ℝ) : Integer.Sparse.eval row10334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10334, Integer.Sparse.eval_collectBalanced, rawRowCheck10334]

theorem rawRowCheck10335 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form16 = rawRow10335 := by decide +kernel

theorem rowCheck10335 : row10335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10335 := by decide +kernel

theorem rowEval10335 (x : Key → ℝ) : Integer.Sparse.eval row10335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10335, Integer.Sparse.eval_collectBalanced, rawRowCheck10335]

theorem rawRowCheck10336 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form16 = rawRow10336 := by decide +kernel

theorem rowCheck10336 : row10336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10336 := by decide +kernel

theorem rowEval10336 (x : Key → ℝ) : Integer.Sparse.eval row10336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10336, Integer.Sparse.eval_collectBalanced, rawRowCheck10336]

theorem rawRowCheck10337 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form16 = rawRow10337 := by decide +kernel

theorem rowCheck10337 : row10337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10337 := by decide +kernel

theorem rowEval10337 (x : Key → ℝ) : Integer.Sparse.eval row10337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10337, Integer.Sparse.eval_collectBalanced, rawRowCheck10337]

theorem rawRowCheck10338 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form16 = rawRow10338 := by decide +kernel

theorem rowCheck10338 : row10338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10338 := by decide +kernel

theorem rowEval10338 (x : Key → ℝ) : Integer.Sparse.eval row10338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10338, Integer.Sparse.eval_collectBalanced, rawRowCheck10338]

theorem rawRowCheck10339 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form16 = rawRow10339 := by decide +kernel

theorem rowCheck10339 : row10339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10339 := by decide +kernel

theorem rowEval10339 (x : Key → ℝ) : Integer.Sparse.eval row10339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10339, Integer.Sparse.eval_collectBalanced, rawRowCheck10339]

theorem rawRowCheck10340 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form16 = rawRow10340 := by decide +kernel

theorem rowCheck10340 : row10340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10340 := by decide +kernel

theorem rowEval10340 (x : Key → ℝ) : Integer.Sparse.eval row10340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10340, Integer.Sparse.eval_collectBalanced, rawRowCheck10340]

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

theorem entryCheck18_1 : entry18_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_1 k)) := by decide +kernel

theorem rowsSound18_1 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval9957 x
  · exact rowEval9958 x
  · exact rowEval9959 x
  · exact rowEval9960 x
  · exact rowEval9961 x
  · exact rowEval9962 x
  · exact rowEval9963 x
  · exact rowEval9964 x
  · exact rowEval9965 x
  · exact rowEval9966 x
  · exact rowEval9967 x
  · exact rowEval9968 x
  · exact rowEval9969 x
  · exact rowEval9970 x
  · exact rowEval9971 x
  · exact rowEval9972 x
  · exact rowEval9973 x
  · exact rowEval9974 x
  · exact rowEval9975 x
  · exact rowEval9976 x
  · exact rowEval9977 x
  · exact rowEval9978 x
  · exact rowEval9979 x
  · exact rowEval9980 x

theorem entryEval18_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_1 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck18_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_1]

theorem entryCheck18_2 : entry18_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_2 k)) := by decide +kernel

theorem rowsSound18_2 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval9981 x
  · exact rowEval9982 x
  · exact rowEval9983 x
  · exact rowEval9984 x
  · exact rowEval9985 x
  · exact rowEval9986 x
  · exact rowEval9987 x
  · exact rowEval9988 x
  · exact rowEval9989 x
  · exact rowEval9990 x
  · exact rowEval9991 x
  · exact rowEval9992 x
  · exact rowEval9993 x
  · exact rowEval9994 x
  · exact rowEval9995 x
  · exact rowEval9996 x
  · exact rowEval9997 x
  · exact rowEval9998 x
  · exact rowEval9999 x
  · exact rowEval10000 x
  · exact rowEval10001 x
  · exact rowEval10002 x
  · exact rowEval10003 x
  · exact rowEval10004 x

theorem entryEval18_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_2 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck18_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_2]

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

theorem entryCheck18_6 : entry18_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_6 k)) := by decide +kernel

theorem rowsSound18_6 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval10077 x
  · exact rowEval10078 x
  · exact rowEval10079 x
  · exact rowEval10080 x
  · exact rowEval10081 x
  · exact rowEval10082 x
  · exact rowEval10083 x
  · exact rowEval10084 x
  · exact rowEval10085 x
  · exact rowEval10086 x
  · exact rowEval10087 x
  · exact rowEval10088 x
  · exact rowEval10089 x
  · exact rowEval10090 x
  · exact rowEval10091 x
  · exact rowEval10092 x
  · exact rowEval10093 x
  · exact rowEval10094 x
  · exact rowEval10095 x
  · exact rowEval10096 x
  · exact rowEval10097 x
  · exact rowEval10098 x
  · exact rowEval10099 x
  · exact rowEval10100 x

theorem entryEval18_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_6 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck18_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_6]

theorem entryCheck18_12 : entry18_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_12 k)) := by decide +kernel

theorem rowsSound18_12 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval10221 x
  · exact rowEval10222 x
  · exact rowEval10223 x
  · exact rowEval10224 x
  · exact rowEval10225 x
  · exact rowEval10226 x
  · exact rowEval10227 x
  · exact rowEval10228 x
  · exact rowEval10229 x
  · exact rowEval10230 x
  · exact rowEval10231 x
  · exact rowEval10232 x
  · exact rowEval10233 x
  · exact rowEval10234 x
  · exact rowEval10235 x
  · exact rowEval10236 x
  · exact rowEval10237 x
  · exact rowEval10238 x
  · exact rowEval10239 x
  · exact rowEval10240 x
  · exact rowEval10241 x
  · exact rowEval10242 x
  · exact rowEval10243 x
  · exact rowEval10244 x

theorem entryEval18_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_12 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck18_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_12]

theorem entryCheck18_14 : entry18_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_14 k)) := by decide +kernel

theorem rowsSound18_14 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval10269 x
  · exact rowEval10270 x
  · exact rowEval10271 x
  · exact rowEval10272 x
  · exact rowEval10273 x
  · exact rowEval10274 x
  · exact rowEval10275 x
  · exact rowEval10276 x
  · exact rowEval10277 x
  · exact rowEval10278 x
  · exact rowEval10279 x
  · exact rowEval10280 x
  · exact rowEval10281 x
  · exact rowEval10282 x
  · exact rowEval10283 x
  · exact rowEval10284 x
  · exact rowEval10285 x
  · exact rowEval10286 x
  · exact rowEval10287 x
  · exact rowEval10288 x
  · exact rowEval10289 x
  · exact rowEval10290 x
  · exact rowEval10291 x
  · exact rowEval10292 x

theorem entryEval18_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_14 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck18_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_14]

theorem entryCheck18_15 : entry18_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_15 k)) := by decide +kernel

theorem rowsSound18_15 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10293 x
  · exact rowEval10294 x
  · exact rowEval10295 x
  · exact rowEval10296 x
  · exact rowEval10297 x
  · exact rowEval10298 x
  · exact rowEval10299 x
  · exact rowEval10300 x
  · exact rowEval10301 x
  · exact rowEval10302 x
  · exact rowEval10303 x
  · exact rowEval10304 x
  · exact rowEval10305 x
  · exact rowEval10306 x
  · exact rowEval10307 x
  · exact rowEval10308 x
  · exact rowEval10309 x
  · exact rowEval10310 x
  · exact rowEval10311 x
  · exact rowEval10312 x
  · exact rowEval10313 x
  · exact rowEval10314 x
  · exact rowEval10315 x
  · exact rowEval10316 x

theorem entryEval18_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_15 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck18_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_15]

theorem entryCheck18_16 : entry18_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_16 k)) := by decide +kernel

theorem rowsSound18_16 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval10317 x
  · exact rowEval10318 x
  · exact rowEval10319 x
  · exact rowEval10320 x
  · exact rowEval10321 x
  · exact rowEval10322 x
  · exact rowEval10323 x
  · exact rowEval10324 x
  · exact rowEval10325 x
  · exact rowEval10326 x
  · exact rowEval10327 x
  · exact rowEval10328 x
  · exact rowEval10329 x
  · exact rowEval10330 x
  · exact rowEval10331 x
  · exact rowEval10332 x
  · exact rowEval10333 x
  · exact rowEval10334 x
  · exact rowEval10335 x
  · exact rowEval10336 x
  · exact rowEval10337 x
  · exact rowEval10338 x
  · exact rowEval10339 x
  · exact rowEval10340 x

theorem entryEval18_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_16 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck18_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_16]

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

theorem rawRowCheck10569 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form18 = rawRow10569 := by decide +kernel

theorem rowCheck10569 : row10569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10569 := by decide +kernel

theorem rowEval10569 (x : Key → ℝ) : Integer.Sparse.eval row10569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10569, Integer.Sparse.eval_collectBalanced, rawRowCheck10569]

theorem rawRowCheck10570 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form18 = rawRow10570 := by decide +kernel

theorem rowCheck10570 : row10570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10570 := by decide +kernel

theorem rowEval10570 (x : Key → ℝ) : Integer.Sparse.eval row10570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10570, Integer.Sparse.eval_collectBalanced, rawRowCheck10570]

theorem rawRowCheck10571 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form18 = rawRow10571 := by decide +kernel

theorem rowCheck10571 : row10571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10571 := by decide +kernel

theorem rowEval10571 (x : Key → ℝ) : Integer.Sparse.eval row10571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10571, Integer.Sparse.eval_collectBalanced, rawRowCheck10571]

theorem rawRowCheck10572 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form18 = rawRow10572 := by decide +kernel

theorem rowCheck10572 : row10572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10572 := by decide +kernel

theorem rowEval10572 (x : Key → ℝ) : Integer.Sparse.eval row10572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10572, Integer.Sparse.eval_collectBalanced, rawRowCheck10572]

theorem rawRowCheck10573 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form18 = rawRow10573 := by decide +kernel

theorem rowCheck10573 : row10573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10573 := by decide +kernel

theorem rowEval10573 (x : Key → ℝ) : Integer.Sparse.eval row10573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10573, Integer.Sparse.eval_collectBalanced, rawRowCheck10573]

theorem rawRowCheck10574 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form18 = rawRow10574 := by decide +kernel

theorem rowCheck10574 : row10574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10574 := by decide +kernel

theorem rowEval10574 (x : Key → ℝ) : Integer.Sparse.eval row10574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10574, Integer.Sparse.eval_collectBalanced, rawRowCheck10574]

theorem rawRowCheck10575 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form18 = rawRow10575 := by decide +kernel

theorem rowCheck10575 : row10575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10575 := by decide +kernel

theorem rowEval10575 (x : Key → ℝ) : Integer.Sparse.eval row10575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10575, Integer.Sparse.eval_collectBalanced, rawRowCheck10575]

theorem rawRowCheck10576 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form18 = rawRow10576 := by decide +kernel

theorem rowCheck10576 : row10576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10576 := by decide +kernel

theorem rowEval10576 (x : Key → ℝ) : Integer.Sparse.eval row10576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10576, Integer.Sparse.eval_collectBalanced, rawRowCheck10576]

theorem rawRowCheck10577 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form18 = rawRow10577 := by decide +kernel

theorem rowCheck10577 : row10577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10577 := by decide +kernel

theorem rowEval10577 (x : Key → ℝ) : Integer.Sparse.eval row10577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10577, Integer.Sparse.eval_collectBalanced, rawRowCheck10577]

theorem rawRowCheck10578 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form18 = rawRow10578 := by decide +kernel

theorem rowCheck10578 : row10578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10578 := by decide +kernel

theorem rowEval10578 (x : Key → ℝ) : Integer.Sparse.eval row10578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10578, Integer.Sparse.eval_collectBalanced, rawRowCheck10578]

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

theorem entryCheck19_18 : entry19_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_18 k)) := by decide +kernel

theorem rowsSound19_18 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval10569 x
  · exact rowEval10570 x
  · exact rowEval10571 x
  · exact rowEval10572 x
  · exact rowEval10573 x
  · exact rowEval10574 x
  · exact rowEval10575 x
  · exact rowEval10576 x
  · exact rowEval10577 x
  · exact rowEval10578 x

theorem entryEval19_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_18 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck19_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_18]

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

theorem rawRowCheck10679 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form18 = rawRow10679 := by decide +kernel

theorem rowCheck10679 : row10679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10679 := by decide +kernel

theorem rowEval10679 (x : Key → ℝ) : Integer.Sparse.eval row10679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form18) x := by
  rw [rowCheck10679, Integer.Sparse.eval_collectBalanced, rawRowCheck10679]

theorem rawRowCheck10680 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form18 = rawRow10680 := by decide +kernel

theorem rowCheck10680 : row10680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10680 := by decide +kernel

theorem rowEval10680 (x : Key → ℝ) : Integer.Sparse.eval row10680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10680, Integer.Sparse.eval_collectBalanced, rawRowCheck10680]

theorem rawRowCheck10681 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form18 = rawRow10681 := by decide +kernel

theorem rowCheck10681 : row10681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10681 := by decide +kernel

theorem rowEval10681 (x : Key → ℝ) : Integer.Sparse.eval row10681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10681, Integer.Sparse.eval_collectBalanced, rawRowCheck10681]

theorem rawRowCheck10682 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form18 = rawRow10682 := by decide +kernel

theorem rowCheck10682 : row10682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10682 := by decide +kernel

theorem rowEval10682 (x : Key → ℝ) : Integer.Sparse.eval row10682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10682, Integer.Sparse.eval_collectBalanced, rawRowCheck10682]

theorem rawRowCheck10683 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form18 = rawRow10683 := by decide +kernel

theorem rowCheck10683 : row10683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10683 := by decide +kernel

theorem rowEval10683 (x : Key → ℝ) : Integer.Sparse.eval row10683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10683, Integer.Sparse.eval_collectBalanced, rawRowCheck10683]

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

theorem entryCheck20_18 : entry20_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_18 k)) := by decide +kernel

theorem rowsSound20_18 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval10679 x
  · exact rowEval10680 x
  · exact rowEval10681 x
  · exact rowEval10682 x
  · exact rowEval10683 x

theorem entryEval20_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_18 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck20_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_18]

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

theorem rawRowCheck12098 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form18 = rawRow12098 := by decide +kernel

theorem rowCheck12098 : row12098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12098 := by decide +kernel

theorem rowEval12098 (x : Key → ℝ) : Integer.Sparse.eval row12098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12098, Integer.Sparse.eval_collectBalanced, rawRowCheck12098]

theorem rawRowCheck12099 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form18 = rawRow12099 := by decide +kernel

theorem rowCheck12099 : row12099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12099 := by decide +kernel

theorem rowEval12099 (x : Key → ℝ) : Integer.Sparse.eval row12099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12099, Integer.Sparse.eval_collectBalanced, rawRowCheck12099]

theorem rawRowCheck12100 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form18 = rawRow12100 := by decide +kernel

theorem rowCheck12100 : row12100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12100 := by decide +kernel

theorem rowEval12100 (x : Key → ℝ) : Integer.Sparse.eval row12100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12100, Integer.Sparse.eval_collectBalanced, rawRowCheck12100]

theorem rawRowCheck12101 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form18 = rawRow12101 := by decide +kernel

theorem rowCheck12101 : row12101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12101 := by decide +kernel

theorem rowEval12101 (x : Key → ℝ) : Integer.Sparse.eval row12101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12101, Integer.Sparse.eval_collectBalanced, rawRowCheck12101]

theorem rawRowCheck12102 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form18 = rawRow12102 := by decide +kernel

theorem rowCheck12102 : row12102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12102 := by decide +kernel

theorem rowEval12102 (x : Key → ℝ) : Integer.Sparse.eval row12102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12102, Integer.Sparse.eval_collectBalanced, rawRowCheck12102]

theorem rawRowCheck12103 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form18 = rawRow12103 := by decide +kernel

theorem rowCheck12103 : row12103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12103 := by decide +kernel

theorem rowEval12103 (x : Key → ℝ) : Integer.Sparse.eval row12103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12103, Integer.Sparse.eval_collectBalanced, rawRowCheck12103]

theorem rawRowCheck12104 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form18 = rawRow12104 := by decide +kernel

theorem rowCheck12104 : row12104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12104 := by decide +kernel

theorem rowEval12104 (x : Key → ℝ) : Integer.Sparse.eval row12104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12104, Integer.Sparse.eval_collectBalanced, rawRowCheck12104]

theorem rawRowCheck12105 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form18 = rawRow12105 := by decide +kernel

theorem rowCheck12105 : row12105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12105 := by decide +kernel

theorem rowEval12105 (x : Key → ℝ) : Integer.Sparse.eval row12105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12105, Integer.Sparse.eval_collectBalanced, rawRowCheck12105]

theorem rawRowCheck12106 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form18 = rawRow12106 := by decide +kernel

theorem rowCheck12106 : row12106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12106 := by decide +kernel

theorem rowEval12106 (x : Key → ℝ) : Integer.Sparse.eval row12106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12106, Integer.Sparse.eval_collectBalanced, rawRowCheck12106]

theorem rawRowCheck12107 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form18 = rawRow12107 := by decide +kernel

theorem rowCheck12107 : row12107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12107 := by decide +kernel

theorem rowEval12107 (x : Key → ℝ) : Integer.Sparse.eval row12107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12107, Integer.Sparse.eval_collectBalanced, rawRowCheck12107]

theorem rawRowCheck12108 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form18 = rawRow12108 := by decide +kernel

theorem rowCheck12108 : row12108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12108 := by decide +kernel

theorem rowEval12108 (x : Key → ℝ) : Integer.Sparse.eval row12108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12108, Integer.Sparse.eval_collectBalanced, rawRowCheck12108]

theorem rawRowCheck12109 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form18 = rawRow12109 := by decide +kernel

theorem rowCheck12109 : row12109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12109 := by decide +kernel

theorem rowEval12109 (x : Key → ℝ) : Integer.Sparse.eval row12109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12109, Integer.Sparse.eval_collectBalanced, rawRowCheck12109]

theorem rawRowCheck12110 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form18 = rawRow12110 := by decide +kernel

theorem rowCheck12110 : row12110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12110 := by decide +kernel

theorem rowEval12110 (x : Key → ℝ) : Integer.Sparse.eval row12110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12110, Integer.Sparse.eval_collectBalanced, rawRowCheck12110]

theorem rawRowCheck12111 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form18 = rawRow12111 := by decide +kernel

theorem rowCheck12111 : row12111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12111 := by decide +kernel

theorem rowEval12111 (x : Key → ℝ) : Integer.Sparse.eval row12111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12111, Integer.Sparse.eval_collectBalanced, rawRowCheck12111]

theorem rawRowCheck12112 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form18 = rawRow12112 := by decide +kernel

theorem rowCheck12112 : row12112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12112 := by decide +kernel

theorem rowEval12112 (x : Key → ℝ) : Integer.Sparse.eval row12112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12112, Integer.Sparse.eval_collectBalanced, rawRowCheck12112]

theorem rawRowCheck12113 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form18 = rawRow12113 := by decide +kernel

theorem rowCheck12113 : row12113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12113 := by decide +kernel

theorem rowEval12113 (x : Key → ℝ) : Integer.Sparse.eval row12113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12113, Integer.Sparse.eval_collectBalanced, rawRowCheck12113]

theorem rawRowCheck12114 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form18 = rawRow12114 := by decide +kernel

theorem rowCheck12114 : row12114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12114 := by decide +kernel

theorem rowEval12114 (x : Key → ℝ) : Integer.Sparse.eval row12114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12114, Integer.Sparse.eval_collectBalanced, rawRowCheck12114]

theorem rawRowCheck12115 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form18 = rawRow12115 := by decide +kernel

theorem rowCheck12115 : row12115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12115 := by decide +kernel

theorem rowEval12115 (x : Key → ℝ) : Integer.Sparse.eval row12115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12115, Integer.Sparse.eval_collectBalanced, rawRowCheck12115]

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

theorem entryCheck23_18 : entry23_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_18 k)) := by decide +kernel

theorem rowsSound23_18 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12098 x
  · exact rowEval12099 x
  · exact rowEval12100 x
  · exact rowEval12101 x
  · exact rowEval12102 x
  · exact rowEval12103 x
  · exact rowEval12104 x
  · exact rowEval12105 x
  · exact rowEval12106 x
  · exact rowEval12107 x
  · exact rowEval12108 x
  · exact rowEval12109 x
  · exact rowEval12110 x
  · exact rowEval12111 x
  · exact rowEval12112 x
  · exact rowEval12113 x
  · exact rowEval12114 x
  · exact rowEval12115 x

theorem entryEval23_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_18 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck23_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_18]

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

theorem rawRowCheck12296 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form18 = rawRow12296 := by decide +kernel

theorem rowCheck12296 : row12296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12296 := by decide +kernel

theorem rowEval12296 (x : Key → ℝ) : Integer.Sparse.eval row12296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12296, Integer.Sparse.eval_collectBalanced, rawRowCheck12296]

theorem rawRowCheck12297 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form18 = rawRow12297 := by decide +kernel

theorem rowCheck12297 : row12297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12297 := by decide +kernel

theorem rowEval12297 (x : Key → ℝ) : Integer.Sparse.eval row12297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12297, Integer.Sparse.eval_collectBalanced, rawRowCheck12297]

theorem rawRowCheck12298 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form18 = rawRow12298 := by decide +kernel

theorem rowCheck12298 : row12298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12298 := by decide +kernel

theorem rowEval12298 (x : Key → ℝ) : Integer.Sparse.eval row12298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12298, Integer.Sparse.eval_collectBalanced, rawRowCheck12298]

theorem rawRowCheck12299 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form18 = rawRow12299 := by decide +kernel

theorem rowCheck12299 : row12299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12299 := by decide +kernel

theorem rowEval12299 (x : Key → ℝ) : Integer.Sparse.eval row12299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12299, Integer.Sparse.eval_collectBalanced, rawRowCheck12299]

theorem rawRowCheck12300 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form18 = rawRow12300 := by decide +kernel

theorem rowCheck12300 : row12300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12300 := by decide +kernel

theorem rowEval12300 (x : Key → ℝ) : Integer.Sparse.eval row12300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12300, Integer.Sparse.eval_collectBalanced, rawRowCheck12300]

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

theorem entryCheck24_18 : entry24_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_18 k)) := by decide +kernel

theorem rowsSound24_18 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12296 x
  · exact rowEval12297 x
  · exact rowEval12298 x
  · exact rowEval12299 x
  · exact rowEval12300 x

theorem entryEval24_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_18 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck24_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_18]

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

theorem rawRowCheck12475 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form18 = rawRow12475 := by decide +kernel

theorem rowCheck12475 : row12475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12475 := by decide +kernel

theorem rowEval12475 (x : Key → ℝ) : Integer.Sparse.eval row12475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12475, Integer.Sparse.eval_collectBalanced, rawRowCheck12475]

theorem rawRowCheck12476 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form18 = rawRow12476 := by decide +kernel

theorem rowCheck12476 : row12476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12476 := by decide +kernel

theorem rowEval12476 (x : Key → ℝ) : Integer.Sparse.eval row12476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12476, Integer.Sparse.eval_collectBalanced, rawRowCheck12476]

theorem rawRowCheck12477 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form18 = rawRow12477 := by decide +kernel

theorem rowCheck12477 : row12477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12477 := by decide +kernel

theorem rowEval12477 (x : Key → ℝ) : Integer.Sparse.eval row12477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12477, Integer.Sparse.eval_collectBalanced, rawRowCheck12477]

theorem rawRowCheck12478 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form18 = rawRow12478 := by decide +kernel

theorem rowCheck12478 : row12478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12478 := by decide +kernel

theorem rowEval12478 (x : Key → ℝ) : Integer.Sparse.eval row12478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12478, Integer.Sparse.eval_collectBalanced, rawRowCheck12478]

theorem rawRowCheck12479 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form18 = rawRow12479 := by decide +kernel

theorem rowCheck12479 : row12479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12479 := by decide +kernel

theorem rowEval12479 (x : Key → ℝ) : Integer.Sparse.eval row12479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12479, Integer.Sparse.eval_collectBalanced, rawRowCheck12479]

theorem rawRowCheck12480 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form18 = rawRow12480 := by decide +kernel

theorem rowCheck12480 : row12480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12480 := by decide +kernel

theorem rowEval12480 (x : Key → ℝ) : Integer.Sparse.eval row12480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12480, Integer.Sparse.eval_collectBalanced, rawRowCheck12480]

theorem rawRowCheck12481 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form18 = rawRow12481 := by decide +kernel

theorem rowCheck12481 : row12481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12481 := by decide +kernel

theorem rowEval12481 (x : Key → ℝ) : Integer.Sparse.eval row12481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12481, Integer.Sparse.eval_collectBalanced, rawRowCheck12481]

theorem rawRowCheck12482 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form18 = rawRow12482 := by decide +kernel

theorem rowCheck12482 : row12482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12482 := by decide +kernel

theorem rowEval12482 (x : Key → ℝ) : Integer.Sparse.eval row12482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12482, Integer.Sparse.eval_collectBalanced, rawRowCheck12482]

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

theorem entryCheck25_18 : entry25_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_18 k)) := by decide +kernel

theorem rowsSound25_18 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12475 x
  · exact rowEval12476 x
  · exact rowEval12477 x
  · exact rowEval12478 x
  · exact rowEval12479 x
  · exact rowEval12480 x
  · exact rowEval12481 x
  · exact rowEval12482 x

theorem entryEval25_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_18 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck25_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_18]

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

theorem entryEvalRow18_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 18 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 18).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval18_0 B hB
  · exact entryEval18_1 B hB
  · exact entryEval18_2 B hB
  · exact entryEval18_3_e B hB
  · exact entryEval18_4 B hB
  · exact entryEval18_5_e B hB
  · exact entryEval18_6 B hB
  · exact entryEval18_7_e B hB
  · exact entryEval18_8_e B hB
  · exact entryEval18_9_e B hB
  · exact entryEval18_10_e B hB
  · exact entryEval18_11_e B hB
  · exact entryEval18_12 B hB
  · exact entryEval18_13_e B hB
  · exact entryEval18_14 B hB
  · exact entryEval18_15 B hB
  · exact entryEval18_16 B hB
  · exact entryEval18_17 B hB
  · exact entryEval18_18_e B hB
  · exact (entryEval19_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_18_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_18_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_18 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_18_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e_oai
