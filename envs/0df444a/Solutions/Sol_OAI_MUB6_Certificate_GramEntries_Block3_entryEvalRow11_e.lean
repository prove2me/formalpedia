-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:12:18.823058+00:00
-- url     : https://prove2.me/submissions/7ce062be-30c3-4c20-b8a3-319d78ed93f2

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval18_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval22_11_e

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

theorem rawRowCheck8669 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form1 = rawRow8669 := by decide +kernel

theorem rowCheck8669 : row8669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8669 := by decide +kernel

theorem rowEval8669 (x : Key → ℝ) : Integer.Sparse.eval row8669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8669, Integer.Sparse.eval_collectBalanced, rawRowCheck8669]

theorem rawRowCheck8670 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form1 = rawRow8670 := by decide +kernel

theorem rowCheck8670 : row8670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8670 := by decide +kernel

theorem rowEval8670 (x : Key → ℝ) : Integer.Sparse.eval row8670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8670, Integer.Sparse.eval_collectBalanced, rawRowCheck8670]

theorem rawRowCheck8671 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form1 = rawRow8671 := by decide +kernel

theorem rowCheck8671 : row8671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8671 := by decide +kernel

theorem rowEval8671 (x : Key → ℝ) : Integer.Sparse.eval row8671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8671, Integer.Sparse.eval_collectBalanced, rawRowCheck8671]

theorem rawRowCheck8672 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8672 := by decide +kernel

theorem rowCheck8672 : row8672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8672 := by decide +kernel

theorem rowEval8672 (x : Key → ℝ) : Integer.Sparse.eval row8672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8672, Integer.Sparse.eval_collectBalanced, rawRowCheck8672]

theorem rawRowCheck8673 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8673 := by decide +kernel

theorem rowCheck8673 : row8673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8673 := by decide +kernel

theorem rowEval8673 (x : Key → ℝ) : Integer.Sparse.eval row8673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8673, Integer.Sparse.eval_collectBalanced, rawRowCheck8673]

theorem rawRowCheck8674 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow8674 := by decide +kernel

theorem rowCheck8674 : row8674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8674 := by decide +kernel

theorem rowEval8674 (x : Key → ℝ) : Integer.Sparse.eval row8674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8674, Integer.Sparse.eval_collectBalanced, rawRowCheck8674]

theorem rawRowCheck8675 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow8675 := by decide +kernel

theorem rowCheck8675 : row8675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8675 := by decide +kernel

theorem rowEval8675 (x : Key → ℝ) : Integer.Sparse.eval row8675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8675, Integer.Sparse.eval_collectBalanced, rawRowCheck8675]

theorem rawRowCheck8676 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow8676 := by decide +kernel

theorem rowCheck8676 : row8676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8676 := by decide +kernel

theorem rowEval8676 (x : Key → ℝ) : Integer.Sparse.eval row8676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck8676, Integer.Sparse.eval_collectBalanced, rawRowCheck8676]

theorem rawRowCheck8677 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form2 = rawRow8677 := by decide +kernel

theorem rowCheck8677 : row8677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8677 := by decide +kernel

theorem rowEval8677 (x : Key → ℝ) : Integer.Sparse.eval row8677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8677, Integer.Sparse.eval_collectBalanced, rawRowCheck8677]

theorem rawRowCheck8678 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form2 = rawRow8678 := by decide +kernel

theorem rowCheck8678 : row8678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8678 := by decide +kernel

theorem rowEval8678 (x : Key → ℝ) : Integer.Sparse.eval row8678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8678, Integer.Sparse.eval_collectBalanced, rawRowCheck8678]

theorem rawRowCheck8679 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form2 = rawRow8679 := by decide +kernel

theorem rowCheck8679 : row8679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8679 := by decide +kernel

theorem rowEval8679 (x : Key → ℝ) : Integer.Sparse.eval row8679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8679, Integer.Sparse.eval_collectBalanced, rawRowCheck8679]

theorem rawRowCheck8680 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8680 := by decide +kernel

theorem rowCheck8680 : row8680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8680 := by decide +kernel

theorem rowEval8680 (x : Key → ℝ) : Integer.Sparse.eval row8680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8680, Integer.Sparse.eval_collectBalanced, rawRowCheck8680]

theorem rawRowCheck8681 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8681 := by decide +kernel

theorem rowCheck8681 : row8681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8681 := by decide +kernel

theorem rowEval8681 (x : Key → ℝ) : Integer.Sparse.eval row8681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8681, Integer.Sparse.eval_collectBalanced, rawRowCheck8681]

theorem rawRowCheck8682 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow8682 := by decide +kernel

theorem rowCheck8682 : row8682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8682 := by decide +kernel

theorem rowEval8682 (x : Key → ℝ) : Integer.Sparse.eval row8682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8682, Integer.Sparse.eval_collectBalanced, rawRowCheck8682]

theorem rawRowCheck8683 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow8683 := by decide +kernel

theorem rowCheck8683 : row8683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8683 := by decide +kernel

theorem rowEval8683 (x : Key → ℝ) : Integer.Sparse.eval row8683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8683, Integer.Sparse.eval_collectBalanced, rawRowCheck8683]

theorem rawRowCheck8684 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow8684 := by decide +kernel

theorem rowCheck8684 : row8684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8684 := by decide +kernel

theorem rowEval8684 (x : Key → ℝ) : Integer.Sparse.eval row8684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck8684, Integer.Sparse.eval_collectBalanced, rawRowCheck8684]

theorem rawRowCheck8685 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form3 = rawRow8685 := by decide +kernel

theorem rowCheck8685 : row8685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8685 := by decide +kernel

theorem rowEval8685 (x : Key → ℝ) : Integer.Sparse.eval row8685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8685, Integer.Sparse.eval_collectBalanced, rawRowCheck8685]

theorem rawRowCheck8686 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form3 = rawRow8686 := by decide +kernel

theorem rowCheck8686 : row8686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8686 := by decide +kernel

theorem rowEval8686 (x : Key → ℝ) : Integer.Sparse.eval row8686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8686, Integer.Sparse.eval_collectBalanced, rawRowCheck8686]

theorem rawRowCheck8687 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form3 = rawRow8687 := by decide +kernel

theorem rowCheck8687 : row8687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8687 := by decide +kernel

theorem rowEval8687 (x : Key → ℝ) : Integer.Sparse.eval row8687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8687, Integer.Sparse.eval_collectBalanced, rawRowCheck8687]

theorem rawRowCheck8688 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8688 := by decide +kernel

theorem rowCheck8688 : row8688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8688 := by decide +kernel

theorem rowEval8688 (x : Key → ℝ) : Integer.Sparse.eval row8688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8688, Integer.Sparse.eval_collectBalanced, rawRowCheck8688]

theorem rawRowCheck8689 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8689 := by decide +kernel

theorem rowCheck8689 : row8689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8689 := by decide +kernel

theorem rowEval8689 (x : Key → ℝ) : Integer.Sparse.eval row8689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8689, Integer.Sparse.eval_collectBalanced, rawRowCheck8689]

theorem rawRowCheck8690 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow8690 := by decide +kernel

theorem rowCheck8690 : row8690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8690 := by decide +kernel

theorem rowEval8690 (x : Key → ℝ) : Integer.Sparse.eval row8690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8690, Integer.Sparse.eval_collectBalanced, rawRowCheck8690]

theorem rawRowCheck8691 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow8691 := by decide +kernel

theorem rowCheck8691 : row8691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8691 := by decide +kernel

theorem rowEval8691 (x : Key → ℝ) : Integer.Sparse.eval row8691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8691, Integer.Sparse.eval_collectBalanced, rawRowCheck8691]

theorem rawRowCheck8692 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow8692 := by decide +kernel

theorem rowCheck8692 : row8692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8692 := by decide +kernel

theorem rowEval8692 (x : Key → ℝ) : Integer.Sparse.eval row8692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck8692, Integer.Sparse.eval_collectBalanced, rawRowCheck8692]

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

theorem rawRowCheck8701 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form5 = rawRow8701 := by decide +kernel

theorem rowCheck8701 : row8701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8701 := by decide +kernel

theorem rowEval8701 (x : Key → ℝ) : Integer.Sparse.eval row8701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8701, Integer.Sparse.eval_collectBalanced, rawRowCheck8701]

theorem rawRowCheck8702 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form5 = rawRow8702 := by decide +kernel

theorem rowCheck8702 : row8702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8702 := by decide +kernel

theorem rowEval8702 (x : Key → ℝ) : Integer.Sparse.eval row8702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8702, Integer.Sparse.eval_collectBalanced, rawRowCheck8702]

theorem rawRowCheck8703 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form5 = rawRow8703 := by decide +kernel

theorem rowCheck8703 : row8703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8703 := by decide +kernel

theorem rowEval8703 (x : Key → ℝ) : Integer.Sparse.eval row8703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8703, Integer.Sparse.eval_collectBalanced, rawRowCheck8703]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck8704 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8704 := by decide +kernel

theorem rowCheck8704 : row8704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8704 := by decide +kernel

theorem rowEval8704 (x : Key → ℝ) : Integer.Sparse.eval row8704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8704, Integer.Sparse.eval_collectBalanced, rawRowCheck8704]

theorem rawRowCheck8705 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8705 := by decide +kernel

theorem rowCheck8705 : row8705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8705 := by decide +kernel

theorem rowEval8705 (x : Key → ℝ) : Integer.Sparse.eval row8705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8705, Integer.Sparse.eval_collectBalanced, rawRowCheck8705]

theorem rawRowCheck8706 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form5 = rawRow8706 := by decide +kernel

theorem rowCheck8706 : row8706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8706 := by decide +kernel

theorem rowEval8706 (x : Key → ℝ) : Integer.Sparse.eval row8706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8706, Integer.Sparse.eval_collectBalanced, rawRowCheck8706]

theorem rawRowCheck8707 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form5 = rawRow8707 := by decide +kernel

theorem rowCheck8707 : row8707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8707 := by decide +kernel

theorem rowEval8707 (x : Key → ℝ) : Integer.Sparse.eval row8707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8707, Integer.Sparse.eval_collectBalanced, rawRowCheck8707]

theorem rawRowCheck8708 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form5 = rawRow8708 := by decide +kernel

theorem rowCheck8708 : row8708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8708 := by decide +kernel

theorem rowEval8708 (x : Key → ℝ) : Integer.Sparse.eval row8708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck8708, Integer.Sparse.eval_collectBalanced, rawRowCheck8708]

theorem rawRowCheck8709 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form6 = rawRow8709 := by decide +kernel

theorem rowCheck8709 : row8709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8709 := by decide +kernel

theorem rowEval8709 (x : Key → ℝ) : Integer.Sparse.eval row8709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8709, Integer.Sparse.eval_collectBalanced, rawRowCheck8709]

theorem rawRowCheck8710 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form6 = rawRow8710 := by decide +kernel

theorem rowCheck8710 : row8710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8710 := by decide +kernel

theorem rowEval8710 (x : Key → ℝ) : Integer.Sparse.eval row8710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8710, Integer.Sparse.eval_collectBalanced, rawRowCheck8710]

theorem rawRowCheck8711 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form6 = rawRow8711 := by decide +kernel

theorem rowCheck8711 : row8711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8711 := by decide +kernel

theorem rowEval8711 (x : Key → ℝ) : Integer.Sparse.eval row8711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8711, Integer.Sparse.eval_collectBalanced, rawRowCheck8711]

theorem rawRowCheck8712 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8712 := by decide +kernel

theorem rowCheck8712 : row8712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8712 := by decide +kernel

theorem rowEval8712 (x : Key → ℝ) : Integer.Sparse.eval row8712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8712, Integer.Sparse.eval_collectBalanced, rawRowCheck8712]

theorem rawRowCheck8713 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8713 := by decide +kernel

theorem rowCheck8713 : row8713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8713 := by decide +kernel

theorem rowEval8713 (x : Key → ℝ) : Integer.Sparse.eval row8713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8713, Integer.Sparse.eval_collectBalanced, rawRowCheck8713]

theorem rawRowCheck8714 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form6 = rawRow8714 := by decide +kernel

theorem rowCheck8714 : row8714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8714 := by decide +kernel

theorem rowEval8714 (x : Key → ℝ) : Integer.Sparse.eval row8714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8714, Integer.Sparse.eval_collectBalanced, rawRowCheck8714]

theorem rawRowCheck8715 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form6 = rawRow8715 := by decide +kernel

theorem rowCheck8715 : row8715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8715 := by decide +kernel

theorem rowEval8715 (x : Key → ℝ) : Integer.Sparse.eval row8715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8715, Integer.Sparse.eval_collectBalanced, rawRowCheck8715]

theorem rawRowCheck8716 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form6 = rawRow8716 := by decide +kernel

theorem rowCheck8716 : row8716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8716 := by decide +kernel

theorem rowEval8716 (x : Key → ℝ) : Integer.Sparse.eval row8716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck8716, Integer.Sparse.eval_collectBalanced, rawRowCheck8716]

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

theorem rawRowCheck8725 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form8 = rawRow8725 := by decide +kernel

theorem rowCheck8725 : row8725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8725 := by decide +kernel

theorem rowEval8725 (x : Key → ℝ) : Integer.Sparse.eval row8725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8725, Integer.Sparse.eval_collectBalanced, rawRowCheck8725]

theorem rawRowCheck8726 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form8 = rawRow8726 := by decide +kernel

theorem rowCheck8726 : row8726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8726 := by decide +kernel

theorem rowEval8726 (x : Key → ℝ) : Integer.Sparse.eval row8726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8726, Integer.Sparse.eval_collectBalanced, rawRowCheck8726]

theorem rawRowCheck8727 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form8 = rawRow8727 := by decide +kernel

theorem rowCheck8727 : row8727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8727 := by decide +kernel

theorem rowEval8727 (x : Key → ℝ) : Integer.Sparse.eval row8727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8727, Integer.Sparse.eval_collectBalanced, rawRowCheck8727]

theorem rawRowCheck8728 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8728 := by decide +kernel

theorem rowCheck8728 : row8728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8728 := by decide +kernel

theorem rowEval8728 (x : Key → ℝ) : Integer.Sparse.eval row8728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8728, Integer.Sparse.eval_collectBalanced, rawRowCheck8728]

theorem rawRowCheck8729 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8729 := by decide +kernel

theorem rowCheck8729 : row8729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8729 := by decide +kernel

theorem rowEval8729 (x : Key → ℝ) : Integer.Sparse.eval row8729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8729, Integer.Sparse.eval_collectBalanced, rawRowCheck8729]

theorem rawRowCheck8730 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form8 = rawRow8730 := by decide +kernel

theorem rowCheck8730 : row8730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8730 := by decide +kernel

theorem rowEval8730 (x : Key → ℝ) : Integer.Sparse.eval row8730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8730, Integer.Sparse.eval_collectBalanced, rawRowCheck8730]

theorem rawRowCheck8731 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form8 = rawRow8731 := by decide +kernel

theorem rowCheck8731 : row8731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8731 := by decide +kernel

theorem rowEval8731 (x : Key → ℝ) : Integer.Sparse.eval row8731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8731, Integer.Sparse.eval_collectBalanced, rawRowCheck8731]

theorem rawRowCheck8732 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form8 = rawRow8732 := by decide +kernel

theorem rowCheck8732 : row8732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8732 := by decide +kernel

theorem rowEval8732 (x : Key → ℝ) : Integer.Sparse.eval row8732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck8732, Integer.Sparse.eval_collectBalanced, rawRowCheck8732]

theorem rawRowCheck8733 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form9 = rawRow8733 := by decide +kernel

theorem rowCheck8733 : row8733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8733 := by decide +kernel

theorem rowEval8733 (x : Key → ℝ) : Integer.Sparse.eval row8733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8733, Integer.Sparse.eval_collectBalanced, rawRowCheck8733]

theorem rawRowCheck8734 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form9 = rawRow8734 := by decide +kernel

theorem rowCheck8734 : row8734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8734 := by decide +kernel

theorem rowEval8734 (x : Key → ℝ) : Integer.Sparse.eval row8734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8734, Integer.Sparse.eval_collectBalanced, rawRowCheck8734]

theorem rawRowCheck8735 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form9 = rawRow8735 := by decide +kernel

theorem rowCheck8735 : row8735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8735 := by decide +kernel

theorem rowEval8735 (x : Key → ℝ) : Integer.Sparse.eval row8735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8735, Integer.Sparse.eval_collectBalanced, rawRowCheck8735]

theorem rawRowCheck8736 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8736 := by decide +kernel

theorem rowCheck8736 : row8736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8736 := by decide +kernel

theorem rowEval8736 (x : Key → ℝ) : Integer.Sparse.eval row8736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8736, Integer.Sparse.eval_collectBalanced, rawRowCheck8736]

theorem rawRowCheck8737 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8737 := by decide +kernel

theorem rowCheck8737 : row8737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8737 := by decide +kernel

theorem rowEval8737 (x : Key → ℝ) : Integer.Sparse.eval row8737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8737, Integer.Sparse.eval_collectBalanced, rawRowCheck8737]

theorem rawRowCheck8738 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form9 = rawRow8738 := by decide +kernel

theorem rowCheck8738 : row8738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8738 := by decide +kernel

theorem rowEval8738 (x : Key → ℝ) : Integer.Sparse.eval row8738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8738, Integer.Sparse.eval_collectBalanced, rawRowCheck8738]

theorem rawRowCheck8739 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form9 = rawRow8739 := by decide +kernel

theorem rowCheck8739 : row8739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8739 := by decide +kernel

theorem rowEval8739 (x : Key → ℝ) : Integer.Sparse.eval row8739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8739, Integer.Sparse.eval_collectBalanced, rawRowCheck8739]

theorem rawRowCheck8740 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form9 = rawRow8740 := by decide +kernel

theorem rowCheck8740 : row8740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8740 := by decide +kernel

theorem rowEval8740 (x : Key → ℝ) : Integer.Sparse.eval row8740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck8740, Integer.Sparse.eval_collectBalanced, rawRowCheck8740]

theorem rawRowCheck8741 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form10 = rawRow8741 := by decide +kernel

theorem rowCheck8741 : row8741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8741 := by decide +kernel

theorem rowEval8741 (x : Key → ℝ) : Integer.Sparse.eval row8741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck8741, Integer.Sparse.eval_collectBalanced, rawRowCheck8741]

theorem rawRowCheck8742 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form10 = rawRow8742 := by decide +kernel

theorem rowCheck8742 : row8742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8742 := by decide +kernel

theorem rowEval8742 (x : Key → ℝ) : Integer.Sparse.eval row8742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8742, Integer.Sparse.eval_collectBalanced, rawRowCheck8742]

theorem rawRowCheck8743 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form10 = rawRow8743 := by decide +kernel

theorem rowCheck8743 : row8743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8743 := by decide +kernel

theorem rowEval8743 (x : Key → ℝ) : Integer.Sparse.eval row8743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8743, Integer.Sparse.eval_collectBalanced, rawRowCheck8743]

theorem rawRowCheck8744 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8744 := by decide +kernel

theorem rowCheck8744 : row8744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8744 := by decide +kernel

theorem rowEval8744 (x : Key → ℝ) : Integer.Sparse.eval row8744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8744, Integer.Sparse.eval_collectBalanced, rawRowCheck8744]

theorem rawRowCheck8745 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8745 := by decide +kernel

theorem rowCheck8745 : row8745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8745 := by decide +kernel

theorem rowEval8745 (x : Key → ℝ) : Integer.Sparse.eval row8745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8745, Integer.Sparse.eval_collectBalanced, rawRowCheck8745]

theorem rawRowCheck8746 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow8746 := by decide +kernel

theorem rowCheck8746 : row8746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8746 := by decide +kernel

theorem rowEval8746 (x : Key → ℝ) : Integer.Sparse.eval row8746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8746, Integer.Sparse.eval_collectBalanced, rawRowCheck8746]

theorem rawRowCheck8747 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow8747 := by decide +kernel

theorem rowCheck8747 : row8747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8747 := by decide +kernel

theorem rowEval8747 (x : Key → ℝ) : Integer.Sparse.eval row8747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8747, Integer.Sparse.eval_collectBalanced, rawRowCheck8747]

theorem rawRowCheck8748 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow8748 := by decide +kernel

theorem rowCheck8748 : row8748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8748 := by decide +kernel

theorem rowEval8748 (x : Key → ℝ) : Integer.Sparse.eval row8748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck8748, Integer.Sparse.eval_collectBalanced, rawRowCheck8748]

theorem rawRowCheck8749 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form11 = rawRow8749 := by decide +kernel

theorem rowCheck8749 : row8749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8749 := by decide +kernel

theorem rowEval8749 (x : Key → ℝ) : Integer.Sparse.eval row8749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck8749, Integer.Sparse.eval_collectBalanced, rawRowCheck8749]

theorem rawRowCheck8750 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form11 = rawRow8750 := by decide +kernel

theorem rowCheck8750 : row8750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8750 := by decide +kernel

theorem rowEval8750 (x : Key → ℝ) : Integer.Sparse.eval row8750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8750, Integer.Sparse.eval_collectBalanced, rawRowCheck8750]

theorem rawRowCheck8751 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form11 = rawRow8751 := by decide +kernel

theorem rowCheck8751 : row8751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8751 := by decide +kernel

theorem rowEval8751 (x : Key → ℝ) : Integer.Sparse.eval row8751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8751, Integer.Sparse.eval_collectBalanced, rawRowCheck8751]

theorem rawRowCheck8752 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8752 := by decide +kernel

theorem rowCheck8752 : row8752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8752 := by decide +kernel

theorem rowEval8752 (x : Key → ℝ) : Integer.Sparse.eval row8752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8752, Integer.Sparse.eval_collectBalanced, rawRowCheck8752]

theorem rawRowCheck8753 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8753 := by decide +kernel

theorem rowCheck8753 : row8753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8753 := by decide +kernel

theorem rowEval8753 (x : Key → ℝ) : Integer.Sparse.eval row8753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8753, Integer.Sparse.eval_collectBalanced, rawRowCheck8753]

theorem rawRowCheck8754 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form11 = rawRow8754 := by decide +kernel

theorem rowCheck8754 : row8754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8754 := by decide +kernel

theorem rowEval8754 (x : Key → ℝ) : Integer.Sparse.eval row8754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8754, Integer.Sparse.eval_collectBalanced, rawRowCheck8754]

theorem rawRowCheck8755 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form11 = rawRow8755 := by decide +kernel

theorem rowCheck8755 : row8755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8755 := by decide +kernel

theorem rowEval8755 (x : Key → ℝ) : Integer.Sparse.eval row8755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8755, Integer.Sparse.eval_collectBalanced, rawRowCheck8755]

theorem rawRowCheck8756 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form11 = rawRow8756 := by decide +kernel

theorem rowCheck8756 : row8756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8756 := by decide +kernel

theorem rowEval8756 (x : Key → ℝ) : Integer.Sparse.eval row8756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck8756, Integer.Sparse.eval_collectBalanced, rawRowCheck8756]

theorem rawRowCheck8825 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow8825 := by decide +kernel

theorem rowCheck8825 : row8825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8825 := by decide +kernel

theorem rowEval8825 (x : Key → ℝ) : Integer.Sparse.eval row8825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck8825, Integer.Sparse.eval_collectBalanced, rawRowCheck8825]

theorem rawRowCheck8826 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow8826 := by decide +kernel

theorem rowCheck8826 : row8826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8826 := by decide +kernel

theorem rowEval8826 (x : Key → ℝ) : Integer.Sparse.eval row8826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8826, Integer.Sparse.eval_collectBalanced, rawRowCheck8826]

theorem rawRowCheck8827 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow8827 := by decide +kernel

theorem rowCheck8827 : row8827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8827 := by decide +kernel

theorem rowEval8827 (x : Key → ℝ) : Integer.Sparse.eval row8827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8827, Integer.Sparse.eval_collectBalanced, rawRowCheck8827]

theorem rawRowCheck8828 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8828 := by decide +kernel

theorem rowCheck8828 : row8828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8828 := by decide +kernel

theorem rowEval8828 (x : Key → ℝ) : Integer.Sparse.eval row8828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8828, Integer.Sparse.eval_collectBalanced, rawRowCheck8828]

theorem rawRowCheck8829 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form11 = rawRow8829 := by decide +kernel

theorem rowCheck8829 : row8829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8829 := by decide +kernel

theorem rowEval8829 (x : Key → ℝ) : Integer.Sparse.eval row8829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8829, Integer.Sparse.eval_collectBalanced, rawRowCheck8829]

theorem rawRowCheck8830 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form11 = rawRow8830 := by decide +kernel

theorem rowCheck8830 : row8830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8830 := by decide +kernel

theorem rowEval8830 (x : Key → ℝ) : Integer.Sparse.eval row8830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8830, Integer.Sparse.eval_collectBalanced, rawRowCheck8830]

theorem rawRowCheck8831 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form11 = rawRow8831 := by decide +kernel

theorem rowCheck8831 : row8831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8831 := by decide +kernel

theorem rowEval8831 (x : Key → ℝ) : Integer.Sparse.eval row8831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck8831, Integer.Sparse.eval_collectBalanced, rawRowCheck8831]

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

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8669 x
  · exact rowEval8670 x
  · exact rowEval8671 x
  · exact rowEval8672 x
  · exact rowEval8673 x
  · exact rowEval8674 x
  · exact rowEval8675 x
  · exact rowEval8676 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

theorem entryCheck11_2 : entry11_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_2 k)) := by decide +kernel

theorem rowsSound11_2 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8677 x
  · exact rowEval8678 x
  · exact rowEval8679 x
  · exact rowEval8680 x
  · exact rowEval8681 x
  · exact rowEval8682 x
  · exact rowEval8683 x
  · exact rowEval8684 x

theorem entryEval11_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_2 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck11_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_2]

theorem entryCheck11_3 : entry11_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_3 k)) := by decide +kernel

theorem rowsSound11_3 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8685 x
  · exact rowEval8686 x
  · exact rowEval8687 x
  · exact rowEval8688 x
  · exact rowEval8689 x
  · exact rowEval8690 x
  · exact rowEval8691 x
  · exact rowEval8692 x

theorem entryEval11_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_3 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck11_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_3]

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

theorem entryCheck11_5 : entry11_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_5 k)) := by decide +kernel

theorem rowsSound11_5 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8701 x
  · exact rowEval8702 x
  · exact rowEval8703 x
  · exact rowEval8704 x
  · exact rowEval8705 x
  · exact rowEval8706 x
  · exact rowEval8707 x
  · exact rowEval8708 x

theorem entryEval11_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_5 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck11_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_5]

theorem entryCheck11_6 : entry11_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_6 k)) := by decide +kernel

theorem rowsSound11_6 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8709 x
  · exact rowEval8710 x
  · exact rowEval8711 x
  · exact rowEval8712 x
  · exact rowEval8713 x
  · exact rowEval8714 x
  · exact rowEval8715 x
  · exact rowEval8716 x

theorem entryEval11_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_6 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck11_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_6]

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

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8725 x
  · exact rowEval8726 x
  · exact rowEval8727 x
  · exact rowEval8728 x
  · exact rowEval8729 x
  · exact rowEval8730 x
  · exact rowEval8731 x
  · exact rowEval8732 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

theorem entryCheck11_9 : entry11_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_9 k)) := by decide +kernel

theorem rowsSound11_9 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8733 x
  · exact rowEval8734 x
  · exact rowEval8735 x
  · exact rowEval8736 x
  · exact rowEval8737 x
  · exact rowEval8738 x
  · exact rowEval8739 x
  · exact rowEval8740 x

theorem entryEval11_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_9 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck11_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_9]

theorem entryCheck11_10 : entry11_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_10 k)) := by decide +kernel

theorem rowsSound11_10 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8741 x
  · exact rowEval8742 x
  · exact rowEval8743 x
  · exact rowEval8744 x
  · exact rowEval8745 x
  · exact rowEval8746 x
  · exact rowEval8747 x
  · exact rowEval8748 x

theorem entryEval11_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_10 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck11_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_10]

theorem entryCheck11_11 : entry11_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form11.terms k).coefficient) (rows11_11 k)) := by decide +kernel

theorem rowsSound11_11 (k : Fin GramFunctions.Block3.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form11.terms k).tag (GramFunctions.Block3.form11.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval8749 x
  · exact rowEval8750 x
  · exact rowEval8751 x
  · exact rowEval8752 x
  · exact rowEval8753 x
  · exact rowEval8754 x
  · exact rowEval8755 x
  · exact rowEval8756 x

theorem entryEval11_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_11 (GramNormalization.eval B) = GramFunctions.Block3.form11.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck11_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form11 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_11]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck8832 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11 = rawRow8832 := by decide +kernel

theorem rowCheck8832 : row8832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8832 := by decide +kernel

theorem rowEval8832 (x : Key → ℝ) : Integer.Sparse.eval row8832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck8832, Integer.Sparse.eval_collectBalanced, rawRowCheck8832]

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

theorem entryCheck12_11 : entry12_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_11 k)) := by decide +kernel

theorem rowsSound12_11 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval8825 x
  · exact rowEval8826 x
  · exact rowEval8827 x
  · exact rowEval8828 x
  · exact rowEval8829 x
  · exact rowEval8830 x
  · exact rowEval8831 x
  · exact rowEval8832 x

theorem entryEval12_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_11 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck12_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_11]

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

theorem rawRowCheck9017 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow9017 := by decide +kernel

theorem rowCheck9017 : row9017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9017 := by decide +kernel

theorem rowEval9017 (x : Key → ℝ) : Integer.Sparse.eval row9017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9017, Integer.Sparse.eval_collectBalanced, rawRowCheck9017]

theorem rawRowCheck9018 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow9018 := by decide +kernel

theorem rowCheck9018 : row9018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9018 := by decide +kernel

theorem rowEval9018 (x : Key → ℝ) : Integer.Sparse.eval row9018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9018, Integer.Sparse.eval_collectBalanced, rawRowCheck9018]

theorem rawRowCheck9019 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow9019 := by decide +kernel

theorem rowCheck9019 : row9019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9019 := by decide +kernel

theorem rowEval9019 (x : Key → ℝ) : Integer.Sparse.eval row9019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9019, Integer.Sparse.eval_collectBalanced, rawRowCheck9019]

theorem rawRowCheck9020 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9020 := by decide +kernel

theorem rowCheck9020 : row9020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9020 := by decide +kernel

theorem rowEval9020 (x : Key → ℝ) : Integer.Sparse.eval row9020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9020, Integer.Sparse.eval_collectBalanced, rawRowCheck9020]

theorem rawRowCheck9021 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form11 = rawRow9021 := by decide +kernel

theorem rowCheck9021 : row9021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9021 := by decide +kernel

theorem rowEval9021 (x : Key → ℝ) : Integer.Sparse.eval row9021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9021, Integer.Sparse.eval_collectBalanced, rawRowCheck9021]

theorem rawRowCheck9022 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form11 = rawRow9022 := by decide +kernel

theorem rowCheck9022 : row9022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9022 := by decide +kernel

theorem rowEval9022 (x : Key → ℝ) : Integer.Sparse.eval row9022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9022, Integer.Sparse.eval_collectBalanced, rawRowCheck9022]

theorem rawRowCheck9023 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form11 = rawRow9023 := by decide +kernel

theorem rowCheck9023 : row9023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9023 := by decide +kernel

theorem rowEval9023 (x : Key → ℝ) : Integer.Sparse.eval row9023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9023, Integer.Sparse.eval_collectBalanced, rawRowCheck9023]

theorem rawRowCheck9024 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form11 = rawRow9024 := by decide +kernel

theorem rowCheck9024 : row9024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9024 := by decide +kernel

theorem rowEval9024 (x : Key → ℝ) : Integer.Sparse.eval row9024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9024, Integer.Sparse.eval_collectBalanced, rawRowCheck9024]

theorem rawRowCheck9025 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form11 = rawRow9025 := by decide +kernel

theorem rowCheck9025 : row9025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9025 := by decide +kernel

theorem rowEval9025 (x : Key → ℝ) : Integer.Sparse.eval row9025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9025, Integer.Sparse.eval_collectBalanced, rawRowCheck9025]

theorem rawRowCheck9026 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form11 = rawRow9026 := by decide +kernel

theorem rowCheck9026 : row9026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9026 := by decide +kernel

theorem rowEval9026 (x : Key → ℝ) : Integer.Sparse.eval row9026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9026, Integer.Sparse.eval_collectBalanced, rawRowCheck9026]

theorem rawRowCheck9027 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form11 = rawRow9027 := by decide +kernel

theorem rowCheck9027 : row9027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9027 := by decide +kernel

theorem rowEval9027 (x : Key → ℝ) : Integer.Sparse.eval row9027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9027, Integer.Sparse.eval_collectBalanced, rawRowCheck9027]

theorem rawRowCheck9028 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form11 = rawRow9028 := by decide +kernel

theorem rowCheck9028 : row9028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9028 := by decide +kernel

theorem rowEval9028 (x : Key → ℝ) : Integer.Sparse.eval row9028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9028, Integer.Sparse.eval_collectBalanced, rawRowCheck9028]

theorem rawRowCheck9029 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form11 = rawRow9029 := by decide +kernel

theorem rowCheck9029 : row9029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9029 := by decide +kernel

theorem rowEval9029 (x : Key → ℝ) : Integer.Sparse.eval row9029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9029, Integer.Sparse.eval_collectBalanced, rawRowCheck9029]

theorem rawRowCheck9030 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form11 = rawRow9030 := by decide +kernel

theorem rowCheck9030 : row9030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9030 := by decide +kernel

theorem rowEval9030 (x : Key → ℝ) : Integer.Sparse.eval row9030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9030, Integer.Sparse.eval_collectBalanced, rawRowCheck9030]

theorem rawRowCheck9031 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form11 = rawRow9031 := by decide +kernel

theorem rowCheck9031 : row9031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9031 := by decide +kernel

theorem rowEval9031 (x : Key → ℝ) : Integer.Sparse.eval row9031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9031, Integer.Sparse.eval_collectBalanced, rawRowCheck9031]

theorem rawRowCheck9032 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form11 = rawRow9032 := by decide +kernel

theorem rowCheck9032 : row9032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9032 := by decide +kernel

theorem rowEval9032 (x : Key → ℝ) : Integer.Sparse.eval row9032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9032, Integer.Sparse.eval_collectBalanced, rawRowCheck9032]

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

theorem entryCheck13_11 : entry13_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_11 k)) := by decide +kernel

theorem rowsSound13_11 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9017 x
  · exact rowEval9018 x
  · exact rowEval9019 x
  · exact rowEval9020 x
  · exact rowEval9021 x
  · exact rowEval9022 x
  · exact rowEval9023 x
  · exact rowEval9024 x
  · exact rowEval9025 x
  · exact rowEval9026 x
  · exact rowEval9027 x
  · exact rowEval9028 x
  · exact rowEval9029 x
  · exact rowEval9030 x
  · exact rowEval9031 x
  · exact rowEval9032 x

theorem entryEval13_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_11 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck13_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_11]

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

theorem rawRowCheck9141 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow9141 := by decide +kernel

theorem rowCheck9141 : row9141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9141 := by decide +kernel

theorem rowEval9141 (x : Key → ℝ) : Integer.Sparse.eval row9141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9141, Integer.Sparse.eval_collectBalanced, rawRowCheck9141]

theorem rawRowCheck9142 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow9142 := by decide +kernel

theorem rowCheck9142 : row9142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9142 := by decide +kernel

theorem rowEval9142 (x : Key → ℝ) : Integer.Sparse.eval row9142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9142, Integer.Sparse.eval_collectBalanced, rawRowCheck9142]

theorem rawRowCheck9143 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow9143 := by decide +kernel

theorem rowCheck9143 : row9143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9143 := by decide +kernel

theorem rowEval9143 (x : Key → ℝ) : Integer.Sparse.eval row9143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9143, Integer.Sparse.eval_collectBalanced, rawRowCheck9143]

theorem rawRowCheck9144 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9144 := by decide +kernel

theorem rowCheck9144 : row9144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9144 := by decide +kernel

theorem rowEval9144 (x : Key → ℝ) : Integer.Sparse.eval row9144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9144, Integer.Sparse.eval_collectBalanced, rawRowCheck9144]

theorem rawRowCheck9145 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9145 := by decide +kernel

theorem rowCheck9145 : row9145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9145 := by decide +kernel

theorem rowEval9145 (x : Key → ℝ) : Integer.Sparse.eval row9145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9145, Integer.Sparse.eval_collectBalanced, rawRowCheck9145]

theorem rawRowCheck9146 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form11 = rawRow9146 := by decide +kernel

theorem rowCheck9146 : row9146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9146 := by decide +kernel

theorem rowEval9146 (x : Key → ℝ) : Integer.Sparse.eval row9146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9146, Integer.Sparse.eval_collectBalanced, rawRowCheck9146]

theorem rawRowCheck9147 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form11 = rawRow9147 := by decide +kernel

theorem rowCheck9147 : row9147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9147 := by decide +kernel

theorem rowEval9147 (x : Key → ℝ) : Integer.Sparse.eval row9147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9147, Integer.Sparse.eval_collectBalanced, rawRowCheck9147]

theorem rawRowCheck9148 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11 = rawRow9148 := by decide +kernel

theorem rowCheck9148 : row9148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9148 := by decide +kernel

theorem rowEval9148 (x : Key → ℝ) : Integer.Sparse.eval row9148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9148, Integer.Sparse.eval_collectBalanced, rawRowCheck9148]

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

theorem entryCheck14_11 : entry14_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_11 k)) := by decide +kernel

theorem rowsSound14_11 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9141 x
  · exact rowEval9142 x
  · exact rowEval9143 x
  · exact rowEval9144 x
  · exact rowEval9145 x
  · exact rowEval9146 x
  · exact rowEval9147 x
  · exact rowEval9148 x

theorem entryEval14_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_11 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck14_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_11]

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

theorem rawRowCheck9305 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form11 = rawRow9305 := by decide +kernel

theorem rowCheck9305 : row9305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9305 := by decide +kernel

theorem rowEval9305 (x : Key → ℝ) : Integer.Sparse.eval row9305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9305, Integer.Sparse.eval_collectBalanced, rawRowCheck9305]

theorem rawRowCheck9306 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form11 = rawRow9306 := by decide +kernel

theorem rowCheck9306 : row9306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9306 := by decide +kernel

theorem rowEval9306 (x : Key → ℝ) : Integer.Sparse.eval row9306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9306, Integer.Sparse.eval_collectBalanced, rawRowCheck9306]

theorem rawRowCheck9307 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form11 = rawRow9307 := by decide +kernel

theorem rowCheck9307 : row9307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9307 := by decide +kernel

theorem rowEval9307 (x : Key → ℝ) : Integer.Sparse.eval row9307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9307, Integer.Sparse.eval_collectBalanced, rawRowCheck9307]

theorem rawRowCheck9308 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form11 = rawRow9308 := by decide +kernel

theorem rowCheck9308 : row9308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9308 := by decide +kernel

theorem rowEval9308 (x : Key → ℝ) : Integer.Sparse.eval row9308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9308, Integer.Sparse.eval_collectBalanced, rawRowCheck9308]

theorem rawRowCheck9309 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form11 = rawRow9309 := by decide +kernel

theorem rowCheck9309 : row9309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9309 := by decide +kernel

theorem rowEval9309 (x : Key → ℝ) : Integer.Sparse.eval row9309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9309, Integer.Sparse.eval_collectBalanced, rawRowCheck9309]

theorem rawRowCheck9310 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form11 = rawRow9310 := by decide +kernel

theorem rowCheck9310 : row9310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9310 := by decide +kernel

theorem rowEval9310 (x : Key → ℝ) : Integer.Sparse.eval row9310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9310, Integer.Sparse.eval_collectBalanced, rawRowCheck9310]

theorem rawRowCheck9311 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form11 = rawRow9311 := by decide +kernel

theorem rowCheck9311 : row9311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9311 := by decide +kernel

theorem rowEval9311 (x : Key → ℝ) : Integer.Sparse.eval row9311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9311, Integer.Sparse.eval_collectBalanced, rawRowCheck9311]

theorem rawRowCheck9312 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form11 = rawRow9312 := by decide +kernel

theorem rowCheck9312 : row9312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9312 := by decide +kernel

theorem rowEval9312 (x : Key → ℝ) : Integer.Sparse.eval row9312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9312, Integer.Sparse.eval_collectBalanced, rawRowCheck9312]

theorem rawRowCheck9313 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form11 = rawRow9313 := by decide +kernel

theorem rowCheck9313 : row9313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9313 := by decide +kernel

theorem rowEval9313 (x : Key → ℝ) : Integer.Sparse.eval row9313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9313, Integer.Sparse.eval_collectBalanced, rawRowCheck9313]

theorem rawRowCheck9314 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form11 = rawRow9314 := by decide +kernel

theorem rowCheck9314 : row9314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9314 := by decide +kernel

theorem rowEval9314 (x : Key → ℝ) : Integer.Sparse.eval row9314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9314, Integer.Sparse.eval_collectBalanced, rawRowCheck9314]

theorem rawRowCheck9315 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form11 = rawRow9315 := by decide +kernel

theorem rowCheck9315 : row9315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9315 := by decide +kernel

theorem rowEval9315 (x : Key → ℝ) : Integer.Sparse.eval row9315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9315, Integer.Sparse.eval_collectBalanced, rawRowCheck9315]

theorem rawRowCheck9316 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form11 = rawRow9316 := by decide +kernel

theorem rowCheck9316 : row9316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9316 := by decide +kernel

theorem rowEval9316 (x : Key → ℝ) : Integer.Sparse.eval row9316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9316, Integer.Sparse.eval_collectBalanced, rawRowCheck9316]

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

theorem rawRowCheck9453 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9453 := by decide +kernel

theorem rowCheck9453 : row9453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9453 := by decide +kernel

theorem rowEval9453 (x : Key → ℝ) : Integer.Sparse.eval row9453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9453, Integer.Sparse.eval_collectBalanced, rawRowCheck9453]

theorem rawRowCheck9454 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form11 = rawRow9454 := by decide +kernel

theorem rowCheck9454 : row9454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9454 := by decide +kernel

theorem rowEval9454 (x : Key → ℝ) : Integer.Sparse.eval row9454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9454, Integer.Sparse.eval_collectBalanced, rawRowCheck9454]

theorem rawRowCheck9455 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form11 = rawRow9455 := by decide +kernel

theorem rowCheck9455 : row9455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9455 := by decide +kernel

theorem rowEval9455 (x : Key → ℝ) : Integer.Sparse.eval row9455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9455, Integer.Sparse.eval_collectBalanced, rawRowCheck9455]

theorem rawRowCheck9456 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form11 = rawRow9456 := by decide +kernel

theorem rowCheck9456 : row9456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9456 := by decide +kernel

theorem rowEval9456 (x : Key → ℝ) : Integer.Sparse.eval row9456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9456, Integer.Sparse.eval_collectBalanced, rawRowCheck9456]

theorem rawRowCheck9457 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9457 := by decide +kernel

theorem rowCheck9457 : row9457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9457 := by decide +kernel

theorem rowEval9457 (x : Key → ℝ) : Integer.Sparse.eval row9457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9457, Integer.Sparse.eval_collectBalanced, rawRowCheck9457]

theorem rawRowCheck9458 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form11 = rawRow9458 := by decide +kernel

theorem rowCheck9458 : row9458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9458 := by decide +kernel

theorem rowEval9458 (x : Key → ℝ) : Integer.Sparse.eval row9458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9458, Integer.Sparse.eval_collectBalanced, rawRowCheck9458]

theorem rawRowCheck9459 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form11 = rawRow9459 := by decide +kernel

theorem rowCheck9459 : row9459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9459 := by decide +kernel

theorem rowEval9459 (x : Key → ℝ) : Integer.Sparse.eval row9459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9459, Integer.Sparse.eval_collectBalanced, rawRowCheck9459]

theorem rawRowCheck9460 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form11 = rawRow9460 := by decide +kernel

theorem rowCheck9460 : row9460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9460 := by decide +kernel

theorem rowEval9460 (x : Key → ℝ) : Integer.Sparse.eval row9460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9460, Integer.Sparse.eval_collectBalanced, rawRowCheck9460]

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

theorem entryCheck15_11 : entry15_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_11 k)) := by decide +kernel

theorem rowsSound15_11 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval8749 x
  · exact rowEval8750 x
  · exact rowEval8751 x
  · exact rowEval8752 x
  · exact rowEval9305 x
  · exact rowEval9306 x
  · exact rowEval9307 x
  · exact rowEval9308 x
  · exact rowEval9309 x
  · exact rowEval9310 x
  · exact rowEval9311 x
  · exact rowEval9312 x
  · exact rowEval9313 x
  · exact rowEval9314 x
  · exact rowEval9315 x
  · exact rowEval9316 x

theorem entryEval15_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_11 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck15_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_11]

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

theorem entryCheck16_11 : entry16_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_11 k)) := by decide +kernel

theorem rowsSound16_11 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9453 x
  · exact rowEval9454 x
  · exact rowEval9455 x
  · exact rowEval9456 x
  · exact rowEval9457 x
  · exact rowEval9458 x
  · exact rowEval9459 x
  · exact rowEval9460 x

theorem entryEval16_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_11 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck16_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_11]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck10499 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form11 = rawRow10499 := by decide +kernel

theorem rowCheck10499 : row10499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10499 := by decide +kernel

theorem rowEval10499 (x : Key → ℝ) : Integer.Sparse.eval row10499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10499, Integer.Sparse.eval_collectBalanced, rawRowCheck10499]

theorem rawRowCheck10500 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form11 = rawRow10500 := by decide +kernel

theorem rowCheck10500 : row10500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10500 := by decide +kernel

theorem rowEval10500 (x : Key → ℝ) : Integer.Sparse.eval row10500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10500, Integer.Sparse.eval_collectBalanced, rawRowCheck10500]

theorem rawRowCheck10501 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form11 = rawRow10501 := by decide +kernel

theorem rowCheck10501 : row10501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10501 := by decide +kernel

theorem rowEval10501 (x : Key → ℝ) : Integer.Sparse.eval row10501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10501, Integer.Sparse.eval_collectBalanced, rawRowCheck10501]

theorem rawRowCheck10502 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form11 = rawRow10502 := by decide +kernel

theorem rowCheck10502 : row10502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10502 := by decide +kernel

theorem rowEval10502 (x : Key → ℝ) : Integer.Sparse.eval row10502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10502, Integer.Sparse.eval_collectBalanced, rawRowCheck10502]

theorem rawRowCheck10503 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form11 = rawRow10503 := by decide +kernel

theorem rowCheck10503 : row10503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10503 := by decide +kernel

theorem rowEval10503 (x : Key → ℝ) : Integer.Sparse.eval row10503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10503, Integer.Sparse.eval_collectBalanced, rawRowCheck10503]

theorem rawRowCheck10504 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form11 = rawRow10504 := by decide +kernel

theorem rowCheck10504 : row10504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10504 := by decide +kernel

theorem rowEval10504 (x : Key → ℝ) : Integer.Sparse.eval row10504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10504, Integer.Sparse.eval_collectBalanced, rawRowCheck10504]

theorem rawRowCheck10505 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form11 = rawRow10505 := by decide +kernel

theorem rowCheck10505 : row10505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10505 := by decide +kernel

theorem rowEval10505 (x : Key → ℝ) : Integer.Sparse.eval row10505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10505, Integer.Sparse.eval_collectBalanced, rawRowCheck10505]

theorem rawRowCheck10506 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form11 = rawRow10506 := by decide +kernel

theorem rowCheck10506 : row10506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10506 := by decide +kernel

theorem rowEval10506 (x : Key → ℝ) : Integer.Sparse.eval row10506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10506, Integer.Sparse.eval_collectBalanced, rawRowCheck10506]

theorem rawRowCheck10507 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form11 = rawRow10507 := by decide +kernel

theorem rowCheck10507 : row10507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10507 := by decide +kernel

theorem rowEval10507 (x : Key → ℝ) : Integer.Sparse.eval row10507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10507, Integer.Sparse.eval_collectBalanced, rawRowCheck10507]

theorem rawRowCheck10508 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form11 = rawRow10508 := by decide +kernel

theorem rowCheck10508 : row10508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10508 := by decide +kernel

theorem rowEval10508 (x : Key → ℝ) : Integer.Sparse.eval row10508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10508, Integer.Sparse.eval_collectBalanced, rawRowCheck10508]

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

theorem entryCheck19_11 : entry19_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_11 k)) := by decide +kernel

theorem rowsSound19_11 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval10499 x
  · exact rowEval10500 x
  · exact rowEval10501 x
  · exact rowEval10502 x
  · exact rowEval10503 x
  · exact rowEval10504 x
  · exact rowEval10505 x
  · exact rowEval10506 x
  · exact rowEval10507 x
  · exact rowEval10508 x

theorem entryEval19_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_11 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck19_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_11]

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

theorem rawRowCheck10644 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow10644 := by decide +kernel

theorem rowCheck10644 : row10644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10644 := by decide +kernel

theorem rowEval10644 (x : Key → ℝ) : Integer.Sparse.eval row10644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck10644, Integer.Sparse.eval_collectBalanced, rawRowCheck10644]

theorem rawRowCheck10645 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow10645 := by decide +kernel

theorem rowCheck10645 : row10645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10645 := by decide +kernel

theorem rowEval10645 (x : Key → ℝ) : Integer.Sparse.eval row10645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10645, Integer.Sparse.eval_collectBalanced, rawRowCheck10645]

theorem rawRowCheck10646 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow10646 := by decide +kernel

theorem rowCheck10646 : row10646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10646 := by decide +kernel

theorem rowEval10646 (x : Key → ℝ) : Integer.Sparse.eval row10646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10646, Integer.Sparse.eval_collectBalanced, rawRowCheck10646]

theorem rawRowCheck10647 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow10647 := by decide +kernel

theorem rowCheck10647 : row10647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10647 := by decide +kernel

theorem rowEval10647 (x : Key → ℝ) : Integer.Sparse.eval row10647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10647, Integer.Sparse.eval_collectBalanced, rawRowCheck10647]

theorem rawRowCheck10648 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form11 = rawRow10648 := by decide +kernel

theorem rowCheck10648 : row10648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10648 := by decide +kernel

theorem rowEval10648 (x : Key → ℝ) : Integer.Sparse.eval row10648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10648, Integer.Sparse.eval_collectBalanced, rawRowCheck10648]

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

theorem entryCheck20_11 : entry20_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_11 k)) := by decide +kernel

theorem rowsSound20_11 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval10644 x
  · exact rowEval10645 x
  · exact rowEval10646 x
  · exact rowEval10647 x
  · exact rowEval10648 x

theorem entryEval20_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_11 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck20_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_11]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11972 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form11 = rawRow11972 := by decide +kernel

theorem rowCheck11972 : row11972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11972 := by decide +kernel

theorem rowEval11972 (x : Key → ℝ) : Integer.Sparse.eval row11972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11972, Integer.Sparse.eval_collectBalanced, rawRowCheck11972]

theorem rawRowCheck11973 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form11 = rawRow11973 := by decide +kernel

theorem rowCheck11973 : row11973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11973 := by decide +kernel

theorem rowEval11973 (x : Key → ℝ) : Integer.Sparse.eval row11973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11973, Integer.Sparse.eval_collectBalanced, rawRowCheck11973]

theorem rawRowCheck11974 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form11 = rawRow11974 := by decide +kernel

theorem rowCheck11974 : row11974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11974 := by decide +kernel

theorem rowEval11974 (x : Key → ℝ) : Integer.Sparse.eval row11974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11974, Integer.Sparse.eval_collectBalanced, rawRowCheck11974]

theorem rawRowCheck11975 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form11 = rawRow11975 := by decide +kernel

theorem rowCheck11975 : row11975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11975 := by decide +kernel

theorem rowEval11975 (x : Key → ℝ) : Integer.Sparse.eval row11975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11975, Integer.Sparse.eval_collectBalanced, rawRowCheck11975]

theorem rawRowCheck11976 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form11 = rawRow11976 := by decide +kernel

theorem rowCheck11976 : row11976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11976 := by decide +kernel

theorem rowEval11976 (x : Key → ℝ) : Integer.Sparse.eval row11976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11976, Integer.Sparse.eval_collectBalanced, rawRowCheck11976]

theorem rawRowCheck11977 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form11 = rawRow11977 := by decide +kernel

theorem rowCheck11977 : row11977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11977 := by decide +kernel

theorem rowEval11977 (x : Key → ℝ) : Integer.Sparse.eval row11977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11977, Integer.Sparse.eval_collectBalanced, rawRowCheck11977]

theorem rawRowCheck11978 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form11 = rawRow11978 := by decide +kernel

theorem rowCheck11978 : row11978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11978 := by decide +kernel

theorem rowEval11978 (x : Key → ℝ) : Integer.Sparse.eval row11978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11978, Integer.Sparse.eval_collectBalanced, rawRowCheck11978]

theorem rawRowCheck11979 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form11 = rawRow11979 := by decide +kernel

theorem rowCheck11979 : row11979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11979 := by decide +kernel

theorem rowEval11979 (x : Key → ℝ) : Integer.Sparse.eval row11979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11979, Integer.Sparse.eval_collectBalanced, rawRowCheck11979]

theorem rawRowCheck11980 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form11 = rawRow11980 := by decide +kernel

theorem rowCheck11980 : row11980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11980 := by decide +kernel

theorem rowEval11980 (x : Key → ℝ) : Integer.Sparse.eval row11980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11980, Integer.Sparse.eval_collectBalanced, rawRowCheck11980]

theorem rawRowCheck11981 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form11 = rawRow11981 := by decide +kernel

theorem rowCheck11981 : row11981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11981 := by decide +kernel

theorem rowEval11981 (x : Key → ℝ) : Integer.Sparse.eval row11981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11981, Integer.Sparse.eval_collectBalanced, rawRowCheck11981]

theorem rawRowCheck11982 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form11 = rawRow11982 := by decide +kernel

theorem rowCheck11982 : row11982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11982 := by decide +kernel

theorem rowEval11982 (x : Key → ℝ) : Integer.Sparse.eval row11982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11982, Integer.Sparse.eval_collectBalanced, rawRowCheck11982]

theorem rawRowCheck11983 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form11 = rawRow11983 := by decide +kernel

theorem rowCheck11983 : row11983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11983 := by decide +kernel

theorem rowEval11983 (x : Key → ℝ) : Integer.Sparse.eval row11983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11983, Integer.Sparse.eval_collectBalanced, rawRowCheck11983]

theorem rawRowCheck11984 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form11 = rawRow11984 := by decide +kernel

theorem rowCheck11984 : row11984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11984 := by decide +kernel

theorem rowEval11984 (x : Key → ℝ) : Integer.Sparse.eval row11984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11984, Integer.Sparse.eval_collectBalanced, rawRowCheck11984]

theorem rawRowCheck11985 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form11 = rawRow11985 := by decide +kernel

theorem rowCheck11985 : row11985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11985 := by decide +kernel

theorem rowEval11985 (x : Key → ℝ) : Integer.Sparse.eval row11985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11985, Integer.Sparse.eval_collectBalanced, rawRowCheck11985]

theorem rawRowCheck11986 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form11 = rawRow11986 := by decide +kernel

theorem rowCheck11986 : row11986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11986 := by decide +kernel

theorem rowEval11986 (x : Key → ℝ) : Integer.Sparse.eval row11986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11986, Integer.Sparse.eval_collectBalanced, rawRowCheck11986]

theorem rawRowCheck11987 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form11 = rawRow11987 := by decide +kernel

theorem rowCheck11987 : row11987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11987 := by decide +kernel

theorem rowEval11987 (x : Key → ℝ) : Integer.Sparse.eval row11987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11987, Integer.Sparse.eval_collectBalanced, rawRowCheck11987]

theorem rawRowCheck11988 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form11 = rawRow11988 := by decide +kernel

theorem rowCheck11988 : row11988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11988 := by decide +kernel

theorem rowEval11988 (x : Key → ℝ) : Integer.Sparse.eval row11988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11988, Integer.Sparse.eval_collectBalanced, rawRowCheck11988]

theorem rawRowCheck11989 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form11 = rawRow11989 := by decide +kernel

theorem rowCheck11989 : row11989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11989 := by decide +kernel

theorem rowEval11989 (x : Key → ℝ) : Integer.Sparse.eval row11989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11989, Integer.Sparse.eval_collectBalanced, rawRowCheck11989]

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

theorem rawRowCheck12261 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form11 = rawRow12261 := by decide +kernel

theorem rowCheck12261 : row12261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12261 := by decide +kernel

theorem rowEval12261 (x : Key → ℝ) : Integer.Sparse.eval row12261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12261, Integer.Sparse.eval_collectBalanced, rawRowCheck12261]

theorem rawRowCheck12262 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow12262 := by decide +kernel

theorem rowCheck12262 : row12262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12262 := by decide +kernel

theorem rowEval12262 (x : Key → ℝ) : Integer.Sparse.eval row12262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12262, Integer.Sparse.eval_collectBalanced, rawRowCheck12262]

theorem rawRowCheck12263 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form11 = rawRow12263 := by decide +kernel

theorem rowCheck12263 : row12263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12263 := by decide +kernel

theorem rowEval12263 (x : Key → ℝ) : Integer.Sparse.eval row12263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12263, Integer.Sparse.eval_collectBalanced, rawRowCheck12263]

theorem rawRowCheck12264 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form11 = rawRow12264 := by decide +kernel

theorem rowCheck12264 : row12264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12264 := by decide +kernel

theorem rowEval12264 (x : Key → ℝ) : Integer.Sparse.eval row12264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12264, Integer.Sparse.eval_collectBalanced, rawRowCheck12264]

theorem rawRowCheck12265 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form11 = rawRow12265 := by decide +kernel

theorem rowCheck12265 : row12265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12265 := by decide +kernel

theorem rowEval12265 (x : Key → ℝ) : Integer.Sparse.eval row12265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12265, Integer.Sparse.eval_collectBalanced, rawRowCheck12265]

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

theorem entryCheck23_11 : entry23_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_11 k)) := by decide +kernel

theorem rowsSound23_11 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval11972 x
  · exact rowEval11973 x
  · exact rowEval11974 x
  · exact rowEval11975 x
  · exact rowEval11976 x
  · exact rowEval11977 x
  · exact rowEval11978 x
  · exact rowEval11979 x
  · exact rowEval11980 x
  · exact rowEval11981 x
  · exact rowEval11982 x
  · exact rowEval11983 x
  · exact rowEval11984 x
  · exact rowEval11985 x
  · exact rowEval11986 x
  · exact rowEval11987 x
  · exact rowEval11988 x
  · exact rowEval11989 x

theorem entryEval23_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_11 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck23_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_11]

end MUB6.Certificate.GramEntries.Block3

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

theorem entryCheck24_11 : entry24_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_11 k)) := by decide +kernel

theorem rowsSound24_11 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval12261 x
  · exact rowEval12262 x
  · exact rowEval12263 x
  · exact rowEval12264 x
  · exact rowEval12265 x

theorem entryEval24_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_11 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck24_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_11]

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

theorem rawRowCheck12419 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form11 = rawRow12419 := by decide +kernel

theorem rowCheck12419 : row12419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12419 := by decide +kernel

theorem rowEval12419 (x : Key → ℝ) : Integer.Sparse.eval row12419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12419, Integer.Sparse.eval_collectBalanced, rawRowCheck12419]

theorem rawRowCheck12420 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form11 = rawRow12420 := by decide +kernel

theorem rowCheck12420 : row12420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12420 := by decide +kernel

theorem rowEval12420 (x : Key → ℝ) : Integer.Sparse.eval row12420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12420, Integer.Sparse.eval_collectBalanced, rawRowCheck12420]

theorem rawRowCheck12421 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form11 = rawRow12421 := by decide +kernel

theorem rowCheck12421 : row12421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12421 := by decide +kernel

theorem rowEval12421 (x : Key → ℝ) : Integer.Sparse.eval row12421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12421, Integer.Sparse.eval_collectBalanced, rawRowCheck12421]

theorem rawRowCheck12422 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form11 = rawRow12422 := by decide +kernel

theorem rowCheck12422 : row12422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12422 := by decide +kernel

theorem rowEval12422 (x : Key → ℝ) : Integer.Sparse.eval row12422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12422, Integer.Sparse.eval_collectBalanced, rawRowCheck12422]

theorem rawRowCheck12423 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form11 = rawRow12423 := by decide +kernel

theorem rowCheck12423 : row12423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12423 := by decide +kernel

theorem rowEval12423 (x : Key → ℝ) : Integer.Sparse.eval row12423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12423, Integer.Sparse.eval_collectBalanced, rawRowCheck12423]

theorem rawRowCheck12424 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form11 = rawRow12424 := by decide +kernel

theorem rowCheck12424 : row12424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12424 := by decide +kernel

theorem rowEval12424 (x : Key → ℝ) : Integer.Sparse.eval row12424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12424, Integer.Sparse.eval_collectBalanced, rawRowCheck12424]

theorem rawRowCheck12425 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form11 = rawRow12425 := by decide +kernel

theorem rowCheck12425 : row12425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12425 := by decide +kernel

theorem rowEval12425 (x : Key → ℝ) : Integer.Sparse.eval row12425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12425, Integer.Sparse.eval_collectBalanced, rawRowCheck12425]

theorem rawRowCheck12426 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form11 = rawRow12426 := by decide +kernel

theorem rowCheck12426 : row12426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12426 := by decide +kernel

theorem rowEval12426 (x : Key → ℝ) : Integer.Sparse.eval row12426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12426, Integer.Sparse.eval_collectBalanced, rawRowCheck12426]

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

theorem entryCheck25_11 : entry25_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_11 k)) := by decide +kernel

theorem rowsSound25_11 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval12419 x
  · exact rowEval12420 x
  · exact rowEval12421 x
  · exact rowEval12422 x
  · exact rowEval12423 x
  · exact rowEval12424 x
  · exact rowEval12425 x
  · exact rowEval12426 x

theorem entryEval25_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_11 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck25_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_11]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12803 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form11 = rawRow12803 := by decide +kernel

theorem rowCheck12803 : row12803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12803 := by decide +kernel

theorem rowEval12803 (x : Key → ℝ) : Integer.Sparse.eval row12803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12803, Integer.Sparse.eval_collectBalanced, rawRowCheck12803]

theorem rawRowCheck12804 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form11 = rawRow12804 := by decide +kernel

theorem rowCheck12804 : row12804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12804 := by decide +kernel

theorem rowEval12804 (x : Key → ℝ) : Integer.Sparse.eval row12804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12804, Integer.Sparse.eval_collectBalanced, rawRowCheck12804]

theorem rawRowCheck12805 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form11 = rawRow12805 := by decide +kernel

theorem rowCheck12805 : row12805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12805 := by decide +kernel

theorem rowEval12805 (x : Key → ℝ) : Integer.Sparse.eval row12805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12805, Integer.Sparse.eval_collectBalanced, rawRowCheck12805]

theorem rawRowCheck12806 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form11 = rawRow12806 := by decide +kernel

theorem rowCheck12806 : row12806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12806 := by decide +kernel

theorem rowEval12806 (x : Key → ℝ) : Integer.Sparse.eval row12806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12806, Integer.Sparse.eval_collectBalanced, rawRowCheck12806]

theorem rawRowCheck12807 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form11 = rawRow12807 := by decide +kernel

theorem rowCheck12807 : row12807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12807 := by decide +kernel

theorem rowEval12807 (x : Key → ℝ) : Integer.Sparse.eval row12807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12807, Integer.Sparse.eval_collectBalanced, rawRowCheck12807]

theorem rawRowCheck12808 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form11 = rawRow12808 := by decide +kernel

theorem rowCheck12808 : row12808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12808 := by decide +kernel

theorem rowEval12808 (x : Key → ℝ) : Integer.Sparse.eval row12808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12808, Integer.Sparse.eval_collectBalanced, rawRowCheck12808]

theorem rawRowCheck12809 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form11 = rawRow12809 := by decide +kernel

theorem rowCheck12809 : row12809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12809 := by decide +kernel

theorem rowEval12809 (x : Key → ℝ) : Integer.Sparse.eval row12809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12809, Integer.Sparse.eval_collectBalanced, rawRowCheck12809]

theorem rawRowCheck12810 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form11 = rawRow12810 := by decide +kernel

theorem rowCheck12810 : row12810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12810 := by decide +kernel

theorem rowEval12810 (x : Key → ℝ) : Integer.Sparse.eval row12810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12810, Integer.Sparse.eval_collectBalanced, rawRowCheck12810]

theorem rawRowCheck12811 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form11 = rawRow12811 := by decide +kernel

theorem rowCheck12811 : row12811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12811 := by decide +kernel

theorem rowEval12811 (x : Key → ℝ) : Integer.Sparse.eval row12811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12811, Integer.Sparse.eval_collectBalanced, rawRowCheck12811]

theorem rawRowCheck12812 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form11 = rawRow12812 := by decide +kernel

theorem rowCheck12812 : row12812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12812 := by decide +kernel

theorem rowEval12812 (x : Key → ℝ) : Integer.Sparse.eval row12812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12812, Integer.Sparse.eval_collectBalanced, rawRowCheck12812]

theorem rawRowCheck12813 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form11 = rawRow12813 := by decide +kernel

theorem rowCheck12813 : row12813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12813 := by decide +kernel

theorem rowEval12813 (x : Key → ℝ) : Integer.Sparse.eval row12813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12813, Integer.Sparse.eval_collectBalanced, rawRowCheck12813]

theorem rawRowCheck12814 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form11 = rawRow12814 := by decide +kernel

theorem rowCheck12814 : row12814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12814 := by decide +kernel

theorem rowEval12814 (x : Key → ℝ) : Integer.Sparse.eval row12814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12814, Integer.Sparse.eval_collectBalanced, rawRowCheck12814]

theorem rawRowCheck12815 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form11 = rawRow12815 := by decide +kernel

theorem rowCheck12815 : row12815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12815 := by decide +kernel

theorem rowEval12815 (x : Key → ℝ) : Integer.Sparse.eval row12815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12815, Integer.Sparse.eval_collectBalanced, rawRowCheck12815]

theorem rawRowCheck12816 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form11 = rawRow12816 := by decide +kernel

theorem rowCheck12816 : row12816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12816 := by decide +kernel

theorem rowEval12816 (x : Key → ℝ) : Integer.Sparse.eval row12816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12816, Integer.Sparse.eval_collectBalanced, rawRowCheck12816]

theorem rawRowCheck12817 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form11 = rawRow12817 := by decide +kernel

theorem rowCheck12817 : row12817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12817 := by decide +kernel

theorem rowEval12817 (x : Key → ℝ) : Integer.Sparse.eval row12817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12817, Integer.Sparse.eval_collectBalanced, rawRowCheck12817]

theorem rawRowCheck12818 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form11 = rawRow12818 := by decide +kernel

theorem rowCheck12818 : row12818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12818 := by decide +kernel

theorem rowEval12818 (x : Key → ℝ) : Integer.Sparse.eval row12818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12818, Integer.Sparse.eval_collectBalanced, rawRowCheck12818]

theorem rawRowCheck12819 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form11 = rawRow12819 := by decide +kernel

theorem rowCheck12819 : row12819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12819 := by decide +kernel

theorem rowEval12819 (x : Key → ℝ) : Integer.Sparse.eval row12819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12819, Integer.Sparse.eval_collectBalanced, rawRowCheck12819]

theorem rawRowCheck12820 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form11 = rawRow12820 := by decide +kernel

theorem rowCheck12820 : row12820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12820 := by decide +kernel

theorem rowEval12820 (x : Key → ℝ) : Integer.Sparse.eval row12820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12820, Integer.Sparse.eval_collectBalanced, rawRowCheck12820]

theorem rawRowCheck12821 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form11 = rawRow12821 := by decide +kernel

theorem rowCheck12821 : row12821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12821 := by decide +kernel

theorem rowEval12821 (x : Key → ℝ) : Integer.Sparse.eval row12821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12821, Integer.Sparse.eval_collectBalanced, rawRowCheck12821]

theorem rawRowCheck12822 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form11 = rawRow12822 := by decide +kernel

theorem rowCheck12822 : row12822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12822 := by decide +kernel

theorem rowEval12822 (x : Key → ℝ) : Integer.Sparse.eval row12822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12822, Integer.Sparse.eval_collectBalanced, rawRowCheck12822]

theorem rawRowCheck12823 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form11 = rawRow12823 := by decide +kernel

theorem rowCheck12823 : row12823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12823 := by decide +kernel

theorem rowEval12823 (x : Key → ℝ) : Integer.Sparse.eval row12823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12823, Integer.Sparse.eval_collectBalanced, rawRowCheck12823]

theorem rawRowCheck12824 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form11 = rawRow12824 := by decide +kernel

theorem rowCheck12824 : row12824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12824 := by decide +kernel

theorem rowEval12824 (x : Key → ℝ) : Integer.Sparse.eval row12824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12824, Integer.Sparse.eval_collectBalanced, rawRowCheck12824]

theorem rawRowCheck12825 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form11 = rawRow12825 := by decide +kernel

theorem rowCheck12825 : row12825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12825 := by decide +kernel

theorem rowEval12825 (x : Key → ℝ) : Integer.Sparse.eval row12825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12825, Integer.Sparse.eval_collectBalanced, rawRowCheck12825]

theorem rawRowCheck12826 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form11 = rawRow12826 := by decide +kernel

theorem rowCheck12826 : row12826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12826 := by decide +kernel

theorem rowEval12826 (x : Key → ℝ) : Integer.Sparse.eval row12826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12826, Integer.Sparse.eval_collectBalanced, rawRowCheck12826]

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

theorem entryCheck26_11 : entry26_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_11 k)) := by decide +kernel

theorem rowsSound26_11 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval12803 x
  · exact rowEval12804 x
  · exact rowEval12805 x
  · exact rowEval12806 x
  · exact rowEval12807 x
  · exact rowEval12808 x
  · exact rowEval12809 x
  · exact rowEval12810 x
  · exact rowEval12811 x
  · exact rowEval12812 x
  · exact rowEval12813 x
  · exact rowEval12814 x
  · exact rowEval12815 x
  · exact rowEval12816 x
  · exact rowEval12817 x
  · exact rowEval12818 x
  · exact rowEval12819 x
  · exact rowEval12820 x
  · exact rowEval12821 x
  · exact rowEval12822 x
  · exact rowEval12823 x
  · exact rowEval12824 x
  · exact rowEval12825 x
  · exact rowEval12826 x

theorem entryEval26_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_11 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck26_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_11]

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

theorem entryEvalRow11_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 11 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 11).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval11_0 B hB
  · exact entryEval11_1 B hB
  · exact entryEval11_2 B hB
  · exact entryEval11_3 B hB
  · exact entryEval11_4 B hB
  · exact entryEval11_5 B hB
  · exact entryEval11_6 B hB
  · exact entryEval11_7 B hB
  · exact entryEval11_8 B hB
  · exact entryEval11_9 B hB
  · exact entryEval11_10 B hB
  · exact entryEval11_11 B hB
  · exact (entryEval12_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e_oai
