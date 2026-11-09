-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:52:22.737161+00:00
-- url     : https://prove2.me/submissions/278049a8-1c3a-4422-b442-b1a3d544b48e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E038
import Definitions.Def_OAIQ106E041
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval5_2_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19334 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19334 := by decide +kernel

theorem rowCheck19334 : row19334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19334 := by decide +kernel

theorem rowEval19334 (x : Key → ℝ) : Integer.Sparse.eval row19334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19334, Integer.Sparse.eval_collectBalanced, rawRowCheck19334]

theorem rawRowCheck19335 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19335 := by decide +kernel

theorem rowCheck19335 : row19335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19335 := by decide +kernel

theorem rowEval19335 (x : Key → ℝ) : Integer.Sparse.eval row19335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19335, Integer.Sparse.eval_collectBalanced, rawRowCheck19335]

theorem rawRowCheck19336 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19336 := by decide +kernel

theorem rowCheck19336 : row19336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19336 := by decide +kernel

theorem rowEval19336 (x : Key → ℝ) : Integer.Sparse.eval row19336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19336, Integer.Sparse.eval_collectBalanced, rawRowCheck19336]

theorem rawRowCheck19337 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form5 = rawRow19337 := by decide +kernel

theorem rowCheck19337 : row19337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19337 := by decide +kernel

theorem rowEval19337 (x : Key → ℝ) : Integer.Sparse.eval row19337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19337, Integer.Sparse.eval_collectBalanced, rawRowCheck19337]

theorem rawRowCheck19338 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form5 = rawRow19338 := by decide +kernel

theorem rowCheck19338 : row19338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19338 := by decide +kernel

theorem rowEval19338 (x : Key → ℝ) : Integer.Sparse.eval row19338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19338, Integer.Sparse.eval_collectBalanced, rawRowCheck19338]

theorem rawRowCheck19339 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form5 = rawRow19339 := by decide +kernel

theorem rowCheck19339 : row19339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19339 := by decide +kernel

theorem rowEval19339 (x : Key → ℝ) : Integer.Sparse.eval row19339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19339, Integer.Sparse.eval_collectBalanced, rawRowCheck19339]

theorem rawRowCheck19340 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form5 = rawRow19340 := by decide +kernel

theorem rowCheck19340 : row19340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19340 := by decide +kernel

theorem rowEval19340 (x : Key → ℝ) : Integer.Sparse.eval row19340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19340, Integer.Sparse.eval_collectBalanced, rawRowCheck19340]

theorem rawRowCheck19341 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form5 = rawRow19341 := by decide +kernel

theorem rowCheck19341 : row19341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19341 := by decide +kernel

theorem rowEval19341 (x : Key → ℝ) : Integer.Sparse.eval row19341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19341, Integer.Sparse.eval_collectBalanced, rawRowCheck19341]

theorem rawRowCheck19342 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form5 = rawRow19342 := by decide +kernel

theorem rowCheck19342 : row19342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19342 := by decide +kernel

theorem rowEval19342 (x : Key → ℝ) : Integer.Sparse.eval row19342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19342, Integer.Sparse.eval_collectBalanced, rawRowCheck19342]

theorem rawRowCheck19343 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form5 = rawRow19343 := by decide +kernel

theorem rowCheck19343 : row19343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19343 := by decide +kernel

theorem rowEval19343 (x : Key → ℝ) : Integer.Sparse.eval row19343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19343, Integer.Sparse.eval_collectBalanced, rawRowCheck19343]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19484 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19484 := by decide +kernel

theorem rowCheck19484 : row19484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19484 := by decide +kernel

theorem rowEval19484 (x : Key → ℝ) : Integer.Sparse.eval row19484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19484, Integer.Sparse.eval_collectBalanced, rawRowCheck19484]

theorem rawRowCheck19485 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19485 := by decide +kernel

theorem rowCheck19485 : row19485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19485 := by decide +kernel

theorem rowEval19485 (x : Key → ℝ) : Integer.Sparse.eval row19485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19485, Integer.Sparse.eval_collectBalanced, rawRowCheck19485]

theorem rawRowCheck19486 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19486 := by decide +kernel

theorem rowCheck19486 : row19486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19486 := by decide +kernel

theorem rowEval19486 (x : Key → ℝ) : Integer.Sparse.eval row19486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19486, Integer.Sparse.eval_collectBalanced, rawRowCheck19486]

theorem rawRowCheck19487 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19487 := by decide +kernel

theorem rowCheck19487 : row19487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19487 := by decide +kernel

theorem rowEval19487 (x : Key → ℝ) : Integer.Sparse.eval row19487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19487, Integer.Sparse.eval_collectBalanced, rawRowCheck19487]

theorem rawRowCheck19488 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19488 := by decide +kernel

theorem rowCheck19488 : row19488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19488 := by decide +kernel

theorem rowEval19488 (x : Key → ℝ) : Integer.Sparse.eval row19488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19488, Integer.Sparse.eval_collectBalanced, rawRowCheck19488]

theorem rawRowCheck19489 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19489 := by decide +kernel

theorem rowCheck19489 : row19489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19489 := by decide +kernel

theorem rowEval19489 (x : Key → ℝ) : Integer.Sparse.eval row19489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19489, Integer.Sparse.eval_collectBalanced, rawRowCheck19489]

theorem rawRowCheck19490 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19490 := by decide +kernel

theorem rowCheck19490 : row19490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19490 := by decide +kernel

theorem rowEval19490 (x : Key → ℝ) : Integer.Sparse.eval row19490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19490, Integer.Sparse.eval_collectBalanced, rawRowCheck19490]

theorem rawRowCheck19491 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form5 = rawRow19491 := by decide +kernel

theorem rowCheck19491 : row19491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19491 := by decide +kernel

theorem rowEval19491 (x : Key → ℝ) : Integer.Sparse.eval row19491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19491, Integer.Sparse.eval_collectBalanced, rawRowCheck19491]

theorem rawRowCheck19492 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form5 = rawRow19492 := by decide +kernel

theorem rowCheck19492 : row19492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19492 := by decide +kernel

theorem rowEval19492 (x : Key → ℝ) : Integer.Sparse.eval row19492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19492, Integer.Sparse.eval_collectBalanced, rawRowCheck19492]

theorem rawRowCheck19493 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form5 = rawRow19493 := by decide +kernel

theorem rowCheck19493 : row19493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19493 := by decide +kernel

theorem rowEval19493 (x : Key → ℝ) : Integer.Sparse.eval row19493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19493, Integer.Sparse.eval_collectBalanced, rawRowCheck19493]

theorem rawRowCheck19494 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form5 = rawRow19494 := by decide +kernel

theorem rowCheck19494 : row19494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19494 := by decide +kernel

theorem rowEval19494 (x : Key → ℝ) : Integer.Sparse.eval row19494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19494, Integer.Sparse.eval_collectBalanced, rawRowCheck19494]

theorem rawRowCheck19495 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form5 = rawRow19495 := by decide +kernel

theorem rowCheck19495 : row19495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19495 := by decide +kernel

theorem rowEval19495 (x : Key → ℝ) : Integer.Sparse.eval row19495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19495, Integer.Sparse.eval_collectBalanced, rawRowCheck19495]

theorem rawRowCheck19496 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form5 = rawRow19496 := by decide +kernel

theorem rowCheck19496 : row19496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19496 := by decide +kernel

theorem rowEval19496 (x : Key → ℝ) : Integer.Sparse.eval row19496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19496, Integer.Sparse.eval_collectBalanced, rawRowCheck19496]

theorem rawRowCheck19497 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19497 := by decide +kernel

theorem rowCheck19497 : row19497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19497 := by decide +kernel

theorem rowEval19497 (x : Key → ℝ) : Integer.Sparse.eval row19497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19497, Integer.Sparse.eval_collectBalanced, rawRowCheck19497]

theorem rawRowCheck19498 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19498 := by decide +kernel

theorem rowCheck19498 : row19498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19498 := by decide +kernel

theorem rowEval19498 (x : Key → ℝ) : Integer.Sparse.eval row19498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19498, Integer.Sparse.eval_collectBalanced, rawRowCheck19498]

theorem rawRowCheck19499 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19499 := by decide +kernel

theorem rowCheck19499 : row19499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19499 := by decide +kernel

theorem rowEval19499 (x : Key → ℝ) : Integer.Sparse.eval row19499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19499, Integer.Sparse.eval_collectBalanced, rawRowCheck19499]

theorem rawRowCheck19500 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19500 := by decide +kernel

theorem rowCheck19500 : row19500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19500 := by decide +kernel

theorem rowEval19500 (x : Key → ℝ) : Integer.Sparse.eval row19500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19500, Integer.Sparse.eval_collectBalanced, rawRowCheck19500]

theorem rawRowCheck19501 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19501 := by decide +kernel

theorem rowCheck19501 : row19501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19501 := by decide +kernel

theorem rowEval19501 (x : Key → ℝ) : Integer.Sparse.eval row19501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19501, Integer.Sparse.eval_collectBalanced, rawRowCheck19501]

theorem rawRowCheck19502 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19502 := by decide +kernel

theorem rowCheck19502 : row19502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19502 := by decide +kernel

theorem rowEval19502 (x : Key → ℝ) : Integer.Sparse.eval row19502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19502, Integer.Sparse.eval_collectBalanced, rawRowCheck19502]

theorem rawRowCheck19503 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19503 := by decide +kernel

theorem rowCheck19503 : row19503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19503 := by decide +kernel

theorem rowEval19503 (x : Key → ℝ) : Integer.Sparse.eval row19503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19503, Integer.Sparse.eval_collectBalanced, rawRowCheck19503]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_5 : entry10_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_5 k)) := by decide +kernel

theorem rowsSound10_5 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19484 x
  · exact rowEval19485 x
  · exact rowEval19486 x
  · exact rowEval19487 x
  · exact rowEval19488 x
  · exact rowEval19489 x
  · exact rowEval19490 x
  · exact rowEval19491 x
  · exact rowEval19492 x
  · exact rowEval19493 x
  · exact rowEval19494 x
  · exact rowEval19495 x
  · exact rowEval19496 x
  · exact rowEval19497 x
  · exact rowEval19498 x
  · exact rowEval19499 x
  · exact rowEval19500 x
  · exact rowEval19501 x
  · exact rowEval19502 x
  · exact rowEval19503 x

theorem entryEval10_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_5 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck10_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_5]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18759 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form0 = rawRow18759 := by decide +kernel

theorem rowCheck18759 : row18759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18759 := by decide +kernel

theorem rowEval18759 (x : Key → ℝ) : Integer.Sparse.eval row18759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18759, Integer.Sparse.eval_collectBalanced, rawRowCheck18759]

theorem rawRowCheck18760 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form0 = rawRow18760 := by decide +kernel

theorem rowCheck18760 : row18760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18760 := by decide +kernel

theorem rowEval18760 (x : Key → ℝ) : Integer.Sparse.eval row18760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18760, Integer.Sparse.eval_collectBalanced, rawRowCheck18760]

theorem rawRowCheck18761 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form0 = rawRow18761 := by decide +kernel

theorem rowCheck18761 : row18761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18761 := by decide +kernel

theorem rowEval18761 (x : Key → ℝ) : Integer.Sparse.eval row18761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18761, Integer.Sparse.eval_collectBalanced, rawRowCheck18761]

theorem rawRowCheck18762 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18762 := by decide +kernel

theorem rowCheck18762 : row18762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18762 := by decide +kernel

theorem rowEval18762 (x : Key → ℝ) : Integer.Sparse.eval row18762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18762, Integer.Sparse.eval_collectBalanced, rawRowCheck18762]

theorem rawRowCheck18763 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18763 := by decide +kernel

theorem rowCheck18763 : row18763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18763 := by decide +kernel

theorem rowEval18763 (x : Key → ℝ) : Integer.Sparse.eval row18763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18763, Integer.Sparse.eval_collectBalanced, rawRowCheck18763]

theorem rawRowCheck18764 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18764 := by decide +kernel

theorem rowCheck18764 : row18764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18764 := by decide +kernel

theorem rowEval18764 (x : Key → ℝ) : Integer.Sparse.eval row18764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18764, Integer.Sparse.eval_collectBalanced, rawRowCheck18764]

theorem rawRowCheck18765 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form0 = rawRow18765 := by decide +kernel

theorem rowCheck18765 : row18765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18765 := by decide +kernel

theorem rowEval18765 (x : Key → ℝ) : Integer.Sparse.eval row18765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18765, Integer.Sparse.eval_collectBalanced, rawRowCheck18765]

theorem rawRowCheck18766 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form0 = rawRow18766 := by decide +kernel

theorem rowCheck18766 : row18766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18766 := by decide +kernel

theorem rowEval18766 (x : Key → ℝ) : Integer.Sparse.eval row18766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18766, Integer.Sparse.eval_collectBalanced, rawRowCheck18766]

theorem rawRowCheck18767 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form0 = rawRow18767 := by decide +kernel

theorem rowCheck18767 : row18767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18767 := by decide +kernel

theorem rowEval18767 (x : Key → ℝ) : Integer.Sparse.eval row18767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18767, Integer.Sparse.eval_collectBalanced, rawRowCheck18767]

theorem rawRowCheck18768 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form0 = rawRow18768 := by decide +kernel

theorem rowCheck18768 : row18768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18768 := by decide +kernel

theorem rowEval18768 (x : Key → ℝ) : Integer.Sparse.eval row18768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18768, Integer.Sparse.eval_collectBalanced, rawRowCheck18768]

theorem rawRowCheck18769 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form0 = rawRow18769 := by decide +kernel

theorem rowCheck18769 : row18769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18769 := by decide +kernel

theorem rowEval18769 (x : Key → ℝ) : Integer.Sparse.eval row18769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18769, Integer.Sparse.eval_collectBalanced, rawRowCheck18769]

theorem rawRowCheck18770 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form0 = rawRow18770 := by decide +kernel

theorem rowCheck18770 : row18770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18770 := by decide +kernel

theorem rowEval18770 (x : Key → ℝ) : Integer.Sparse.eval row18770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18770, Integer.Sparse.eval_collectBalanced, rawRowCheck18770]

theorem rawRowCheck18771 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form0 = rawRow18771 := by decide +kernel

theorem rowCheck18771 : row18771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18771 := by decide +kernel

theorem rowEval18771 (x : Key → ℝ) : Integer.Sparse.eval row18771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18771, Integer.Sparse.eval_collectBalanced, rawRowCheck18771]

theorem rawRowCheck18772 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form0 = rawRow18772 := by decide +kernel

theorem rowCheck18772 : row18772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18772 := by decide +kernel

theorem rowEval18772 (x : Key → ℝ) : Integer.Sparse.eval row18772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18772, Integer.Sparse.eval_collectBalanced, rawRowCheck18772]

theorem rawRowCheck18773 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form0 = rawRow18773 := by decide +kernel

theorem rowCheck18773 : row18773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18773 := by decide +kernel

theorem rowEval18773 (x : Key → ℝ) : Integer.Sparse.eval row18773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18773, Integer.Sparse.eval_collectBalanced, rawRowCheck18773]

theorem rawRowCheck18774 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form0 = rawRow18774 := by decide +kernel

theorem rowCheck18774 : row18774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18774 := by decide +kernel

theorem rowEval18774 (x : Key → ℝ) : Integer.Sparse.eval row18774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18774, Integer.Sparse.eval_collectBalanced, rawRowCheck18774]

theorem rawRowCheck18775 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form0 = rawRow18775 := by decide +kernel

theorem rowCheck18775 : row18775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18775 := by decide +kernel

theorem rowEval18775 (x : Key → ℝ) : Integer.Sparse.eval row18775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18775, Integer.Sparse.eval_collectBalanced, rawRowCheck18775]

theorem rawRowCheck18776 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form0 = rawRow18776 := by decide +kernel

theorem rowCheck18776 : row18776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18776 := by decide +kernel

theorem rowEval18776 (x : Key → ℝ) : Integer.Sparse.eval row18776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18776, Integer.Sparse.eval_collectBalanced, rawRowCheck18776]

theorem rawRowCheck18777 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18777 := by decide +kernel

theorem rowCheck18777 : row18777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18777 := by decide +kernel

theorem rowEval18777 (x : Key → ℝ) : Integer.Sparse.eval row18777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18777, Integer.Sparse.eval_collectBalanced, rawRowCheck18777]

theorem rawRowCheck18778 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18778 := by decide +kernel

theorem rowCheck18778 : row18778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18778 := by decide +kernel

theorem rowEval18778 (x : Key → ℝ) : Integer.Sparse.eval row18778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18778, Integer.Sparse.eval_collectBalanced, rawRowCheck18778]

theorem rawRowCheck18779 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18779 := by decide +kernel

theorem rowCheck18779 : row18779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18779 := by decide +kernel

theorem rowEval18779 (x : Key → ℝ) : Integer.Sparse.eval row18779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18779, Integer.Sparse.eval_collectBalanced, rawRowCheck18779]

theorem rawRowCheck18780 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form0 = rawRow18780 := by decide +kernel

theorem rowCheck18780 : row18780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18780 := by decide +kernel

theorem rowEval18780 (x : Key → ℝ) : Integer.Sparse.eval row18780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18780, Integer.Sparse.eval_collectBalanced, rawRowCheck18780]

theorem rawRowCheck18781 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form0 = rawRow18781 := by decide +kernel

theorem rowCheck18781 : row18781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18781 := by decide +kernel

theorem rowEval18781 (x : Key → ℝ) : Integer.Sparse.eval row18781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18781, Integer.Sparse.eval_collectBalanced, rawRowCheck18781]

theorem rawRowCheck18782 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form0 = rawRow18782 := by decide +kernel

theorem rowCheck18782 : row18782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18782 := by decide +kernel

theorem rowEval18782 (x : Key → ℝ) : Integer.Sparse.eval row18782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18782, Integer.Sparse.eval_collectBalanced, rawRowCheck18782]

theorem rawRowCheck18783 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form0 = rawRow18783 := by decide +kernel

theorem rowCheck18783 : row18783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18783 := by decide +kernel

theorem rowEval18783 (x : Key → ℝ) : Integer.Sparse.eval row18783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18783, Integer.Sparse.eval_collectBalanced, rawRowCheck18783]

theorem rawRowCheck18784 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form0 = rawRow18784 := by decide +kernel

theorem rowCheck18784 : row18784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18784 := by decide +kernel

theorem rowEval18784 (x : Key → ℝ) : Integer.Sparse.eval row18784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18784, Integer.Sparse.eval_collectBalanced, rawRowCheck18784]

theorem rawRowCheck18785 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form0 = rawRow18785 := by decide +kernel

theorem rowCheck18785 : row18785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18785 := by decide +kernel

theorem rowEval18785 (x : Key → ℝ) : Integer.Sparse.eval row18785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18785, Integer.Sparse.eval_collectBalanced, rawRowCheck18785]

theorem rawRowCheck18786 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18786 := by decide +kernel

theorem rowCheck18786 : row18786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18786 := by decide +kernel

theorem rowEval18786 (x : Key → ℝ) : Integer.Sparse.eval row18786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18786, Integer.Sparse.eval_collectBalanced, rawRowCheck18786]

theorem rawRowCheck18787 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18787 := by decide +kernel

theorem rowCheck18787 : row18787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18787 := by decide +kernel

theorem rowEval18787 (x : Key → ℝ) : Integer.Sparse.eval row18787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18787, Integer.Sparse.eval_collectBalanced, rawRowCheck18787]

theorem rawRowCheck18788 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18788 := by decide +kernel

theorem rowCheck18788 : row18788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18788 := by decide +kernel

theorem rowEval18788 (x : Key → ℝ) : Integer.Sparse.eval row18788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18788, Integer.Sparse.eval_collectBalanced, rawRowCheck18788]

theorem rawRowCheck18789 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form1 = rawRow18789 := by decide +kernel

theorem rowCheck18789 : row18789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18789 := by decide +kernel

theorem rowEval18789 (x : Key → ℝ) : Integer.Sparse.eval row18789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18789, Integer.Sparse.eval_collectBalanced, rawRowCheck18789]

theorem rawRowCheck18790 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form1 = rawRow18790 := by decide +kernel

theorem rowCheck18790 : row18790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18790 := by decide +kernel

theorem rowEval18790 (x : Key → ℝ) : Integer.Sparse.eval row18790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18790, Integer.Sparse.eval_collectBalanced, rawRowCheck18790]

theorem rawRowCheck18791 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form1 = rawRow18791 := by decide +kernel

theorem rowCheck18791 : row18791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18791 := by decide +kernel

theorem rowEval18791 (x : Key → ℝ) : Integer.Sparse.eval row18791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18791, Integer.Sparse.eval_collectBalanced, rawRowCheck18791]

theorem rawRowCheck18792 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18792 := by decide +kernel

theorem rowCheck18792 : row18792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18792 := by decide +kernel

theorem rowEval18792 (x : Key → ℝ) : Integer.Sparse.eval row18792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18792, Integer.Sparse.eval_collectBalanced, rawRowCheck18792]

theorem rawRowCheck18793 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18793 := by decide +kernel

theorem rowCheck18793 : row18793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18793 := by decide +kernel

theorem rowEval18793 (x : Key → ℝ) : Integer.Sparse.eval row18793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18793, Integer.Sparse.eval_collectBalanced, rawRowCheck18793]

theorem rawRowCheck18794 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18794 := by decide +kernel

theorem rowCheck18794 : row18794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18794 := by decide +kernel

theorem rowEval18794 (x : Key → ℝ) : Integer.Sparse.eval row18794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18794, Integer.Sparse.eval_collectBalanced, rawRowCheck18794]

theorem rawRowCheck18795 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form1 = rawRow18795 := by decide +kernel

theorem rowCheck18795 : row18795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18795 := by decide +kernel

theorem rowEval18795 (x : Key → ℝ) : Integer.Sparse.eval row18795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18795, Integer.Sparse.eval_collectBalanced, rawRowCheck18795]

theorem rawRowCheck18796 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form1 = rawRow18796 := by decide +kernel

theorem rowCheck18796 : row18796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18796 := by decide +kernel

theorem rowEval18796 (x : Key → ℝ) : Integer.Sparse.eval row18796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18796, Integer.Sparse.eval_collectBalanced, rawRowCheck18796]

theorem rawRowCheck18797 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form1 = rawRow18797 := by decide +kernel

theorem rowCheck18797 : row18797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18797 := by decide +kernel

theorem rowEval18797 (x : Key → ℝ) : Integer.Sparse.eval row18797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18797, Integer.Sparse.eval_collectBalanced, rawRowCheck18797]

theorem rawRowCheck18798 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form1 = rawRow18798 := by decide +kernel

theorem rowCheck18798 : row18798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18798 := by decide +kernel

theorem rowEval18798 (x : Key → ℝ) : Integer.Sparse.eval row18798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18798, Integer.Sparse.eval_collectBalanced, rawRowCheck18798]

theorem rawRowCheck18799 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form1 = rawRow18799 := by decide +kernel

theorem rowCheck18799 : row18799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18799 := by decide +kernel

theorem rowEval18799 (x : Key → ℝ) : Integer.Sparse.eval row18799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18799, Integer.Sparse.eval_collectBalanced, rawRowCheck18799]

theorem rawRowCheck18800 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form1 = rawRow18800 := by decide +kernel

theorem rowCheck18800 : row18800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18800 := by decide +kernel

theorem rowEval18800 (x : Key → ℝ) : Integer.Sparse.eval row18800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18800, Integer.Sparse.eval_collectBalanced, rawRowCheck18800]

theorem rawRowCheck18801 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form1 = rawRow18801 := by decide +kernel

theorem rowCheck18801 : row18801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18801 := by decide +kernel

theorem rowEval18801 (x : Key → ℝ) : Integer.Sparse.eval row18801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18801, Integer.Sparse.eval_collectBalanced, rawRowCheck18801]

theorem rawRowCheck18802 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form1 = rawRow18802 := by decide +kernel

theorem rowCheck18802 : row18802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18802 := by decide +kernel

theorem rowEval18802 (x : Key → ℝ) : Integer.Sparse.eval row18802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18802, Integer.Sparse.eval_collectBalanced, rawRowCheck18802]

theorem rawRowCheck18803 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form1 = rawRow18803 := by decide +kernel

theorem rowCheck18803 : row18803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18803 := by decide +kernel

theorem rowEval18803 (x : Key → ℝ) : Integer.Sparse.eval row18803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18803, Integer.Sparse.eval_collectBalanced, rawRowCheck18803]

theorem rawRowCheck18804 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form1 = rawRow18804 := by decide +kernel

theorem rowCheck18804 : row18804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18804 := by decide +kernel

theorem rowEval18804 (x : Key → ℝ) : Integer.Sparse.eval row18804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18804, Integer.Sparse.eval_collectBalanced, rawRowCheck18804]

theorem rawRowCheck18805 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form1 = rawRow18805 := by decide +kernel

theorem rowCheck18805 : row18805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18805 := by decide +kernel

theorem rowEval18805 (x : Key → ℝ) : Integer.Sparse.eval row18805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18805, Integer.Sparse.eval_collectBalanced, rawRowCheck18805]

theorem rawRowCheck18806 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form1 = rawRow18806 := by decide +kernel

theorem rowCheck18806 : row18806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18806 := by decide +kernel

theorem rowEval18806 (x : Key → ℝ) : Integer.Sparse.eval row18806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18806, Integer.Sparse.eval_collectBalanced, rawRowCheck18806]

theorem rawRowCheck18807 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18807 := by decide +kernel

theorem rowCheck18807 : row18807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18807 := by decide +kernel

theorem rowEval18807 (x : Key → ℝ) : Integer.Sparse.eval row18807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18807, Integer.Sparse.eval_collectBalanced, rawRowCheck18807]

theorem rawRowCheck18808 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18808 := by decide +kernel

theorem rowCheck18808 : row18808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18808 := by decide +kernel

theorem rowEval18808 (x : Key → ℝ) : Integer.Sparse.eval row18808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18808, Integer.Sparse.eval_collectBalanced, rawRowCheck18808]

theorem rawRowCheck18809 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18809 := by decide +kernel

theorem rowCheck18809 : row18809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18809 := by decide +kernel

theorem rowEval18809 (x : Key → ℝ) : Integer.Sparse.eval row18809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18809, Integer.Sparse.eval_collectBalanced, rawRowCheck18809]

theorem rawRowCheck18810 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form1 = rawRow18810 := by decide +kernel

theorem rowCheck18810 : row18810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18810 := by decide +kernel

theorem rowEval18810 (x : Key → ℝ) : Integer.Sparse.eval row18810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18810, Integer.Sparse.eval_collectBalanced, rawRowCheck18810]

theorem rawRowCheck18811 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form1 = rawRow18811 := by decide +kernel

theorem rowCheck18811 : row18811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18811 := by decide +kernel

theorem rowEval18811 (x : Key → ℝ) : Integer.Sparse.eval row18811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18811, Integer.Sparse.eval_collectBalanced, rawRowCheck18811]

theorem rawRowCheck18812 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form1 = rawRow18812 := by decide +kernel

theorem rowCheck18812 : row18812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18812 := by decide +kernel

theorem rowEval18812 (x : Key → ℝ) : Integer.Sparse.eval row18812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18812, Integer.Sparse.eval_collectBalanced, rawRowCheck18812]

theorem rawRowCheck18813 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form1 = rawRow18813 := by decide +kernel

theorem rowCheck18813 : row18813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18813 := by decide +kernel

theorem rowEval18813 (x : Key → ℝ) : Integer.Sparse.eval row18813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18813, Integer.Sparse.eval_collectBalanced, rawRowCheck18813]

theorem rawRowCheck18814 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form1 = rawRow18814 := by decide +kernel

theorem rowCheck18814 : row18814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18814 := by decide +kernel

theorem rowEval18814 (x : Key → ℝ) : Integer.Sparse.eval row18814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18814, Integer.Sparse.eval_collectBalanced, rawRowCheck18814]

theorem rawRowCheck18815 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form1 = rawRow18815 := by decide +kernel

theorem rowCheck18815 : row18815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18815 := by decide +kernel

theorem rowEval18815 (x : Key → ℝ) : Integer.Sparse.eval row18815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18815, Integer.Sparse.eval_collectBalanced, rawRowCheck18815]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18816 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18816 := by decide +kernel

theorem rowCheck18816 : row18816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18816 := by decide +kernel

theorem rowEval18816 (x : Key → ℝ) : Integer.Sparse.eval row18816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18816, Integer.Sparse.eval_collectBalanced, rawRowCheck18816]

theorem rawRowCheck18817 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18817 := by decide +kernel

theorem rowCheck18817 : row18817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18817 := by decide +kernel

theorem rowEval18817 (x : Key → ℝ) : Integer.Sparse.eval row18817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18817, Integer.Sparse.eval_collectBalanced, rawRowCheck18817]

theorem rawRowCheck18818 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18818 := by decide +kernel

theorem rowCheck18818 : row18818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18818 := by decide +kernel

theorem rowEval18818 (x : Key → ℝ) : Integer.Sparse.eval row18818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18818, Integer.Sparse.eval_collectBalanced, rawRowCheck18818]

theorem rawRowCheck18849 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form3 = rawRow18849 := by decide +kernel

theorem rowCheck18849 : row18849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18849 := by decide +kernel

theorem rowEval18849 (x : Key → ℝ) : Integer.Sparse.eval row18849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18849, Integer.Sparse.eval_collectBalanced, rawRowCheck18849]

theorem rawRowCheck18850 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form3 = rawRow18850 := by decide +kernel

theorem rowCheck18850 : row18850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18850 := by decide +kernel

theorem rowEval18850 (x : Key → ℝ) : Integer.Sparse.eval row18850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18850, Integer.Sparse.eval_collectBalanced, rawRowCheck18850]

theorem rawRowCheck18851 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form3 = rawRow18851 := by decide +kernel

theorem rowCheck18851 : row18851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18851 := by decide +kernel

theorem rowEval18851 (x : Key → ℝ) : Integer.Sparse.eval row18851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18851, Integer.Sparse.eval_collectBalanced, rawRowCheck18851]

theorem rawRowCheck18852 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form3 = rawRow18852 := by decide +kernel

theorem rowCheck18852 : row18852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18852 := by decide +kernel

theorem rowEval18852 (x : Key → ℝ) : Integer.Sparse.eval row18852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18852, Integer.Sparse.eval_collectBalanced, rawRowCheck18852]

theorem rawRowCheck18853 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form3 = rawRow18853 := by decide +kernel

theorem rowCheck18853 : row18853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18853 := by decide +kernel

theorem rowEval18853 (x : Key → ℝ) : Integer.Sparse.eval row18853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18853, Integer.Sparse.eval_collectBalanced, rawRowCheck18853]

theorem rawRowCheck18854 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form3 = rawRow18854 := by decide +kernel

theorem rowCheck18854 : row18854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18854 := by decide +kernel

theorem rowEval18854 (x : Key → ℝ) : Integer.Sparse.eval row18854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18854, Integer.Sparse.eval_collectBalanced, rawRowCheck18854]

theorem rawRowCheck18855 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form3 = rawRow18855 := by decide +kernel

theorem rowCheck18855 : row18855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18855 := by decide +kernel

theorem rowEval18855 (x : Key → ℝ) : Integer.Sparse.eval row18855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18855, Integer.Sparse.eval_collectBalanced, rawRowCheck18855]

theorem rawRowCheck18856 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form3 = rawRow18856 := by decide +kernel

theorem rowCheck18856 : row18856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18856 := by decide +kernel

theorem rowEval18856 (x : Key → ℝ) : Integer.Sparse.eval row18856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18856, Integer.Sparse.eval_collectBalanced, rawRowCheck18856]

theorem rawRowCheck18857 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form3 = rawRow18857 := by decide +kernel

theorem rowCheck18857 : row18857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18857 := by decide +kernel

theorem rowEval18857 (x : Key → ℝ) : Integer.Sparse.eval row18857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18857, Integer.Sparse.eval_collectBalanced, rawRowCheck18857]

theorem rawRowCheck18858 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form3 = rawRow18858 := by decide +kernel

theorem rowCheck18858 : row18858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18858 := by decide +kernel

theorem rowEval18858 (x : Key → ℝ) : Integer.Sparse.eval row18858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18858, Integer.Sparse.eval_collectBalanced, rawRowCheck18858]

theorem rawRowCheck18859 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form3 = rawRow18859 := by decide +kernel

theorem rowCheck18859 : row18859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18859 := by decide +kernel

theorem rowEval18859 (x : Key → ℝ) : Integer.Sparse.eval row18859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18859, Integer.Sparse.eval_collectBalanced, rawRowCheck18859]

theorem rawRowCheck18860 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form3 = rawRow18860 := by decide +kernel

theorem rowCheck18860 : row18860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18860 := by decide +kernel

theorem rowEval18860 (x : Key → ℝ) : Integer.Sparse.eval row18860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18860, Integer.Sparse.eval_collectBalanced, rawRowCheck18860]

theorem rawRowCheck18861 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form3 = rawRow18861 := by decide +kernel

theorem rowCheck18861 : row18861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18861 := by decide +kernel

theorem rowEval18861 (x : Key → ℝ) : Integer.Sparse.eval row18861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18861, Integer.Sparse.eval_collectBalanced, rawRowCheck18861]

theorem rawRowCheck18862 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form3 = rawRow18862 := by decide +kernel

theorem rowCheck18862 : row18862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18862 := by decide +kernel

theorem rowEval18862 (x : Key → ℝ) : Integer.Sparse.eval row18862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18862, Integer.Sparse.eval_collectBalanced, rawRowCheck18862]

theorem rawRowCheck18863 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form3 = rawRow18863 := by decide +kernel

theorem rowCheck18863 : row18863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18863 := by decide +kernel

theorem rowEval18863 (x : Key → ℝ) : Integer.Sparse.eval row18863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18863, Integer.Sparse.eval_collectBalanced, rawRowCheck18863]

theorem rawRowCheck18864 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form3 = rawRow18864 := by decide +kernel

theorem rowCheck18864 : row18864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18864 := by decide +kernel

theorem rowEval18864 (x : Key → ℝ) : Integer.Sparse.eval row18864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18864, Integer.Sparse.eval_collectBalanced, rawRowCheck18864]

theorem rawRowCheck18865 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form3 = rawRow18865 := by decide +kernel

theorem rowCheck18865 : row18865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18865 := by decide +kernel

theorem rowEval18865 (x : Key → ℝ) : Integer.Sparse.eval row18865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18865, Integer.Sparse.eval_collectBalanced, rawRowCheck18865]

theorem rawRowCheck18866 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form3 = rawRow18866 := by decide +kernel

theorem rowCheck18866 : row18866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18866 := by decide +kernel

theorem rowEval18866 (x : Key → ℝ) : Integer.Sparse.eval row18866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18866, Integer.Sparse.eval_collectBalanced, rawRowCheck18866]

theorem rawRowCheck18867 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form3 = rawRow18867 := by decide +kernel

theorem rowCheck18867 : row18867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18867 := by decide +kernel

theorem rowEval18867 (x : Key → ℝ) : Integer.Sparse.eval row18867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18867, Integer.Sparse.eval_collectBalanced, rawRowCheck18867]

theorem rawRowCheck18868 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form3 = rawRow18868 := by decide +kernel

theorem rowCheck18868 : row18868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18868 := by decide +kernel

theorem rowEval18868 (x : Key → ℝ) : Integer.Sparse.eval row18868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18868, Integer.Sparse.eval_collectBalanced, rawRowCheck18868]

theorem rawRowCheck18869 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form3 = rawRow18869 := by decide +kernel

theorem rowCheck18869 : row18869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18869 := by decide +kernel

theorem rowEval18869 (x : Key → ℝ) : Integer.Sparse.eval row18869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18869, Integer.Sparse.eval_collectBalanced, rawRowCheck18869]

theorem rawRowCheck18870 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form3 = rawRow18870 := by decide +kernel

theorem rowCheck18870 : row18870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18870 := by decide +kernel

theorem rowEval18870 (x : Key → ℝ) : Integer.Sparse.eval row18870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18870, Integer.Sparse.eval_collectBalanced, rawRowCheck18870]

theorem rawRowCheck18871 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form3 = rawRow18871 := by decide +kernel

theorem rowCheck18871 : row18871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18871 := by decide +kernel

theorem rowEval18871 (x : Key → ℝ) : Integer.Sparse.eval row18871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18871, Integer.Sparse.eval_collectBalanced, rawRowCheck18871]

theorem rawRowCheck18872 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form3 = rawRow18872 := by decide +kernel

theorem rowCheck18872 : row18872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18872 := by decide +kernel

theorem rowEval18872 (x : Key → ℝ) : Integer.Sparse.eval row18872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18872, Integer.Sparse.eval_collectBalanced, rawRowCheck18872]

theorem rawRowCheck18873 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form3 = rawRow18873 := by decide +kernel

theorem rowCheck18873 : row18873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18873 := by decide +kernel

theorem rowEval18873 (x : Key → ℝ) : Integer.Sparse.eval row18873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18873, Integer.Sparse.eval_collectBalanced, rawRowCheck18873]

theorem rawRowCheck18874 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form3 = rawRow18874 := by decide +kernel

theorem rowCheck18874 : row18874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18874 := by decide +kernel

theorem rowEval18874 (x : Key → ℝ) : Integer.Sparse.eval row18874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18874, Integer.Sparse.eval_collectBalanced, rawRowCheck18874]

theorem rawRowCheck18875 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form3 = rawRow18875 := by decide +kernel

theorem rowCheck18875 : row18875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18875 := by decide +kernel

theorem rowEval18875 (x : Key → ℝ) : Integer.Sparse.eval row18875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18875, Integer.Sparse.eval_collectBalanced, rawRowCheck18875]

theorem rawRowCheck18876 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18876 := by decide +kernel

theorem rowCheck18876 : row18876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18876 := by decide +kernel

theorem rowEval18876 (x : Key → ℝ) : Integer.Sparse.eval row18876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18876, Integer.Sparse.eval_collectBalanced, rawRowCheck18876]

theorem rawRowCheck18877 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18877 := by decide +kernel

theorem rowCheck18877 : row18877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18877 := by decide +kernel

theorem rowEval18877 (x : Key → ℝ) : Integer.Sparse.eval row18877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18877, Integer.Sparse.eval_collectBalanced, rawRowCheck18877]

theorem rawRowCheck18878 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18878 := by decide +kernel

theorem rowCheck18878 : row18878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18878 := by decide +kernel

theorem rowEval18878 (x : Key → ℝ) : Integer.Sparse.eval row18878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18878, Integer.Sparse.eval_collectBalanced, rawRowCheck18878]

theorem rawRowCheck18879 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form4 = rawRow18879 := by decide +kernel

theorem rowCheck18879 : row18879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18879 := by decide +kernel

theorem rowEval18879 (x : Key → ℝ) : Integer.Sparse.eval row18879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18879, Integer.Sparse.eval_collectBalanced, rawRowCheck18879]

theorem rawRowCheck18880 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form4 = rawRow18880 := by decide +kernel

theorem rowCheck18880 : row18880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18880 := by decide +kernel

theorem rowEval18880 (x : Key → ℝ) : Integer.Sparse.eval row18880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18880, Integer.Sparse.eval_collectBalanced, rawRowCheck18880]

theorem rawRowCheck18881 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form4 = rawRow18881 := by decide +kernel

theorem rowCheck18881 : row18881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18881 := by decide +kernel

theorem rowEval18881 (x : Key → ℝ) : Integer.Sparse.eval row18881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18881, Integer.Sparse.eval_collectBalanced, rawRowCheck18881]

theorem rawRowCheck18882 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form4 = rawRow18882 := by decide +kernel

theorem rowCheck18882 : row18882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18882 := by decide +kernel

theorem rowEval18882 (x : Key → ℝ) : Integer.Sparse.eval row18882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18882, Integer.Sparse.eval_collectBalanced, rawRowCheck18882]

theorem rawRowCheck18883 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form4 = rawRow18883 := by decide +kernel

theorem rowCheck18883 : row18883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18883 := by decide +kernel

theorem rowEval18883 (x : Key → ℝ) : Integer.Sparse.eval row18883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18883, Integer.Sparse.eval_collectBalanced, rawRowCheck18883]

theorem rawRowCheck18884 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form4 = rawRow18884 := by decide +kernel

theorem rowCheck18884 : row18884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18884 := by decide +kernel

theorem rowEval18884 (x : Key → ℝ) : Integer.Sparse.eval row18884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18884, Integer.Sparse.eval_collectBalanced, rawRowCheck18884]

theorem rawRowCheck18885 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form4 = rawRow18885 := by decide +kernel

theorem rowCheck18885 : row18885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18885 := by decide +kernel

theorem rowEval18885 (x : Key → ℝ) : Integer.Sparse.eval row18885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18885, Integer.Sparse.eval_collectBalanced, rawRowCheck18885]

theorem rawRowCheck18886 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form4 = rawRow18886 := by decide +kernel

theorem rowCheck18886 : row18886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18886 := by decide +kernel

theorem rowEval18886 (x : Key → ℝ) : Integer.Sparse.eval row18886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18886, Integer.Sparse.eval_collectBalanced, rawRowCheck18886]

theorem rawRowCheck18887 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form4 = rawRow18887 := by decide +kernel

theorem rowCheck18887 : row18887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18887 := by decide +kernel

theorem rowEval18887 (x : Key → ℝ) : Integer.Sparse.eval row18887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18887, Integer.Sparse.eval_collectBalanced, rawRowCheck18887]

theorem rawRowCheck18888 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form4 = rawRow18888 := by decide +kernel

theorem rowCheck18888 : row18888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18888 := by decide +kernel

theorem rowEval18888 (x : Key → ℝ) : Integer.Sparse.eval row18888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18888, Integer.Sparse.eval_collectBalanced, rawRowCheck18888]

theorem rawRowCheck18889 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form4 = rawRow18889 := by decide +kernel

theorem rowCheck18889 : row18889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18889 := by decide +kernel

theorem rowEval18889 (x : Key → ℝ) : Integer.Sparse.eval row18889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18889, Integer.Sparse.eval_collectBalanced, rawRowCheck18889]

theorem rawRowCheck18890 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form4 = rawRow18890 := by decide +kernel

theorem rowCheck18890 : row18890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18890 := by decide +kernel

theorem rowEval18890 (x : Key → ℝ) : Integer.Sparse.eval row18890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18890, Integer.Sparse.eval_collectBalanced, rawRowCheck18890]

theorem rawRowCheck18891 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form4 = rawRow18891 := by decide +kernel

theorem rowCheck18891 : row18891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18891 := by decide +kernel

theorem rowEval18891 (x : Key → ℝ) : Integer.Sparse.eval row18891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18891, Integer.Sparse.eval_collectBalanced, rawRowCheck18891]

theorem rawRowCheck18892 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form4 = rawRow18892 := by decide +kernel

theorem rowCheck18892 : row18892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18892 := by decide +kernel

theorem rowEval18892 (x : Key → ℝ) : Integer.Sparse.eval row18892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18892, Integer.Sparse.eval_collectBalanced, rawRowCheck18892]

theorem rawRowCheck18893 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form4 = rawRow18893 := by decide +kernel

theorem rowCheck18893 : row18893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18893 := by decide +kernel

theorem rowEval18893 (x : Key → ℝ) : Integer.Sparse.eval row18893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18893, Integer.Sparse.eval_collectBalanced, rawRowCheck18893]

theorem rawRowCheck18894 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form4 = rawRow18894 := by decide +kernel

theorem rowCheck18894 : row18894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18894 := by decide +kernel

theorem rowEval18894 (x : Key → ℝ) : Integer.Sparse.eval row18894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18894, Integer.Sparse.eval_collectBalanced, rawRowCheck18894]

theorem rawRowCheck18895 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form4 = rawRow18895 := by decide +kernel

theorem rowCheck18895 : row18895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18895 := by decide +kernel

theorem rowEval18895 (x : Key → ℝ) : Integer.Sparse.eval row18895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18895, Integer.Sparse.eval_collectBalanced, rawRowCheck18895]

theorem rawRowCheck18896 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form4 = rawRow18896 := by decide +kernel

theorem rowCheck18896 : row18896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18896 := by decide +kernel

theorem rowEval18896 (x : Key → ℝ) : Integer.Sparse.eval row18896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18896, Integer.Sparse.eval_collectBalanced, rawRowCheck18896]

theorem rawRowCheck18897 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form4 = rawRow18897 := by decide +kernel

theorem rowCheck18897 : row18897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18897 := by decide +kernel

theorem rowEval18897 (x : Key → ℝ) : Integer.Sparse.eval row18897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18897, Integer.Sparse.eval_collectBalanced, rawRowCheck18897]

theorem rawRowCheck18898 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form4 = rawRow18898 := by decide +kernel

theorem rowCheck18898 : row18898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18898 := by decide +kernel

theorem rowEval18898 (x : Key → ℝ) : Integer.Sparse.eval row18898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18898, Integer.Sparse.eval_collectBalanced, rawRowCheck18898]

theorem rawRowCheck18899 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form4 = rawRow18899 := by decide +kernel

theorem rowCheck18899 : row18899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18899 := by decide +kernel

theorem rowEval18899 (x : Key → ℝ) : Integer.Sparse.eval row18899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18899, Integer.Sparse.eval_collectBalanced, rawRowCheck18899]

theorem rawRowCheck18900 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form4 = rawRow18900 := by decide +kernel

theorem rowCheck18900 : row18900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18900 := by decide +kernel

theorem rowEval18900 (x : Key → ℝ) : Integer.Sparse.eval row18900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18900, Integer.Sparse.eval_collectBalanced, rawRowCheck18900]

theorem rawRowCheck18901 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form4 = rawRow18901 := by decide +kernel

theorem rowCheck18901 : row18901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18901 := by decide +kernel

theorem rowEval18901 (x : Key → ℝ) : Integer.Sparse.eval row18901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18901, Integer.Sparse.eval_collectBalanced, rawRowCheck18901]

theorem rawRowCheck18902 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form4 = rawRow18902 := by decide +kernel

theorem rowCheck18902 : row18902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18902 := by decide +kernel

theorem rowEval18902 (x : Key → ℝ) : Integer.Sparse.eval row18902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18902, Integer.Sparse.eval_collectBalanced, rawRowCheck18902]

theorem rawRowCheck18903 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form4 = rawRow18903 := by decide +kernel

theorem rowCheck18903 : row18903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18903 := by decide +kernel

theorem rowEval18903 (x : Key → ℝ) : Integer.Sparse.eval row18903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18903, Integer.Sparse.eval_collectBalanced, rawRowCheck18903]

theorem rawRowCheck18904 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form4 = rawRow18904 := by decide +kernel

theorem rowCheck18904 : row18904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18904 := by decide +kernel

theorem rowEval18904 (x : Key → ℝ) : Integer.Sparse.eval row18904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18904, Integer.Sparse.eval_collectBalanced, rawRowCheck18904]

theorem rawRowCheck18905 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form4 = rawRow18905 := by decide +kernel

theorem rowCheck18905 : row18905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18905 := by decide +kernel

theorem rowEval18905 (x : Key → ℝ) : Integer.Sparse.eval row18905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18905, Integer.Sparse.eval_collectBalanced, rawRowCheck18905]

theorem rawRowCheck18906 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form4 = rawRow18906 := by decide +kernel

theorem rowCheck18906 : row18906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18906 := by decide +kernel

theorem rowEval18906 (x : Key → ℝ) : Integer.Sparse.eval row18906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18906, Integer.Sparse.eval_collectBalanced, rawRowCheck18906]

theorem rawRowCheck18907 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form4 = rawRow18907 := by decide +kernel

theorem rowCheck18907 : row18907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18907 := by decide +kernel

theorem rowEval18907 (x : Key → ℝ) : Integer.Sparse.eval row18907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18907, Integer.Sparse.eval_collectBalanced, rawRowCheck18907]

theorem rawRowCheck18908 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form4 = rawRow18908 := by decide +kernel

theorem rowCheck18908 : row18908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18908 := by decide +kernel

theorem rowEval18908 (x : Key → ℝ) : Integer.Sparse.eval row18908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18908, Integer.Sparse.eval_collectBalanced, rawRowCheck18908]

theorem rawRowCheck18909 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form5 = rawRow18909 := by decide +kernel

theorem rowCheck18909 : row18909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18909 := by decide +kernel

theorem rowEval18909 (x : Key → ℝ) : Integer.Sparse.eval row18909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18909, Integer.Sparse.eval_collectBalanced, rawRowCheck18909]

theorem rawRowCheck18910 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form5 = rawRow18910 := by decide +kernel

theorem rowCheck18910 : row18910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18910 := by decide +kernel

theorem rowEval18910 (x : Key → ℝ) : Integer.Sparse.eval row18910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18910, Integer.Sparse.eval_collectBalanced, rawRowCheck18910]

theorem rawRowCheck18911 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form5 = rawRow18911 := by decide +kernel

theorem rowCheck18911 : row18911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18911 := by decide +kernel

theorem rowEval18911 (x : Key → ℝ) : Integer.Sparse.eval row18911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18911, Integer.Sparse.eval_collectBalanced, rawRowCheck18911]

theorem rawRowCheck18912 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form5 = rawRow18912 := by decide +kernel

theorem rowCheck18912 : row18912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18912 := by decide +kernel

theorem rowEval18912 (x : Key → ℝ) : Integer.Sparse.eval row18912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18912, Integer.Sparse.eval_collectBalanced, rawRowCheck18912]

theorem rawRowCheck18913 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form5 = rawRow18913 := by decide +kernel

theorem rowCheck18913 : row18913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18913 := by decide +kernel

theorem rowEval18913 (x : Key → ℝ) : Integer.Sparse.eval row18913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18913, Integer.Sparse.eval_collectBalanced, rawRowCheck18913]

theorem rawRowCheck18914 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form5 = rawRow18914 := by decide +kernel

theorem rowCheck18914 : row18914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18914 := by decide +kernel

theorem rowEval18914 (x : Key → ℝ) : Integer.Sparse.eval row18914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18914, Integer.Sparse.eval_collectBalanced, rawRowCheck18914]

theorem rawRowCheck18915 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form5 = rawRow18915 := by decide +kernel

theorem rowCheck18915 : row18915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18915 := by decide +kernel

theorem rowEval18915 (x : Key → ℝ) : Integer.Sparse.eval row18915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18915, Integer.Sparse.eval_collectBalanced, rawRowCheck18915]

theorem rawRowCheck18916 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form5 = rawRow18916 := by decide +kernel

theorem rowCheck18916 : row18916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18916 := by decide +kernel

theorem rowEval18916 (x : Key → ℝ) : Integer.Sparse.eval row18916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18916, Integer.Sparse.eval_collectBalanced, rawRowCheck18916]

theorem rawRowCheck18917 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form5 = rawRow18917 := by decide +kernel

theorem rowCheck18917 : row18917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18917 := by decide +kernel

theorem rowEval18917 (x : Key → ℝ) : Integer.Sparse.eval row18917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18917, Integer.Sparse.eval_collectBalanced, rawRowCheck18917]

theorem rawRowCheck18918 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form5 = rawRow18918 := by decide +kernel

theorem rowCheck18918 : row18918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18918 := by decide +kernel

theorem rowEval18918 (x : Key → ℝ) : Integer.Sparse.eval row18918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18918, Integer.Sparse.eval_collectBalanced, rawRowCheck18918]

theorem rawRowCheck18919 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form5 = rawRow18919 := by decide +kernel

theorem rowCheck18919 : row18919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18919 := by decide +kernel

theorem rowEval18919 (x : Key → ℝ) : Integer.Sparse.eval row18919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18919, Integer.Sparse.eval_collectBalanced, rawRowCheck18919]

theorem rawRowCheck18920 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form5 = rawRow18920 := by decide +kernel

theorem rowCheck18920 : row18920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18920 := by decide +kernel

theorem rowEval18920 (x : Key → ℝ) : Integer.Sparse.eval row18920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18920, Integer.Sparse.eval_collectBalanced, rawRowCheck18920]

theorem rawRowCheck18921 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form5 = rawRow18921 := by decide +kernel

theorem rowCheck18921 : row18921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18921 := by decide +kernel

theorem rowEval18921 (x : Key → ℝ) : Integer.Sparse.eval row18921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18921, Integer.Sparse.eval_collectBalanced, rawRowCheck18921]

theorem rawRowCheck18922 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form5 = rawRow18922 := by decide +kernel

theorem rowCheck18922 : row18922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18922 := by decide +kernel

theorem rowEval18922 (x : Key → ℝ) : Integer.Sparse.eval row18922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18922, Integer.Sparse.eval_collectBalanced, rawRowCheck18922]

theorem rawRowCheck18923 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form5 = rawRow18923 := by decide +kernel

theorem rowCheck18923 : row18923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18923 := by decide +kernel

theorem rowEval18923 (x : Key → ℝ) : Integer.Sparse.eval row18923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18923, Integer.Sparse.eval_collectBalanced, rawRowCheck18923]

theorem rawRowCheck18924 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form5 = rawRow18924 := by decide +kernel

theorem rowCheck18924 : row18924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18924 := by decide +kernel

theorem rowEval18924 (x : Key → ℝ) : Integer.Sparse.eval row18924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18924, Integer.Sparse.eval_collectBalanced, rawRowCheck18924]

theorem rawRowCheck18925 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form5 = rawRow18925 := by decide +kernel

theorem rowCheck18925 : row18925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18925 := by decide +kernel

theorem rowEval18925 (x : Key → ℝ) : Integer.Sparse.eval row18925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18925, Integer.Sparse.eval_collectBalanced, rawRowCheck18925]

theorem rawRowCheck18926 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form5 = rawRow18926 := by decide +kernel

theorem rowCheck18926 : row18926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18926 := by decide +kernel

theorem rowEval18926 (x : Key → ℝ) : Integer.Sparse.eval row18926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18926, Integer.Sparse.eval_collectBalanced, rawRowCheck18926]

theorem rawRowCheck18927 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form5 = rawRow18927 := by decide +kernel

theorem rowCheck18927 : row18927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18927 := by decide +kernel

theorem rowEval18927 (x : Key → ℝ) : Integer.Sparse.eval row18927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18927, Integer.Sparse.eval_collectBalanced, rawRowCheck18927]

theorem rawRowCheck18928 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form5 = rawRow18928 := by decide +kernel

theorem rowCheck18928 : row18928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18928 := by decide +kernel

theorem rowEval18928 (x : Key → ℝ) : Integer.Sparse.eval row18928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18928, Integer.Sparse.eval_collectBalanced, rawRowCheck18928]

theorem rawRowCheck18929 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form5 = rawRow18929 := by decide +kernel

theorem rowCheck18929 : row18929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18929 := by decide +kernel

theorem rowEval18929 (x : Key → ℝ) : Integer.Sparse.eval row18929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18929, Integer.Sparse.eval_collectBalanced, rawRowCheck18929]

theorem rawRowCheck18930 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form5 = rawRow18930 := by decide +kernel

theorem rowCheck18930 : row18930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18930 := by decide +kernel

theorem rowEval18930 (x : Key → ℝ) : Integer.Sparse.eval row18930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18930, Integer.Sparse.eval_collectBalanced, rawRowCheck18930]

theorem rawRowCheck18931 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form5 = rawRow18931 := by decide +kernel

theorem rowCheck18931 : row18931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18931 := by decide +kernel

theorem rowEval18931 (x : Key → ℝ) : Integer.Sparse.eval row18931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18931, Integer.Sparse.eval_collectBalanced, rawRowCheck18931]

theorem rawRowCheck18932 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form5 = rawRow18932 := by decide +kernel

theorem rowCheck18932 : row18932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18932 := by decide +kernel

theorem rowEval18932 (x : Key → ℝ) : Integer.Sparse.eval row18932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18932, Integer.Sparse.eval_collectBalanced, rawRowCheck18932]

theorem rawRowCheck18933 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form5 = rawRow18933 := by decide +kernel

theorem rowCheck18933 : row18933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18933 := by decide +kernel

theorem rowEval18933 (x : Key → ℝ) : Integer.Sparse.eval row18933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18933, Integer.Sparse.eval_collectBalanced, rawRowCheck18933]

theorem rawRowCheck18934 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form5 = rawRow18934 := by decide +kernel

theorem rowCheck18934 : row18934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18934 := by decide +kernel

theorem rowEval18934 (x : Key → ℝ) : Integer.Sparse.eval row18934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18934, Integer.Sparse.eval_collectBalanced, rawRowCheck18934]

theorem rawRowCheck18935 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form5 = rawRow18935 := by decide +kernel

theorem rowCheck18935 : row18935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18935 := by decide +kernel

theorem rowEval18935 (x : Key → ℝ) : Integer.Sparse.eval row18935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18935, Integer.Sparse.eval_collectBalanced, rawRowCheck18935]

theorem rawRowCheck18936 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form5 = rawRow18936 := by decide +kernel

theorem rowCheck18936 : row18936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18936 := by decide +kernel

theorem rowEval18936 (x : Key → ℝ) : Integer.Sparse.eval row18936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18936, Integer.Sparse.eval_collectBalanced, rawRowCheck18936]

theorem rawRowCheck18937 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form5 = rawRow18937 := by decide +kernel

theorem rowCheck18937 : row18937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18937 := by decide +kernel

theorem rowEval18937 (x : Key → ℝ) : Integer.Sparse.eval row18937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18937, Integer.Sparse.eval_collectBalanced, rawRowCheck18937]

theorem rawRowCheck18938 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form5 = rawRow18938 := by decide +kernel

theorem rowCheck18938 : row18938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18938 := by decide +kernel

theorem rowEval18938 (x : Key → ℝ) : Integer.Sparse.eval row18938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18938, Integer.Sparse.eval_collectBalanced, rawRowCheck18938]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18759 x
  · exact rowEval18760 x
  · exact rowEval18761 x
  · exact rowEval18762 x
  · exact rowEval18763 x
  · exact rowEval18764 x
  · exact rowEval18765 x
  · exact rowEval18766 x
  · exact rowEval18767 x
  · exact rowEval18768 x
  · exact rowEval18769 x
  · exact rowEval18770 x
  · exact rowEval18771 x
  · exact rowEval18772 x
  · exact rowEval18773 x
  · exact rowEval18774 x
  · exact rowEval18775 x
  · exact rowEval18776 x
  · exact rowEval18777 x
  · exact rowEval18778 x
  · exact rowEval18779 x
  · exact rowEval18780 x
  · exact rowEval18781 x
  · exact rowEval18782 x
  · exact rowEval18783 x
  · exact rowEval18784 x
  · exact rowEval18785 x
  · exact rowEval18786 x
  · exact rowEval18787 x
  · exact rowEval18788 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18789 x
  · exact rowEval18790 x
  · exact rowEval18791 x
  · exact rowEval18792 x
  · exact rowEval18793 x
  · exact rowEval18794 x
  · exact rowEval18795 x
  · exact rowEval18796 x
  · exact rowEval18797 x
  · exact rowEval18798 x
  · exact rowEval18799 x
  · exact rowEval18800 x
  · exact rowEval18801 x
  · exact rowEval18802 x
  · exact rowEval18803 x
  · exact rowEval18804 x
  · exact rowEval18805 x
  · exact rowEval18806 x
  · exact rowEval18807 x
  · exact rowEval18808 x
  · exact rowEval18809 x
  · exact rowEval18810 x
  · exact rowEval18811 x
  · exact rowEval18812 x
  · exact rowEval18813 x
  · exact rowEval18814 x
  · exact rowEval18815 x
  · exact rowEval18816 x
  · exact rowEval18817 x
  · exact rowEval18818 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18849 x
  · exact rowEval18850 x
  · exact rowEval18851 x
  · exact rowEval18852 x
  · exact rowEval18853 x
  · exact rowEval18854 x
  · exact rowEval18855 x
  · exact rowEval18856 x
  · exact rowEval18857 x
  · exact rowEval18858 x
  · exact rowEval18859 x
  · exact rowEval18860 x
  · exact rowEval18861 x
  · exact rowEval18862 x
  · exact rowEval18863 x
  · exact rowEval18864 x
  · exact rowEval18865 x
  · exact rowEval18866 x
  · exact rowEval18867 x
  · exact rowEval18868 x
  · exact rowEval18869 x
  · exact rowEval18870 x
  · exact rowEval18871 x
  · exact rowEval18872 x
  · exact rowEval18873 x
  · exact rowEval18874 x
  · exact rowEval18875 x
  · exact rowEval18876 x
  · exact rowEval18877 x
  · exact rowEval18878 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval18879 x
  · exact rowEval18880 x
  · exact rowEval18881 x
  · exact rowEval18882 x
  · exact rowEval18883 x
  · exact rowEval18884 x
  · exact rowEval18885 x
  · exact rowEval18886 x
  · exact rowEval18887 x
  · exact rowEval18888 x
  · exact rowEval18889 x
  · exact rowEval18890 x
  · exact rowEval18891 x
  · exact rowEval18892 x
  · exact rowEval18893 x
  · exact rowEval18894 x
  · exact rowEval18895 x
  · exact rowEval18896 x
  · exact rowEval18897 x
  · exact rowEval18898 x
  · exact rowEval18899 x
  · exact rowEval18900 x
  · exact rowEval18901 x
  · exact rowEval18902 x
  · exact rowEval18903 x
  · exact rowEval18904 x
  · exact rowEval18905 x
  · exact rowEval18906 x
  · exact rowEval18907 x
  · exact rowEval18908 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

theorem entryCheck5_5 : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_5 k)) := by decide +kernel

theorem rowsSound5_5 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval18909 x
  · exact rowEval18910 x
  · exact rowEval18911 x
  · exact rowEval18912 x
  · exact rowEval18913 x
  · exact rowEval18914 x
  · exact rowEval18915 x
  · exact rowEval18916 x
  · exact rowEval18917 x
  · exact rowEval18918 x
  · exact rowEval18919 x
  · exact rowEval18920 x
  · exact rowEval18921 x
  · exact rowEval18922 x
  · exact rowEval18923 x
  · exact rowEval18924 x
  · exact rowEval18925 x
  · exact rowEval18926 x
  · exact rowEval18927 x
  · exact rowEval18928 x
  · exact rowEval18929 x
  · exact rowEval18930 x
  · exact rowEval18931 x
  · exact rowEval18932 x
  · exact rowEval18933 x
  · exact rowEval18934 x
  · exact rowEval18935 x
  · exact rowEval18936 x
  · exact rowEval18937 x
  · exact rowEval18938 x

theorem entryEval5_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_5 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck5_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_5]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19039 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form5 = rawRow19039 := by decide +kernel

theorem rowCheck19039 : row19039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19039 := by decide +kernel

theorem rowEval19039 (x : Key → ℝ) : Integer.Sparse.eval row19039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19039, Integer.Sparse.eval_collectBalanced, rawRowCheck19039]

theorem rawRowCheck19040 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form5 = rawRow19040 := by decide +kernel

theorem rowCheck19040 : row19040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19040 := by decide +kernel

theorem rowEval19040 (x : Key → ℝ) : Integer.Sparse.eval row19040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19040, Integer.Sparse.eval_collectBalanced, rawRowCheck19040]

theorem rawRowCheck19041 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form5 = rawRow19041 := by decide +kernel

theorem rowCheck19041 : row19041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19041 := by decide +kernel

theorem rowEval19041 (x : Key → ℝ) : Integer.Sparse.eval row19041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19041, Integer.Sparse.eval_collectBalanced, rawRowCheck19041]

theorem rawRowCheck19042 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19042 := by decide +kernel

theorem rowCheck19042 : row19042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19042 := by decide +kernel

theorem rowEval19042 (x : Key → ℝ) : Integer.Sparse.eval row19042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19042, Integer.Sparse.eval_collectBalanced, rawRowCheck19042]

theorem rawRowCheck19043 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form5 = rawRow19043 := by decide +kernel

theorem rowCheck19043 : row19043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19043 := by decide +kernel

theorem rowEval19043 (x : Key → ℝ) : Integer.Sparse.eval row19043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19043, Integer.Sparse.eval_collectBalanced, rawRowCheck19043]

theorem rawRowCheck19044 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form5 = rawRow19044 := by decide +kernel

theorem rowCheck19044 : row19044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19044 := by decide +kernel

theorem rowEval19044 (x : Key → ℝ) : Integer.Sparse.eval row19044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19044, Integer.Sparse.eval_collectBalanced, rawRowCheck19044]

theorem rawRowCheck19045 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form5 = rawRow19045 := by decide +kernel

theorem rowCheck19045 : row19045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19045 := by decide +kernel

theorem rowEval19045 (x : Key → ℝ) : Integer.Sparse.eval row19045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19045, Integer.Sparse.eval_collectBalanced, rawRowCheck19045]

theorem rawRowCheck19046 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form5 = rawRow19046 := by decide +kernel

theorem rowCheck19046 : row19046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19046 := by decide +kernel

theorem rowEval19046 (x : Key → ℝ) : Integer.Sparse.eval row19046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19046, Integer.Sparse.eval_collectBalanced, rawRowCheck19046]

theorem rawRowCheck19047 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form5 = rawRow19047 := by decide +kernel

theorem rowCheck19047 : row19047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19047 := by decide +kernel

theorem rowEval19047 (x : Key → ℝ) : Integer.Sparse.eval row19047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19047, Integer.Sparse.eval_collectBalanced, rawRowCheck19047]

theorem rawRowCheck19048 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form5 = rawRow19048 := by decide +kernel

theorem rowCheck19048 : row19048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19048 := by decide +kernel

theorem rowEval19048 (x : Key → ℝ) : Integer.Sparse.eval row19048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19048, Integer.Sparse.eval_collectBalanced, rawRowCheck19048]

theorem rawRowCheck19049 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form5 = rawRow19049 := by decide +kernel

theorem rowCheck19049 : row19049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19049 := by decide +kernel

theorem rowEval19049 (x : Key → ℝ) : Integer.Sparse.eval row19049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19049, Integer.Sparse.eval_collectBalanced, rawRowCheck19049]

theorem rawRowCheck19050 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form5 = rawRow19050 := by decide +kernel

theorem rowCheck19050 : row19050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19050 := by decide +kernel

theorem rowEval19050 (x : Key → ℝ) : Integer.Sparse.eval row19050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19050, Integer.Sparse.eval_collectBalanced, rawRowCheck19050]

theorem rawRowCheck19051 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form5 = rawRow19051 := by decide +kernel

theorem rowCheck19051 : row19051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19051 := by decide +kernel

theorem rowEval19051 (x : Key → ℝ) : Integer.Sparse.eval row19051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19051, Integer.Sparse.eval_collectBalanced, rawRowCheck19051]

theorem rawRowCheck19052 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form5 = rawRow19052 := by decide +kernel

theorem rowCheck19052 : row19052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19052 := by decide +kernel

theorem rowEval19052 (x : Key → ℝ) : Integer.Sparse.eval row19052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19052, Integer.Sparse.eval_collectBalanced, rawRowCheck19052]

theorem rawRowCheck19053 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form5 = rawRow19053 := by decide +kernel

theorem rowCheck19053 : row19053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19053 := by decide +kernel

theorem rowEval19053 (x : Key → ℝ) : Integer.Sparse.eval row19053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19053, Integer.Sparse.eval_collectBalanced, rawRowCheck19053]

theorem rawRowCheck19054 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form5 = rawRow19054 := by decide +kernel

theorem rowCheck19054 : row19054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19054 := by decide +kernel

theorem rowEval19054 (x : Key → ℝ) : Integer.Sparse.eval row19054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19054, Integer.Sparse.eval_collectBalanced, rawRowCheck19054]

theorem rawRowCheck19055 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19055 := by decide +kernel

theorem rowCheck19055 : row19055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19055 := by decide +kernel

theorem rowEval19055 (x : Key → ℝ) : Integer.Sparse.eval row19055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19055, Integer.Sparse.eval_collectBalanced, rawRowCheck19055]

theorem rawRowCheck19056 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form5 = rawRow19056 := by decide +kernel

theorem rowCheck19056 : row19056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19056 := by decide +kernel

theorem rowEval19056 (x : Key → ℝ) : Integer.Sparse.eval row19056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19056, Integer.Sparse.eval_collectBalanced, rawRowCheck19056]

theorem rawRowCheck19057 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form5 = rawRow19057 := by decide +kernel

theorem rowCheck19057 : row19057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19057 := by decide +kernel

theorem rowEval19057 (x : Key → ℝ) : Integer.Sparse.eval row19057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19057, Integer.Sparse.eval_collectBalanced, rawRowCheck19057]

theorem rawRowCheck19058 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form5 = rawRow19058 := by decide +kernel

theorem rowCheck19058 : row19058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19058 := by decide +kernel

theorem rowEval19058 (x : Key → ℝ) : Integer.Sparse.eval row19058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19058, Integer.Sparse.eval_collectBalanced, rawRowCheck19058]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19179 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19179 := by decide +kernel

theorem rowCheck19179 : row19179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19179 := by decide +kernel

theorem rowEval19179 (x : Key → ℝ) : Integer.Sparse.eval row19179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19179, Integer.Sparse.eval_collectBalanced, rawRowCheck19179]

theorem rawRowCheck19180 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19180 := by decide +kernel

theorem rowCheck19180 : row19180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19180 := by decide +kernel

theorem rowEval19180 (x : Key → ℝ) : Integer.Sparse.eval row19180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19180, Integer.Sparse.eval_collectBalanced, rawRowCheck19180]

theorem rawRowCheck19181 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19181 := by decide +kernel

theorem rowCheck19181 : row19181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19181 := by decide +kernel

theorem rowEval19181 (x : Key → ℝ) : Integer.Sparse.eval row19181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19181, Integer.Sparse.eval_collectBalanced, rawRowCheck19181]

theorem rawRowCheck19182 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19182 := by decide +kernel

theorem rowCheck19182 : row19182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19182 := by decide +kernel

theorem rowEval19182 (x : Key → ℝ) : Integer.Sparse.eval row19182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19182, Integer.Sparse.eval_collectBalanced, rawRowCheck19182]

theorem rawRowCheck19183 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19183 := by decide +kernel

theorem rowCheck19183 : row19183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19183 := by decide +kernel

theorem rowEval19183 (x : Key → ℝ) : Integer.Sparse.eval row19183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19183, Integer.Sparse.eval_collectBalanced, rawRowCheck19183]

theorem rawRowCheck19184 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19184 := by decide +kernel

theorem rowCheck19184 : row19184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19184 := by decide +kernel

theorem rowEval19184 (x : Key → ℝ) : Integer.Sparse.eval row19184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19184, Integer.Sparse.eval_collectBalanced, rawRowCheck19184]

theorem rawRowCheck19185 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19185 := by decide +kernel

theorem rowCheck19185 : row19185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19185 := by decide +kernel

theorem rowEval19185 (x : Key → ℝ) : Integer.Sparse.eval row19185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19185, Integer.Sparse.eval_collectBalanced, rawRowCheck19185]

theorem rawRowCheck19186 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19186 := by decide +kernel

theorem rowCheck19186 : row19186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19186 := by decide +kernel

theorem rowEval19186 (x : Key → ℝ) : Integer.Sparse.eval row19186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19186, Integer.Sparse.eval_collectBalanced, rawRowCheck19186]

theorem rawRowCheck19187 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19187 := by decide +kernel

theorem rowCheck19187 : row19187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19187 := by decide +kernel

theorem rowEval19187 (x : Key → ℝ) : Integer.Sparse.eval row19187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19187, Integer.Sparse.eval_collectBalanced, rawRowCheck19187]

theorem rawRowCheck19188 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19188 := by decide +kernel

theorem rowCheck19188 : row19188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19188 := by decide +kernel

theorem rowEval19188 (x : Key → ℝ) : Integer.Sparse.eval row19188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19188, Integer.Sparse.eval_collectBalanced, rawRowCheck19188]

theorem rawRowCheck19189 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19189 := by decide +kernel

theorem rowCheck19189 : row19189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19189 := by decide +kernel

theorem rowEval19189 (x : Key → ℝ) : Integer.Sparse.eval row19189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19189, Integer.Sparse.eval_collectBalanced, rawRowCheck19189]

theorem rawRowCheck19190 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19190 := by decide +kernel

theorem rowCheck19190 : row19190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19190 := by decide +kernel

theorem rowEval19190 (x : Key → ℝ) : Integer.Sparse.eval row19190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19190, Integer.Sparse.eval_collectBalanced, rawRowCheck19190]

theorem rawRowCheck19191 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19191 := by decide +kernel

theorem rowCheck19191 : row19191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19191 := by decide +kernel

theorem rowEval19191 (x : Key → ℝ) : Integer.Sparse.eval row19191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19191, Integer.Sparse.eval_collectBalanced, rawRowCheck19191]

theorem rawRowCheck19192 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19192 := by decide +kernel

theorem rowCheck19192 : row19192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19192 := by decide +kernel

theorem rowEval19192 (x : Key → ℝ) : Integer.Sparse.eval row19192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19192, Integer.Sparse.eval_collectBalanced, rawRowCheck19192]

theorem rawRowCheck19193 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form5 = rawRow19193 := by decide +kernel

theorem rowCheck19193 : row19193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19193 := by decide +kernel

theorem rowEval19193 (x : Key → ℝ) : Integer.Sparse.eval row19193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19193, Integer.Sparse.eval_collectBalanced, rawRowCheck19193]

theorem rawRowCheck19194 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form5 = rawRow19194 := by decide +kernel

theorem rowCheck19194 : row19194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19194 := by decide +kernel

theorem rowEval19194 (x : Key → ℝ) : Integer.Sparse.eval row19194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19194, Integer.Sparse.eval_collectBalanced, rawRowCheck19194]

theorem rawRowCheck19195 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form5 = rawRow19195 := by decide +kernel

theorem rowCheck19195 : row19195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19195 := by decide +kernel

theorem rowEval19195 (x : Key → ℝ) : Integer.Sparse.eval row19195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19195, Integer.Sparse.eval_collectBalanced, rawRowCheck19195]

theorem rawRowCheck19196 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form5 = rawRow19196 := by decide +kernel

theorem rowCheck19196 : row19196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19196 := by decide +kernel

theorem rowEval19196 (x : Key → ℝ) : Integer.Sparse.eval row19196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19196, Integer.Sparse.eval_collectBalanced, rawRowCheck19196]

theorem rawRowCheck19197 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form5 = rawRow19197 := by decide +kernel

theorem rowCheck19197 : row19197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19197 := by decide +kernel

theorem rowEval19197 (x : Key → ℝ) : Integer.Sparse.eval row19197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19197, Integer.Sparse.eval_collectBalanced, rawRowCheck19197]

theorem rawRowCheck19198 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form5 = rawRow19198 := by decide +kernel

theorem rowCheck19198 : row19198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19198 := by decide +kernel

theorem rowEval19198 (x : Key → ℝ) : Integer.Sparse.eval row19198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19198, Integer.Sparse.eval_collectBalanced, rawRowCheck19198]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck6_5 : entry6_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_5 k)) := by decide +kernel

theorem rowsSound6_5 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19039 x
  · exact rowEval19040 x
  · exact rowEval19041 x
  · exact rowEval19042 x
  · exact rowEval19043 x
  · exact rowEval19044 x
  · exact rowEval19045 x
  · exact rowEval19046 x
  · exact rowEval19047 x
  · exact rowEval19048 x
  · exact rowEval19049 x
  · exact rowEval19050 x
  · exact rowEval19051 x
  · exact rowEval19052 x
  · exact rowEval19053 x
  · exact rowEval19054 x
  · exact rowEval19055 x
  · exact rowEval19056 x
  · exact rowEval19057 x
  · exact rowEval19058 x

theorem entryEval6_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_5 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck6_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_5]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19264 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19264 := by decide +kernel

theorem rowCheck19264 : row19264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19264 := by decide +kernel

theorem rowEval19264 (x : Key → ℝ) : Integer.Sparse.eval row19264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19264, Integer.Sparse.eval_collectBalanced, rawRowCheck19264]

theorem rawRowCheck19265 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19265 := by decide +kernel

theorem rowCheck19265 : row19265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19265 := by decide +kernel

theorem rowEval19265 (x : Key → ℝ) : Integer.Sparse.eval row19265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19265, Integer.Sparse.eval_collectBalanced, rawRowCheck19265]

theorem rawRowCheck19266 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19266 := by decide +kernel

theorem rowCheck19266 : row19266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19266 := by decide +kernel

theorem rowEval19266 (x : Key → ℝ) : Integer.Sparse.eval row19266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19266, Integer.Sparse.eval_collectBalanced, rawRowCheck19266]

theorem rawRowCheck19267 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19267 := by decide +kernel

theorem rowCheck19267 : row19267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19267 := by decide +kernel

theorem rowEval19267 (x : Key → ℝ) : Integer.Sparse.eval row19267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19267, Integer.Sparse.eval_collectBalanced, rawRowCheck19267]

theorem rawRowCheck19268 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19268 := by decide +kernel

theorem rowCheck19268 : row19268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19268 := by decide +kernel

theorem rowEval19268 (x : Key → ℝ) : Integer.Sparse.eval row19268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19268, Integer.Sparse.eval_collectBalanced, rawRowCheck19268]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck7_5 : entry7_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_5 k)) := by decide +kernel

theorem rowsSound7_5 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19179 x
  · exact rowEval19180 x
  · exact rowEval19181 x
  · exact rowEval19182 x
  · exact rowEval19183 x
  · exact rowEval19184 x
  · exact rowEval19185 x
  · exact rowEval19186 x
  · exact rowEval19187 x
  · exact rowEval19188 x
  · exact rowEval19189 x
  · exact rowEval19190 x
  · exact rowEval19191 x
  · exact rowEval19192 x
  · exact rowEval19193 x
  · exact rowEval19194 x
  · exact rowEval19195 x
  · exact rowEval19196 x
  · exact rowEval19197 x
  · exact rowEval19198 x

theorem entryEval7_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_5 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck7_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_5]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19264 x
  · exact rowEval19265 x
  · exact rowEval19266 x
  · exact rowEval19267 x
  · exact rowEval19268 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19334 x
  · exact rowEval19335 x
  · exact rowEval19336 x
  · exact rowEval19337 x
  · exact rowEval19338 x
  · exact rowEval19339 x
  · exact rowEval19340 x
  · exact rowEval19341 x
  · exact rowEval19342 x
  · exact rowEval19343 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

theorem entryEvalRow5_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 5 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 5).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval5_0 B hB
  · exact entryEval5_1 B hB
  · exact entryEval5_2_e B hB
  · exact entryEval5_3 B hB
  · exact entryEval5_4 B hB
  · exact entryEval5_5 B hB
  · exact (entryEval6_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e_oai
