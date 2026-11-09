-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:50:06.527398+00:00
-- url     : https://prove2.me/submissions/4265566c-8ac3-4ba1-8e81-78c9868909b9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E038
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_10_e

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

theorem rawRowCheck19384 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19384 := by decide +kernel

theorem rowCheck19384 : row19384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19384 := by decide +kernel

theorem rowEval19384 (x : Key → ℝ) : Integer.Sparse.eval row19384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19384, Integer.Sparse.eval_collectBalanced, rawRowCheck19384]

theorem rawRowCheck19385 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19385 := by decide +kernel

theorem rowCheck19385 : row19385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19385 := by decide +kernel

theorem rowEval19385 (x : Key → ℝ) : Integer.Sparse.eval row19385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19385, Integer.Sparse.eval_collectBalanced, rawRowCheck19385]

theorem rawRowCheck19386 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19386 := by decide +kernel

theorem rowCheck19386 : row19386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19386 := by decide +kernel

theorem rowEval19386 (x : Key → ℝ) : Integer.Sparse.eval row19386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19386, Integer.Sparse.eval_collectBalanced, rawRowCheck19386]

theorem rawRowCheck19387 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19387 := by decide +kernel

theorem rowCheck19387 : row19387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19387 := by decide +kernel

theorem rowEval19387 (x : Key → ℝ) : Integer.Sparse.eval row19387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19387, Integer.Sparse.eval_collectBalanced, rawRowCheck19387]

theorem rawRowCheck19388 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19388 := by decide +kernel

theorem rowCheck19388 : row19388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19388 := by decide +kernel

theorem rowEval19388 (x : Key → ℝ) : Integer.Sparse.eval row19388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19388, Integer.Sparse.eval_collectBalanced, rawRowCheck19388]

theorem rawRowCheck19389 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19389 := by decide +kernel

theorem rowCheck19389 : row19389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19389 := by decide +kernel

theorem rowEval19389 (x : Key → ℝ) : Integer.Sparse.eval row19389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19389, Integer.Sparse.eval_collectBalanced, rawRowCheck19389]

theorem rawRowCheck19390 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19390 := by decide +kernel

theorem rowCheck19390 : row19390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19390 := by decide +kernel

theorem rowEval19390 (x : Key → ℝ) : Integer.Sparse.eval row19390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19390, Integer.Sparse.eval_collectBalanced, rawRowCheck19390]

theorem rawRowCheck19391 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19391 := by decide +kernel

theorem rowCheck19391 : row19391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19391 := by decide +kernel

theorem rowEval19391 (x : Key → ℝ) : Integer.Sparse.eval row19391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19391, Integer.Sparse.eval_collectBalanced, rawRowCheck19391]

theorem rawRowCheck19392 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19392 := by decide +kernel

theorem rowCheck19392 : row19392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19392 := by decide +kernel

theorem rowEval19392 (x : Key → ℝ) : Integer.Sparse.eval row19392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19392, Integer.Sparse.eval_collectBalanced, rawRowCheck19392]

theorem rawRowCheck19393 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19393 := by decide +kernel

theorem rowCheck19393 : row19393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19393 := by decide +kernel

theorem rowEval19393 (x : Key → ℝ) : Integer.Sparse.eval row19393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19393, Integer.Sparse.eval_collectBalanced, rawRowCheck19393]

theorem rawRowCheck19394 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19394 := by decide +kernel

theorem rowCheck19394 : row19394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19394 := by decide +kernel

theorem rowEval19394 (x : Key → ℝ) : Integer.Sparse.eval row19394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19394, Integer.Sparse.eval_collectBalanced, rawRowCheck19394]

theorem rawRowCheck19395 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19395 := by decide +kernel

theorem rowCheck19395 : row19395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19395 := by decide +kernel

theorem rowEval19395 (x : Key → ℝ) : Integer.Sparse.eval row19395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19395, Integer.Sparse.eval_collectBalanced, rawRowCheck19395]

theorem rawRowCheck19396 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19396 := by decide +kernel

theorem rowCheck19396 : row19396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19396 := by decide +kernel

theorem rowEval19396 (x : Key → ℝ) : Integer.Sparse.eval row19396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19396, Integer.Sparse.eval_collectBalanced, rawRowCheck19396]

theorem rawRowCheck19397 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19397 := by decide +kernel

theorem rowCheck19397 : row19397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19397 := by decide +kernel

theorem rowEval19397 (x : Key → ℝ) : Integer.Sparse.eval row19397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19397, Integer.Sparse.eval_collectBalanced, rawRowCheck19397]

theorem rawRowCheck19398 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19398 := by decide +kernel

theorem rowCheck19398 : row19398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19398 := by decide +kernel

theorem rowEval19398 (x : Key → ℝ) : Integer.Sparse.eval row19398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19398, Integer.Sparse.eval_collectBalanced, rawRowCheck19398]

theorem rawRowCheck19399 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19399 := by decide +kernel

theorem rowCheck19399 : row19399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19399 := by decide +kernel

theorem rowEval19399 (x : Key → ℝ) : Integer.Sparse.eval row19399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19399, Integer.Sparse.eval_collectBalanced, rawRowCheck19399]

theorem rawRowCheck19400 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19400 := by decide +kernel

theorem rowCheck19400 : row19400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19400 := by decide +kernel

theorem rowEval19400 (x : Key → ℝ) : Integer.Sparse.eval row19400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19400, Integer.Sparse.eval_collectBalanced, rawRowCheck19400]

theorem rawRowCheck19401 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19401 := by decide +kernel

theorem rowCheck19401 : row19401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19401 := by decide +kernel

theorem rowEval19401 (x : Key → ℝ) : Integer.Sparse.eval row19401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19401, Integer.Sparse.eval_collectBalanced, rawRowCheck19401]

theorem rawRowCheck19402 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19402 := by decide +kernel

theorem rowCheck19402 : row19402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19402 := by decide +kernel

theorem rowEval19402 (x : Key → ℝ) : Integer.Sparse.eval row19402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19402, Integer.Sparse.eval_collectBalanced, rawRowCheck19402]

theorem rawRowCheck19403 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19403 := by decide +kernel

theorem rowCheck19403 : row19403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19403 := by decide +kernel

theorem rowEval19403 (x : Key → ℝ) : Integer.Sparse.eval row19403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19403, Integer.Sparse.eval_collectBalanced, rawRowCheck19403]

theorem rawRowCheck19404 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19404 := by decide +kernel

theorem rowCheck19404 : row19404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19404 := by decide +kernel

theorem rowEval19404 (x : Key → ℝ) : Integer.Sparse.eval row19404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19404, Integer.Sparse.eval_collectBalanced, rawRowCheck19404]

theorem rawRowCheck19405 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19405 := by decide +kernel

theorem rowCheck19405 : row19405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19405 := by decide +kernel

theorem rowEval19405 (x : Key → ℝ) : Integer.Sparse.eval row19405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19405, Integer.Sparse.eval_collectBalanced, rawRowCheck19405]

theorem rawRowCheck19406 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19406 := by decide +kernel

theorem rowCheck19406 : row19406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19406 := by decide +kernel

theorem rowEval19406 (x : Key → ℝ) : Integer.Sparse.eval row19406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19406, Integer.Sparse.eval_collectBalanced, rawRowCheck19406]

theorem rawRowCheck19407 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19407 := by decide +kernel

theorem rowCheck19407 : row19407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19407 := by decide +kernel

theorem rowEval19407 (x : Key → ℝ) : Integer.Sparse.eval row19407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19407, Integer.Sparse.eval_collectBalanced, rawRowCheck19407]

theorem rawRowCheck19408 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19408 := by decide +kernel

theorem rowCheck19408 : row19408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19408 := by decide +kernel

theorem rowEval19408 (x : Key → ℝ) : Integer.Sparse.eval row19408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19408, Integer.Sparse.eval_collectBalanced, rawRowCheck19408]

theorem rawRowCheck19409 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19409 := by decide +kernel

theorem rowCheck19409 : row19409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19409 := by decide +kernel

theorem rowEval19409 (x : Key → ℝ) : Integer.Sparse.eval row19409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19409, Integer.Sparse.eval_collectBalanced, rawRowCheck19409]

theorem rawRowCheck19410 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19410 := by decide +kernel

theorem rowCheck19410 : row19410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19410 := by decide +kernel

theorem rowEval19410 (x : Key → ℝ) : Integer.Sparse.eval row19410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19410, Integer.Sparse.eval_collectBalanced, rawRowCheck19410]

theorem rawRowCheck19411 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form1 = rawRow19411 := by decide +kernel

theorem rowCheck19411 : row19411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19411 := by decide +kernel

theorem rowEval19411 (x : Key → ℝ) : Integer.Sparse.eval row19411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19411, Integer.Sparse.eval_collectBalanced, rawRowCheck19411]

theorem rawRowCheck19412 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form1 = rawRow19412 := by decide +kernel

theorem rowCheck19412 : row19412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19412 := by decide +kernel

theorem rowEval19412 (x : Key → ℝ) : Integer.Sparse.eval row19412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19412, Integer.Sparse.eval_collectBalanced, rawRowCheck19412]

theorem rawRowCheck19413 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form1 = rawRow19413 := by decide +kernel

theorem rowCheck19413 : row19413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19413 := by decide +kernel

theorem rowEval19413 (x : Key → ℝ) : Integer.Sparse.eval row19413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19413, Integer.Sparse.eval_collectBalanced, rawRowCheck19413]

theorem rawRowCheck19414 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form1 = rawRow19414 := by decide +kernel

theorem rowCheck19414 : row19414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19414 := by decide +kernel

theorem rowEval19414 (x : Key → ℝ) : Integer.Sparse.eval row19414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19414, Integer.Sparse.eval_collectBalanced, rawRowCheck19414]

theorem rawRowCheck19415 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form1 = rawRow19415 := by decide +kernel

theorem rowCheck19415 : row19415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19415 := by decide +kernel

theorem rowEval19415 (x : Key → ℝ) : Integer.Sparse.eval row19415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19415, Integer.Sparse.eval_collectBalanced, rawRowCheck19415]

theorem rawRowCheck19416 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form1 = rawRow19416 := by decide +kernel

theorem rowCheck19416 : row19416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19416 := by decide +kernel

theorem rowEval19416 (x : Key → ℝ) : Integer.Sparse.eval row19416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19416, Integer.Sparse.eval_collectBalanced, rawRowCheck19416]

theorem rawRowCheck19417 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19417 := by decide +kernel

theorem rowCheck19417 : row19417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19417 := by decide +kernel

theorem rowEval19417 (x : Key → ℝ) : Integer.Sparse.eval row19417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19417, Integer.Sparse.eval_collectBalanced, rawRowCheck19417]

theorem rawRowCheck19418 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19418 := by decide +kernel

theorem rowCheck19418 : row19418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19418 := by decide +kernel

theorem rowEval19418 (x : Key → ℝ) : Integer.Sparse.eval row19418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19418, Integer.Sparse.eval_collectBalanced, rawRowCheck19418]

theorem rawRowCheck19419 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19419 := by decide +kernel

theorem rowCheck19419 : row19419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19419 := by decide +kernel

theorem rowEval19419 (x : Key → ℝ) : Integer.Sparse.eval row19419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19419, Integer.Sparse.eval_collectBalanced, rawRowCheck19419]

theorem rawRowCheck19420 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19420 := by decide +kernel

theorem rowCheck19420 : row19420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19420 := by decide +kernel

theorem rowEval19420 (x : Key → ℝ) : Integer.Sparse.eval row19420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19420, Integer.Sparse.eval_collectBalanced, rawRowCheck19420]

theorem rawRowCheck19421 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19421 := by decide +kernel

theorem rowCheck19421 : row19421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19421 := by decide +kernel

theorem rowEval19421 (x : Key → ℝ) : Integer.Sparse.eval row19421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19421, Integer.Sparse.eval_collectBalanced, rawRowCheck19421]

theorem rawRowCheck19422 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19422 := by decide +kernel

theorem rowCheck19422 : row19422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19422 := by decide +kernel

theorem rowEval19422 (x : Key → ℝ) : Integer.Sparse.eval row19422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19422, Integer.Sparse.eval_collectBalanced, rawRowCheck19422]

theorem rawRowCheck19423 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19423 := by decide +kernel

theorem rowCheck19423 : row19423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19423 := by decide +kernel

theorem rowEval19423 (x : Key → ℝ) : Integer.Sparse.eval row19423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19423, Integer.Sparse.eval_collectBalanced, rawRowCheck19423]

theorem rawRowCheck19424 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form2 = rawRow19424 := by decide +kernel

theorem rowCheck19424 : row19424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19424 := by decide +kernel

theorem rowEval19424 (x : Key → ℝ) : Integer.Sparse.eval row19424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19424, Integer.Sparse.eval_collectBalanced, rawRowCheck19424]

theorem rawRowCheck19425 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form2 = rawRow19425 := by decide +kernel

theorem rowCheck19425 : row19425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19425 := by decide +kernel

theorem rowEval19425 (x : Key → ℝ) : Integer.Sparse.eval row19425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19425, Integer.Sparse.eval_collectBalanced, rawRowCheck19425]

theorem rawRowCheck19426 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form2 = rawRow19426 := by decide +kernel

theorem rowCheck19426 : row19426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19426 := by decide +kernel

theorem rowEval19426 (x : Key → ℝ) : Integer.Sparse.eval row19426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19426, Integer.Sparse.eval_collectBalanced, rawRowCheck19426]

theorem rawRowCheck19427 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19427 := by decide +kernel

theorem rowCheck19427 : row19427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19427 := by decide +kernel

theorem rowEval19427 (x : Key → ℝ) : Integer.Sparse.eval row19427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19427, Integer.Sparse.eval_collectBalanced, rawRowCheck19427]

theorem rawRowCheck19428 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form2 = rawRow19428 := by decide +kernel

theorem rowCheck19428 : row19428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19428 := by decide +kernel

theorem rowEval19428 (x : Key → ℝ) : Integer.Sparse.eval row19428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19428, Integer.Sparse.eval_collectBalanced, rawRowCheck19428]

theorem rawRowCheck19429 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form2 = rawRow19429 := by decide +kernel

theorem rowCheck19429 : row19429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19429 := by decide +kernel

theorem rowEval19429 (x : Key → ℝ) : Integer.Sparse.eval row19429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19429, Integer.Sparse.eval_collectBalanced, rawRowCheck19429]

theorem rawRowCheck19430 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form2 = rawRow19430 := by decide +kernel

theorem rowCheck19430 : row19430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19430 := by decide +kernel

theorem rowEval19430 (x : Key → ℝ) : Integer.Sparse.eval row19430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19430, Integer.Sparse.eval_collectBalanced, rawRowCheck19430]

theorem rawRowCheck19431 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form2 = rawRow19431 := by decide +kernel

theorem rowCheck19431 : row19431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19431 := by decide +kernel

theorem rowEval19431 (x : Key → ℝ) : Integer.Sparse.eval row19431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19431, Integer.Sparse.eval_collectBalanced, rawRowCheck19431]

theorem rawRowCheck19432 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form2 = rawRow19432 := by decide +kernel

theorem rowCheck19432 : row19432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19432 := by decide +kernel

theorem rowEval19432 (x : Key → ℝ) : Integer.Sparse.eval row19432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19432, Integer.Sparse.eval_collectBalanced, rawRowCheck19432]

theorem rawRowCheck19433 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form2 = rawRow19433 := by decide +kernel

theorem rowCheck19433 : row19433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19433 := by decide +kernel

theorem rowEval19433 (x : Key → ℝ) : Integer.Sparse.eval row19433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19433, Integer.Sparse.eval_collectBalanced, rawRowCheck19433]

theorem rawRowCheck19434 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form2 = rawRow19434 := by decide +kernel

theorem rowCheck19434 : row19434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19434 := by decide +kernel

theorem rowEval19434 (x : Key → ℝ) : Integer.Sparse.eval row19434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19434, Integer.Sparse.eval_collectBalanced, rawRowCheck19434]

theorem rawRowCheck19435 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form2 = rawRow19435 := by decide +kernel

theorem rowCheck19435 : row19435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19435 := by decide +kernel

theorem rowEval19435 (x : Key → ℝ) : Integer.Sparse.eval row19435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19435, Integer.Sparse.eval_collectBalanced, rawRowCheck19435]

theorem rawRowCheck19436 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form2 = rawRow19436 := by decide +kernel

theorem rowCheck19436 : row19436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19436 := by decide +kernel

theorem rowEval19436 (x : Key → ℝ) : Integer.Sparse.eval row19436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19436, Integer.Sparse.eval_collectBalanced, rawRowCheck19436]

theorem rawRowCheck19437 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19437 := by decide +kernel

theorem rowCheck19437 : row19437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19437 := by decide +kernel

theorem rowEval19437 (x : Key → ℝ) : Integer.Sparse.eval row19437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19437, Integer.Sparse.eval_collectBalanced, rawRowCheck19437]

theorem rawRowCheck19438 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19438 := by decide +kernel

theorem rowCheck19438 : row19438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19438 := by decide +kernel

theorem rowEval19438 (x : Key → ℝ) : Integer.Sparse.eval row19438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19438, Integer.Sparse.eval_collectBalanced, rawRowCheck19438]

theorem rawRowCheck19439 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19439 := by decide +kernel

theorem rowCheck19439 : row19439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19439 := by decide +kernel

theorem rowEval19439 (x : Key → ℝ) : Integer.Sparse.eval row19439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19439, Integer.Sparse.eval_collectBalanced, rawRowCheck19439]

theorem rawRowCheck19440 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19440 := by decide +kernel

theorem rowCheck19440 : row19440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19440 := by decide +kernel

theorem rowEval19440 (x : Key → ℝ) : Integer.Sparse.eval row19440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19440, Integer.Sparse.eval_collectBalanced, rawRowCheck19440]

theorem rawRowCheck19441 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19441 := by decide +kernel

theorem rowCheck19441 : row19441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19441 := by decide +kernel

theorem rowEval19441 (x : Key → ℝ) : Integer.Sparse.eval row19441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19441, Integer.Sparse.eval_collectBalanced, rawRowCheck19441]

theorem rawRowCheck19442 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19442 := by decide +kernel

theorem rowCheck19442 : row19442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19442 := by decide +kernel

theorem rowEval19442 (x : Key → ℝ) : Integer.Sparse.eval row19442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19442, Integer.Sparse.eval_collectBalanced, rawRowCheck19442]

theorem rawRowCheck19443 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19443 := by decide +kernel

theorem rowCheck19443 : row19443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19443 := by decide +kernel

theorem rowEval19443 (x : Key → ℝ) : Integer.Sparse.eval row19443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19443, Integer.Sparse.eval_collectBalanced, rawRowCheck19443]

theorem rawRowCheck19444 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19444 := by decide +kernel

theorem rowCheck19444 : row19444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19444 := by decide +kernel

theorem rowEval19444 (x : Key → ℝ) : Integer.Sparse.eval row19444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19444, Integer.Sparse.eval_collectBalanced, rawRowCheck19444]

theorem rawRowCheck19445 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19445 := by decide +kernel

theorem rowCheck19445 : row19445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19445 := by decide +kernel

theorem rowEval19445 (x : Key → ℝ) : Integer.Sparse.eval row19445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19445, Integer.Sparse.eval_collectBalanced, rawRowCheck19445]

theorem rawRowCheck19446 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19446 := by decide +kernel

theorem rowCheck19446 : row19446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19446 := by decide +kernel

theorem rowEval19446 (x : Key → ℝ) : Integer.Sparse.eval row19446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19446, Integer.Sparse.eval_collectBalanced, rawRowCheck19446]

theorem rawRowCheck19447 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19447 := by decide +kernel

theorem rowCheck19447 : row19447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19447 := by decide +kernel

theorem rowEval19447 (x : Key → ℝ) : Integer.Sparse.eval row19447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19447, Integer.Sparse.eval_collectBalanced, rawRowCheck19447]

theorem rawRowCheck19448 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19448 := by decide +kernel

theorem rowCheck19448 : row19448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19448 := by decide +kernel

theorem rowEval19448 (x : Key → ℝ) : Integer.Sparse.eval row19448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19448, Integer.Sparse.eval_collectBalanced, rawRowCheck19448]

theorem rawRowCheck19449 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19449 := by decide +kernel

theorem rowCheck19449 : row19449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19449 := by decide +kernel

theorem rowEval19449 (x : Key → ℝ) : Integer.Sparse.eval row19449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19449, Integer.Sparse.eval_collectBalanced, rawRowCheck19449]

theorem rawRowCheck19450 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19450 := by decide +kernel

theorem rowCheck19450 : row19450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19450 := by decide +kernel

theorem rowEval19450 (x : Key → ℝ) : Integer.Sparse.eval row19450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19450, Integer.Sparse.eval_collectBalanced, rawRowCheck19450]

theorem rawRowCheck19451 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form3 = rawRow19451 := by decide +kernel

theorem rowCheck19451 : row19451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19451 := by decide +kernel

theorem rowEval19451 (x : Key → ℝ) : Integer.Sparse.eval row19451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19451, Integer.Sparse.eval_collectBalanced, rawRowCheck19451]

theorem rawRowCheck19452 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form3 = rawRow19452 := by decide +kernel

theorem rowCheck19452 : row19452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19452 := by decide +kernel

theorem rowEval19452 (x : Key → ℝ) : Integer.Sparse.eval row19452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19452, Integer.Sparse.eval_collectBalanced, rawRowCheck19452]

theorem rawRowCheck19453 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form3 = rawRow19453 := by decide +kernel

theorem rowCheck19453 : row19453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19453 := by decide +kernel

theorem rowEval19453 (x : Key → ℝ) : Integer.Sparse.eval row19453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19453, Integer.Sparse.eval_collectBalanced, rawRowCheck19453]

theorem rawRowCheck19454 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form3 = rawRow19454 := by decide +kernel

theorem rowCheck19454 : row19454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19454 := by decide +kernel

theorem rowEval19454 (x : Key → ℝ) : Integer.Sparse.eval row19454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19454, Integer.Sparse.eval_collectBalanced, rawRowCheck19454]

theorem rawRowCheck19455 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form3 = rawRow19455 := by decide +kernel

theorem rowCheck19455 : row19455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19455 := by decide +kernel

theorem rowEval19455 (x : Key → ℝ) : Integer.Sparse.eval row19455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19455, Integer.Sparse.eval_collectBalanced, rawRowCheck19455]

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

theorem rawRowCheck19456 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form3 = rawRow19456 := by decide +kernel

theorem rowCheck19456 : row19456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19456 := by decide +kernel

theorem rowEval19456 (x : Key → ℝ) : Integer.Sparse.eval row19456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19456, Integer.Sparse.eval_collectBalanced, rawRowCheck19456]

theorem rawRowCheck19457 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19457 := by decide +kernel

theorem rowCheck19457 : row19457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19457 := by decide +kernel

theorem rowEval19457 (x : Key → ℝ) : Integer.Sparse.eval row19457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19457, Integer.Sparse.eval_collectBalanced, rawRowCheck19457]

theorem rawRowCheck19458 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19458 := by decide +kernel

theorem rowCheck19458 : row19458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19458 := by decide +kernel

theorem rowEval19458 (x : Key → ℝ) : Integer.Sparse.eval row19458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19458, Integer.Sparse.eval_collectBalanced, rawRowCheck19458]

theorem rawRowCheck19459 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19459 := by decide +kernel

theorem rowCheck19459 : row19459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19459 := by decide +kernel

theorem rowEval19459 (x : Key → ℝ) : Integer.Sparse.eval row19459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19459, Integer.Sparse.eval_collectBalanced, rawRowCheck19459]

theorem rawRowCheck19460 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19460 := by decide +kernel

theorem rowCheck19460 : row19460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19460 := by decide +kernel

theorem rowEval19460 (x : Key → ℝ) : Integer.Sparse.eval row19460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19460, Integer.Sparse.eval_collectBalanced, rawRowCheck19460]

theorem rawRowCheck19461 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19461 := by decide +kernel

theorem rowCheck19461 : row19461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19461 := by decide +kernel

theorem rowEval19461 (x : Key → ℝ) : Integer.Sparse.eval row19461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19461, Integer.Sparse.eval_collectBalanced, rawRowCheck19461]

theorem rawRowCheck19462 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19462 := by decide +kernel

theorem rowCheck19462 : row19462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19462 := by decide +kernel

theorem rowEval19462 (x : Key → ℝ) : Integer.Sparse.eval row19462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19462, Integer.Sparse.eval_collectBalanced, rawRowCheck19462]

theorem rawRowCheck19463 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19463 := by decide +kernel

theorem rowCheck19463 : row19463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19463 := by decide +kernel

theorem rowEval19463 (x : Key → ℝ) : Integer.Sparse.eval row19463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19463, Integer.Sparse.eval_collectBalanced, rawRowCheck19463]

theorem rawRowCheck19464 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19464 := by decide +kernel

theorem rowCheck19464 : row19464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19464 := by decide +kernel

theorem rowEval19464 (x : Key → ℝ) : Integer.Sparse.eval row19464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19464, Integer.Sparse.eval_collectBalanced, rawRowCheck19464]

theorem rawRowCheck19465 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19465 := by decide +kernel

theorem rowCheck19465 : row19465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19465 := by decide +kernel

theorem rowEval19465 (x : Key → ℝ) : Integer.Sparse.eval row19465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19465, Integer.Sparse.eval_collectBalanced, rawRowCheck19465]

theorem rawRowCheck19466 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19466 := by decide +kernel

theorem rowCheck19466 : row19466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19466 := by decide +kernel

theorem rowEval19466 (x : Key → ℝ) : Integer.Sparse.eval row19466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19466, Integer.Sparse.eval_collectBalanced, rawRowCheck19466]

theorem rawRowCheck19467 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19467 := by decide +kernel

theorem rowCheck19467 : row19467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19467 := by decide +kernel

theorem rowEval19467 (x : Key → ℝ) : Integer.Sparse.eval row19467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19467, Integer.Sparse.eval_collectBalanced, rawRowCheck19467]

theorem rawRowCheck19468 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19468 := by decide +kernel

theorem rowCheck19468 : row19468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19468 := by decide +kernel

theorem rowEval19468 (x : Key → ℝ) : Integer.Sparse.eval row19468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19468, Integer.Sparse.eval_collectBalanced, rawRowCheck19468]

theorem rawRowCheck19469 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19469 := by decide +kernel

theorem rowCheck19469 : row19469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19469 := by decide +kernel

theorem rowEval19469 (x : Key → ℝ) : Integer.Sparse.eval row19469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19469, Integer.Sparse.eval_collectBalanced, rawRowCheck19469]

theorem rawRowCheck19470 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19470 := by decide +kernel

theorem rowCheck19470 : row19470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19470 := by decide +kernel

theorem rowEval19470 (x : Key → ℝ) : Integer.Sparse.eval row19470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19470, Integer.Sparse.eval_collectBalanced, rawRowCheck19470]

theorem rawRowCheck19471 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form4 = rawRow19471 := by decide +kernel

theorem rowCheck19471 : row19471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19471 := by decide +kernel

theorem rowEval19471 (x : Key → ℝ) : Integer.Sparse.eval row19471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19471, Integer.Sparse.eval_collectBalanced, rawRowCheck19471]

theorem rawRowCheck19472 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form4 = rawRow19472 := by decide +kernel

theorem rowCheck19472 : row19472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19472 := by decide +kernel

theorem rowEval19472 (x : Key → ℝ) : Integer.Sparse.eval row19472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19472, Integer.Sparse.eval_collectBalanced, rawRowCheck19472]

theorem rawRowCheck19473 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form4 = rawRow19473 := by decide +kernel

theorem rowCheck19473 : row19473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19473 := by decide +kernel

theorem rowEval19473 (x : Key → ℝ) : Integer.Sparse.eval row19473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19473, Integer.Sparse.eval_collectBalanced, rawRowCheck19473]

theorem rawRowCheck19474 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form4 = rawRow19474 := by decide +kernel

theorem rowCheck19474 : row19474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19474 := by decide +kernel

theorem rowEval19474 (x : Key → ℝ) : Integer.Sparse.eval row19474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19474, Integer.Sparse.eval_collectBalanced, rawRowCheck19474]

theorem rawRowCheck19475 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form4 = rawRow19475 := by decide +kernel

theorem rowCheck19475 : row19475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19475 := by decide +kernel

theorem rowEval19475 (x : Key → ℝ) : Integer.Sparse.eval row19475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19475, Integer.Sparse.eval_collectBalanced, rawRowCheck19475]

theorem rawRowCheck19476 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form4 = rawRow19476 := by decide +kernel

theorem rowCheck19476 : row19476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19476 := by decide +kernel

theorem rowEval19476 (x : Key → ℝ) : Integer.Sparse.eval row19476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19476, Integer.Sparse.eval_collectBalanced, rawRowCheck19476]

theorem rawRowCheck19477 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19477 := by decide +kernel

theorem rowCheck19477 : row19477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19477 := by decide +kernel

theorem rowEval19477 (x : Key → ℝ) : Integer.Sparse.eval row19477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19477, Integer.Sparse.eval_collectBalanced, rawRowCheck19477]

theorem rawRowCheck19478 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19478 := by decide +kernel

theorem rowCheck19478 : row19478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19478 := by decide +kernel

theorem rowEval19478 (x : Key → ℝ) : Integer.Sparse.eval row19478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19478, Integer.Sparse.eval_collectBalanced, rawRowCheck19478]

theorem rawRowCheck19479 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19479 := by decide +kernel

theorem rowCheck19479 : row19479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19479 := by decide +kernel

theorem rowEval19479 (x : Key → ℝ) : Integer.Sparse.eval row19479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19479, Integer.Sparse.eval_collectBalanced, rawRowCheck19479]

theorem rawRowCheck19480 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19480 := by decide +kernel

theorem rowCheck19480 : row19480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19480 := by decide +kernel

theorem rowEval19480 (x : Key → ℝ) : Integer.Sparse.eval row19480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19480, Integer.Sparse.eval_collectBalanced, rawRowCheck19480]

theorem rawRowCheck19481 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19481 := by decide +kernel

theorem rowCheck19481 : row19481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19481 := by decide +kernel

theorem rowEval19481 (x : Key → ℝ) : Integer.Sparse.eval row19481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19481, Integer.Sparse.eval_collectBalanced, rawRowCheck19481]

theorem rawRowCheck19482 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19482 := by decide +kernel

theorem rowCheck19482 : row19482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19482 := by decide +kernel

theorem rowEval19482 (x : Key → ℝ) : Integer.Sparse.eval row19482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19482, Integer.Sparse.eval_collectBalanced, rawRowCheck19482]

theorem rawRowCheck19483 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19483 := by decide +kernel

theorem rowCheck19483 : row19483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19483 := by decide +kernel

theorem rowEval19483 (x : Key → ℝ) : Integer.Sparse.eval row19483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19483, Integer.Sparse.eval_collectBalanced, rawRowCheck19483]

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

theorem rawRowCheck19504 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19504 := by decide +kernel

theorem rowCheck19504 : row19504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19504 := by decide +kernel

theorem rowEval19504 (x : Key → ℝ) : Integer.Sparse.eval row19504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19504, Integer.Sparse.eval_collectBalanced, rawRowCheck19504]

theorem rawRowCheck19505 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19505 := by decide +kernel

theorem rowCheck19505 : row19505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19505 := by decide +kernel

theorem rowEval19505 (x : Key → ℝ) : Integer.Sparse.eval row19505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19505, Integer.Sparse.eval_collectBalanced, rawRowCheck19505]

theorem rawRowCheck19506 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19506 := by decide +kernel

theorem rowCheck19506 : row19506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19506 := by decide +kernel

theorem rowEval19506 (x : Key → ℝ) : Integer.Sparse.eval row19506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19506, Integer.Sparse.eval_collectBalanced, rawRowCheck19506]

theorem rawRowCheck19507 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19507 := by decide +kernel

theorem rowCheck19507 : row19507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19507 := by decide +kernel

theorem rowEval19507 (x : Key → ℝ) : Integer.Sparse.eval row19507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19507, Integer.Sparse.eval_collectBalanced, rawRowCheck19507]

theorem rawRowCheck19508 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19508 := by decide +kernel

theorem rowCheck19508 : row19508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19508 := by decide +kernel

theorem rowEval19508 (x : Key → ℝ) : Integer.Sparse.eval row19508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19508, Integer.Sparse.eval_collectBalanced, rawRowCheck19508]

theorem rawRowCheck19509 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19509 := by decide +kernel

theorem rowCheck19509 : row19509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19509 := by decide +kernel

theorem rowEval19509 (x : Key → ℝ) : Integer.Sparse.eval row19509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19509, Integer.Sparse.eval_collectBalanced, rawRowCheck19509]

theorem rawRowCheck19510 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19510 := by decide +kernel

theorem rowCheck19510 : row19510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19510 := by decide +kernel

theorem rowEval19510 (x : Key → ℝ) : Integer.Sparse.eval row19510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19510, Integer.Sparse.eval_collectBalanced, rawRowCheck19510]

theorem rawRowCheck19511 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form6 = rawRow19511 := by decide +kernel

theorem rowCheck19511 : row19511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19511 := by decide +kernel

theorem rowEval19511 (x : Key → ℝ) : Integer.Sparse.eval row19511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19511, Integer.Sparse.eval_collectBalanced, rawRowCheck19511]

theorem rawRowCheck19512 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form6 = rawRow19512 := by decide +kernel

theorem rowCheck19512 : row19512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19512 := by decide +kernel

theorem rowEval19512 (x : Key → ℝ) : Integer.Sparse.eval row19512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19512, Integer.Sparse.eval_collectBalanced, rawRowCheck19512]

theorem rawRowCheck19513 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form6 = rawRow19513 := by decide +kernel

theorem rowCheck19513 : row19513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19513 := by decide +kernel

theorem rowEval19513 (x : Key → ℝ) : Integer.Sparse.eval row19513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19513, Integer.Sparse.eval_collectBalanced, rawRowCheck19513]

theorem rawRowCheck19514 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form6 = rawRow19514 := by decide +kernel

theorem rowCheck19514 : row19514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19514 := by decide +kernel

theorem rowEval19514 (x : Key → ℝ) : Integer.Sparse.eval row19514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19514, Integer.Sparse.eval_collectBalanced, rawRowCheck19514]

theorem rawRowCheck19515 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form6 = rawRow19515 := by decide +kernel

theorem rowCheck19515 : row19515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19515 := by decide +kernel

theorem rowEval19515 (x : Key → ℝ) : Integer.Sparse.eval row19515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19515, Integer.Sparse.eval_collectBalanced, rawRowCheck19515]

theorem rawRowCheck19516 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form6 = rawRow19516 := by decide +kernel

theorem rowCheck19516 : row19516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19516 := by decide +kernel

theorem rowEval19516 (x : Key → ℝ) : Integer.Sparse.eval row19516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19516, Integer.Sparse.eval_collectBalanced, rawRowCheck19516]

theorem rawRowCheck19517 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19517 := by decide +kernel

theorem rowCheck19517 : row19517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19517 := by decide +kernel

theorem rowEval19517 (x : Key → ℝ) : Integer.Sparse.eval row19517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19517, Integer.Sparse.eval_collectBalanced, rawRowCheck19517]

theorem rawRowCheck19518 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19518 := by decide +kernel

theorem rowCheck19518 : row19518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19518 := by decide +kernel

theorem rowEval19518 (x : Key → ℝ) : Integer.Sparse.eval row19518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19518, Integer.Sparse.eval_collectBalanced, rawRowCheck19518]

theorem rawRowCheck19519 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19519 := by decide +kernel

theorem rowCheck19519 : row19519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19519 := by decide +kernel

theorem rowEval19519 (x : Key → ℝ) : Integer.Sparse.eval row19519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19519, Integer.Sparse.eval_collectBalanced, rawRowCheck19519]

theorem rawRowCheck19520 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19520 := by decide +kernel

theorem rowCheck19520 : row19520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19520 := by decide +kernel

theorem rowEval19520 (x : Key → ℝ) : Integer.Sparse.eval row19520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19520, Integer.Sparse.eval_collectBalanced, rawRowCheck19520]

theorem rawRowCheck19521 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19521 := by decide +kernel

theorem rowCheck19521 : row19521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19521 := by decide +kernel

theorem rowEval19521 (x : Key → ℝ) : Integer.Sparse.eval row19521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19521, Integer.Sparse.eval_collectBalanced, rawRowCheck19521]

theorem rawRowCheck19522 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19522 := by decide +kernel

theorem rowCheck19522 : row19522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19522 := by decide +kernel

theorem rowEval19522 (x : Key → ℝ) : Integer.Sparse.eval row19522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19522, Integer.Sparse.eval_collectBalanced, rawRowCheck19522]

theorem rawRowCheck19523 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19523 := by decide +kernel

theorem rowCheck19523 : row19523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19523 := by decide +kernel

theorem rowEval19523 (x : Key → ℝ) : Integer.Sparse.eval row19523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19523, Integer.Sparse.eval_collectBalanced, rawRowCheck19523]

theorem rawRowCheck19524 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form7 = rawRow19524 := by decide +kernel

theorem rowCheck19524 : row19524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19524 := by decide +kernel

theorem rowEval19524 (x : Key → ℝ) : Integer.Sparse.eval row19524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19524, Integer.Sparse.eval_collectBalanced, rawRowCheck19524]

theorem rawRowCheck19525 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form7 = rawRow19525 := by decide +kernel

theorem rowCheck19525 : row19525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19525 := by decide +kernel

theorem rowEval19525 (x : Key → ℝ) : Integer.Sparse.eval row19525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19525, Integer.Sparse.eval_collectBalanced, rawRowCheck19525]

theorem rawRowCheck19526 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form7 = rawRow19526 := by decide +kernel

theorem rowCheck19526 : row19526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19526 := by decide +kernel

theorem rowEval19526 (x : Key → ℝ) : Integer.Sparse.eval row19526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19526, Integer.Sparse.eval_collectBalanced, rawRowCheck19526]

theorem rawRowCheck19527 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19527 := by decide +kernel

theorem rowCheck19527 : row19527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19527 := by decide +kernel

theorem rowEval19527 (x : Key → ℝ) : Integer.Sparse.eval row19527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19527, Integer.Sparse.eval_collectBalanced, rawRowCheck19527]

theorem rawRowCheck19528 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form7 = rawRow19528 := by decide +kernel

theorem rowCheck19528 : row19528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19528 := by decide +kernel

theorem rowEval19528 (x : Key → ℝ) : Integer.Sparse.eval row19528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19528, Integer.Sparse.eval_collectBalanced, rawRowCheck19528]

theorem rawRowCheck19529 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form7 = rawRow19529 := by decide +kernel

theorem rowCheck19529 : row19529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19529 := by decide +kernel

theorem rowEval19529 (x : Key → ℝ) : Integer.Sparse.eval row19529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19529, Integer.Sparse.eval_collectBalanced, rawRowCheck19529]

theorem rawRowCheck19530 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form7 = rawRow19530 := by decide +kernel

theorem rowCheck19530 : row19530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19530 := by decide +kernel

theorem rowEval19530 (x : Key → ℝ) : Integer.Sparse.eval row19530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19530, Integer.Sparse.eval_collectBalanced, rawRowCheck19530]

theorem rawRowCheck19531 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form7 = rawRow19531 := by decide +kernel

theorem rowCheck19531 : row19531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19531 := by decide +kernel

theorem rowEval19531 (x : Key → ℝ) : Integer.Sparse.eval row19531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19531, Integer.Sparse.eval_collectBalanced, rawRowCheck19531]

theorem rawRowCheck19532 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form7 = rawRow19532 := by decide +kernel

theorem rowCheck19532 : row19532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19532 := by decide +kernel

theorem rowEval19532 (x : Key → ℝ) : Integer.Sparse.eval row19532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19532, Integer.Sparse.eval_collectBalanced, rawRowCheck19532]

theorem rawRowCheck19533 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form7 = rawRow19533 := by decide +kernel

theorem rowCheck19533 : row19533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19533 := by decide +kernel

theorem rowEval19533 (x : Key → ℝ) : Integer.Sparse.eval row19533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19533, Integer.Sparse.eval_collectBalanced, rawRowCheck19533]

theorem rawRowCheck19534 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form7 = rawRow19534 := by decide +kernel

theorem rowCheck19534 : row19534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19534 := by decide +kernel

theorem rowEval19534 (x : Key → ℝ) : Integer.Sparse.eval row19534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19534, Integer.Sparse.eval_collectBalanced, rawRowCheck19534]

theorem rawRowCheck19535 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form7 = rawRow19535 := by decide +kernel

theorem rowCheck19535 : row19535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19535 := by decide +kernel

theorem rowEval19535 (x : Key → ℝ) : Integer.Sparse.eval row19535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19535, Integer.Sparse.eval_collectBalanced, rawRowCheck19535]

theorem rawRowCheck19536 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form7 = rawRow19536 := by decide +kernel

theorem rowCheck19536 : row19536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19536 := by decide +kernel

theorem rowEval19536 (x : Key → ℝ) : Integer.Sparse.eval row19536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19536, Integer.Sparse.eval_collectBalanced, rawRowCheck19536]

theorem rawRowCheck19537 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form7 = rawRow19537 := by decide +kernel

theorem rowCheck19537 : row19537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19537 := by decide +kernel

theorem rowEval19537 (x : Key → ℝ) : Integer.Sparse.eval row19537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19537, Integer.Sparse.eval_collectBalanced, rawRowCheck19537]

theorem rawRowCheck19538 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form7 = rawRow19538 := by decide +kernel

theorem rowCheck19538 : row19538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19538 := by decide +kernel

theorem rowEval19538 (x : Key → ℝ) : Integer.Sparse.eval row19538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19538, Integer.Sparse.eval_collectBalanced, rawRowCheck19538]

theorem rawRowCheck19539 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form7 = rawRow19539 := by decide +kernel

theorem rowCheck19539 : row19539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19539 := by decide +kernel

theorem rowEval19539 (x : Key → ℝ) : Integer.Sparse.eval row19539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19539, Integer.Sparse.eval_collectBalanced, rawRowCheck19539]

theorem rawRowCheck19540 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19540 := by decide +kernel

theorem rowCheck19540 : row19540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19540 := by decide +kernel

theorem rowEval19540 (x : Key → ℝ) : Integer.Sparse.eval row19540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19540, Integer.Sparse.eval_collectBalanced, rawRowCheck19540]

theorem rawRowCheck19541 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form7 = rawRow19541 := by decide +kernel

theorem rowCheck19541 : row19541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19541 := by decide +kernel

theorem rowEval19541 (x : Key → ℝ) : Integer.Sparse.eval row19541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19541, Integer.Sparse.eval_collectBalanced, rawRowCheck19541]

theorem rawRowCheck19542 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form7 = rawRow19542 := by decide +kernel

theorem rowCheck19542 : row19542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19542 := by decide +kernel

theorem rowEval19542 (x : Key → ℝ) : Integer.Sparse.eval row19542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19542, Integer.Sparse.eval_collectBalanced, rawRowCheck19542]

theorem rawRowCheck19543 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form7 = rawRow19543 := by decide +kernel

theorem rowCheck19543 : row19543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19543 := by decide +kernel

theorem rowEval19543 (x : Key → ℝ) : Integer.Sparse.eval row19543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19543, Integer.Sparse.eval_collectBalanced, rawRowCheck19543]

theorem rawRowCheck19544 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form8 = rawRow19544 := by decide +kernel

theorem rowCheck19544 : row19544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19544 := by decide +kernel

theorem rowEval19544 (x : Key → ℝ) : Integer.Sparse.eval row19544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19544, Integer.Sparse.eval_collectBalanced, rawRowCheck19544]

theorem rawRowCheck19545 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form8 = rawRow19545 := by decide +kernel

theorem rowCheck19545 : row19545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19545 := by decide +kernel

theorem rowEval19545 (x : Key → ℝ) : Integer.Sparse.eval row19545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19545, Integer.Sparse.eval_collectBalanced, rawRowCheck19545]

theorem rawRowCheck19546 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form8 = rawRow19546 := by decide +kernel

theorem rowCheck19546 : row19546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19546 := by decide +kernel

theorem rowEval19546 (x : Key → ℝ) : Integer.Sparse.eval row19546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19546, Integer.Sparse.eval_collectBalanced, rawRowCheck19546]

theorem rawRowCheck19547 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19547 := by decide +kernel

theorem rowCheck19547 : row19547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19547 := by decide +kernel

theorem rowEval19547 (x : Key → ℝ) : Integer.Sparse.eval row19547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19547, Integer.Sparse.eval_collectBalanced, rawRowCheck19547]

theorem rawRowCheck19548 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form8 = rawRow19548 := by decide +kernel

theorem rowCheck19548 : row19548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19548 := by decide +kernel

theorem rowEval19548 (x : Key → ℝ) : Integer.Sparse.eval row19548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19548, Integer.Sparse.eval_collectBalanced, rawRowCheck19548]

theorem rawRowCheck19549 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form8 = rawRow19549 := by decide +kernel

theorem rowCheck19549 : row19549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19549 := by decide +kernel

theorem rowEval19549 (x : Key → ℝ) : Integer.Sparse.eval row19549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19549, Integer.Sparse.eval_collectBalanced, rawRowCheck19549]

theorem rawRowCheck19550 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form8 = rawRow19550 := by decide +kernel

theorem rowCheck19550 : row19550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19550 := by decide +kernel

theorem rowEval19550 (x : Key → ℝ) : Integer.Sparse.eval row19550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19550, Integer.Sparse.eval_collectBalanced, rawRowCheck19550]

theorem rawRowCheck19551 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form8 = rawRow19551 := by decide +kernel

theorem rowCheck19551 : row19551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19551 := by decide +kernel

theorem rowEval19551 (x : Key → ℝ) : Integer.Sparse.eval row19551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19551, Integer.Sparse.eval_collectBalanced, rawRowCheck19551]

theorem rawRowCheck19552 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form8 = rawRow19552 := by decide +kernel

theorem rowCheck19552 : row19552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19552 := by decide +kernel

theorem rowEval19552 (x : Key → ℝ) : Integer.Sparse.eval row19552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19552, Integer.Sparse.eval_collectBalanced, rawRowCheck19552]

theorem rawRowCheck19553 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form8 = rawRow19553 := by decide +kernel

theorem rowCheck19553 : row19553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19553 := by decide +kernel

theorem rowEval19553 (x : Key → ℝ) : Integer.Sparse.eval row19553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19553, Integer.Sparse.eval_collectBalanced, rawRowCheck19553]

theorem rawRowCheck19554 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form8 = rawRow19554 := by decide +kernel

theorem rowCheck19554 : row19554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19554 := by decide +kernel

theorem rowEval19554 (x : Key → ℝ) : Integer.Sparse.eval row19554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19554, Integer.Sparse.eval_collectBalanced, rawRowCheck19554]

theorem rawRowCheck19555 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form8 = rawRow19555 := by decide +kernel

theorem rowCheck19555 : row19555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19555 := by decide +kernel

theorem rowEval19555 (x : Key → ℝ) : Integer.Sparse.eval row19555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19555, Integer.Sparse.eval_collectBalanced, rawRowCheck19555]

theorem rawRowCheck19556 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form8 = rawRow19556 := by decide +kernel

theorem rowCheck19556 : row19556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19556 := by decide +kernel

theorem rowEval19556 (x : Key → ℝ) : Integer.Sparse.eval row19556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19556, Integer.Sparse.eval_collectBalanced, rawRowCheck19556]

theorem rawRowCheck19557 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form8 = rawRow19557 := by decide +kernel

theorem rowCheck19557 : row19557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19557 := by decide +kernel

theorem rowEval19557 (x : Key → ℝ) : Integer.Sparse.eval row19557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19557, Integer.Sparse.eval_collectBalanced, rawRowCheck19557]

theorem rawRowCheck19558 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form8 = rawRow19558 := by decide +kernel

theorem rowCheck19558 : row19558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19558 := by decide +kernel

theorem rowEval19558 (x : Key → ℝ) : Integer.Sparse.eval row19558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19558, Integer.Sparse.eval_collectBalanced, rawRowCheck19558]

theorem rawRowCheck19559 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form8 = rawRow19559 := by decide +kernel

theorem rowCheck19559 : row19559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19559 := by decide +kernel

theorem rowEval19559 (x : Key → ℝ) : Integer.Sparse.eval row19559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19559, Integer.Sparse.eval_collectBalanced, rawRowCheck19559]

theorem rawRowCheck19560 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19560 := by decide +kernel

theorem rowCheck19560 : row19560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19560 := by decide +kernel

theorem rowEval19560 (x : Key → ℝ) : Integer.Sparse.eval row19560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19560, Integer.Sparse.eval_collectBalanced, rawRowCheck19560]

theorem rawRowCheck19561 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form8 = rawRow19561 := by decide +kernel

theorem rowCheck19561 : row19561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19561 := by decide +kernel

theorem rowEval19561 (x : Key → ℝ) : Integer.Sparse.eval row19561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19561, Integer.Sparse.eval_collectBalanced, rawRowCheck19561]

theorem rawRowCheck19562 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form8 = rawRow19562 := by decide +kernel

theorem rowCheck19562 : row19562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19562 := by decide +kernel

theorem rowEval19562 (x : Key → ℝ) : Integer.Sparse.eval row19562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19562, Integer.Sparse.eval_collectBalanced, rawRowCheck19562]

theorem rawRowCheck19563 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form8 = rawRow19563 := by decide +kernel

theorem rowCheck19563 : row19563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19563 := by decide +kernel

theorem rowEval19563 (x : Key → ℝ) : Integer.Sparse.eval row19563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19563, Integer.Sparse.eval_collectBalanced, rawRowCheck19563]

theorem rawRowCheck19564 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form9 = rawRow19564 := by decide +kernel

theorem rowCheck19564 : row19564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19564 := by decide +kernel

theorem rowEval19564 (x : Key → ℝ) : Integer.Sparse.eval row19564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19564, Integer.Sparse.eval_collectBalanced, rawRowCheck19564]

theorem rawRowCheck19565 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form9 = rawRow19565 := by decide +kernel

theorem rowCheck19565 : row19565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19565 := by decide +kernel

theorem rowEval19565 (x : Key → ℝ) : Integer.Sparse.eval row19565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19565, Integer.Sparse.eval_collectBalanced, rawRowCheck19565]

theorem rawRowCheck19566 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form9 = rawRow19566 := by decide +kernel

theorem rowCheck19566 : row19566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19566 := by decide +kernel

theorem rowEval19566 (x : Key → ℝ) : Integer.Sparse.eval row19566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19566, Integer.Sparse.eval_collectBalanced, rawRowCheck19566]

theorem rawRowCheck19567 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form9 = rawRow19567 := by decide +kernel

theorem rowCheck19567 : row19567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19567 := by decide +kernel

theorem rowEval19567 (x : Key → ℝ) : Integer.Sparse.eval row19567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19567, Integer.Sparse.eval_collectBalanced, rawRowCheck19567]

theorem rawRowCheck19568 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form9 = rawRow19568 := by decide +kernel

theorem rowCheck19568 : row19568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19568 := by decide +kernel

theorem rowEval19568 (x : Key → ℝ) : Integer.Sparse.eval row19568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19568, Integer.Sparse.eval_collectBalanced, rawRowCheck19568]

theorem rawRowCheck19569 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form9 = rawRow19569 := by decide +kernel

theorem rowCheck19569 : row19569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19569 := by decide +kernel

theorem rowEval19569 (x : Key → ℝ) : Integer.Sparse.eval row19569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19569, Integer.Sparse.eval_collectBalanced, rawRowCheck19569]

theorem rawRowCheck19570 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form9 = rawRow19570 := by decide +kernel

theorem rowCheck19570 : row19570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19570 := by decide +kernel

theorem rowEval19570 (x : Key → ℝ) : Integer.Sparse.eval row19570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19570, Integer.Sparse.eval_collectBalanced, rawRowCheck19570]

theorem rawRowCheck19571 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form9 = rawRow19571 := by decide +kernel

theorem rowCheck19571 : row19571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19571 := by decide +kernel

theorem rowEval19571 (x : Key → ℝ) : Integer.Sparse.eval row19571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19571, Integer.Sparse.eval_collectBalanced, rawRowCheck19571]

theorem rawRowCheck19572 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form9 = rawRow19572 := by decide +kernel

theorem rowCheck19572 : row19572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19572 := by decide +kernel

theorem rowEval19572 (x : Key → ℝ) : Integer.Sparse.eval row19572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19572, Integer.Sparse.eval_collectBalanced, rawRowCheck19572]

theorem rawRowCheck19573 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form9 = rawRow19573 := by decide +kernel

theorem rowCheck19573 : row19573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19573 := by decide +kernel

theorem rowEval19573 (x : Key → ℝ) : Integer.Sparse.eval row19573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19573, Integer.Sparse.eval_collectBalanced, rawRowCheck19573]

theorem rawRowCheck19574 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form9 = rawRow19574 := by decide +kernel

theorem rowCheck19574 : row19574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19574 := by decide +kernel

theorem rowEval19574 (x : Key → ℝ) : Integer.Sparse.eval row19574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19574, Integer.Sparse.eval_collectBalanced, rawRowCheck19574]

theorem rawRowCheck19575 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form9 = rawRow19575 := by decide +kernel

theorem rowCheck19575 : row19575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19575 := by decide +kernel

theorem rowEval19575 (x : Key → ℝ) : Integer.Sparse.eval row19575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19575, Integer.Sparse.eval_collectBalanced, rawRowCheck19575]

theorem rawRowCheck19576 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form9 = rawRow19576 := by decide +kernel

theorem rowCheck19576 : row19576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19576 := by decide +kernel

theorem rowEval19576 (x : Key → ℝ) : Integer.Sparse.eval row19576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19576, Integer.Sparse.eval_collectBalanced, rawRowCheck19576]

theorem rawRowCheck19577 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form9 = rawRow19577 := by decide +kernel

theorem rowCheck19577 : row19577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19577 := by decide +kernel

theorem rowEval19577 (x : Key → ℝ) : Integer.Sparse.eval row19577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19577, Integer.Sparse.eval_collectBalanced, rawRowCheck19577]

theorem rawRowCheck19578 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form9 = rawRow19578 := by decide +kernel

theorem rowCheck19578 : row19578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19578 := by decide +kernel

theorem rowEval19578 (x : Key → ℝ) : Integer.Sparse.eval row19578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19578, Integer.Sparse.eval_collectBalanced, rawRowCheck19578]

theorem rawRowCheck19579 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form9 = rawRow19579 := by decide +kernel

theorem rowCheck19579 : row19579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19579 := by decide +kernel

theorem rowEval19579 (x : Key → ℝ) : Integer.Sparse.eval row19579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19579, Integer.Sparse.eval_collectBalanced, rawRowCheck19579]

theorem rawRowCheck19580 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form9 = rawRow19580 := by decide +kernel

theorem rowCheck19580 : row19580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19580 := by decide +kernel

theorem rowEval19580 (x : Key → ℝ) : Integer.Sparse.eval row19580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19580, Integer.Sparse.eval_collectBalanced, rawRowCheck19580]

theorem rawRowCheck19581 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form9 = rawRow19581 := by decide +kernel

theorem rowCheck19581 : row19581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19581 := by decide +kernel

theorem rowEval19581 (x : Key → ℝ) : Integer.Sparse.eval row19581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19581, Integer.Sparse.eval_collectBalanced, rawRowCheck19581]

theorem rawRowCheck19582 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form9 = rawRow19582 := by decide +kernel

theorem rowCheck19582 : row19582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19582 := by decide +kernel

theorem rowEval19582 (x : Key → ℝ) : Integer.Sparse.eval row19582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19582, Integer.Sparse.eval_collectBalanced, rawRowCheck19582]

theorem rawRowCheck19583 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form9 = rawRow19583 := by decide +kernel

theorem rowCheck19583 : row19583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19583 := by decide +kernel

theorem rowEval19583 (x : Key → ℝ) : Integer.Sparse.eval row19583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19583, Integer.Sparse.eval_collectBalanced, rawRowCheck19583]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19584 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form10 = rawRow19584 := by decide +kernel

theorem rowCheck19584 : row19584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19584 := by decide +kernel

theorem rowEval19584 (x : Key → ℝ) : Integer.Sparse.eval row19584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19584, Integer.Sparse.eval_collectBalanced, rawRowCheck19584]

theorem rawRowCheck19585 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form10 = rawRow19585 := by decide +kernel

theorem rowCheck19585 : row19585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19585 := by decide +kernel

theorem rowEval19585 (x : Key → ℝ) : Integer.Sparse.eval row19585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19585, Integer.Sparse.eval_collectBalanced, rawRowCheck19585]

theorem rawRowCheck19586 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form10 = rawRow19586 := by decide +kernel

theorem rowCheck19586 : row19586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19586 := by decide +kernel

theorem rowEval19586 (x : Key → ℝ) : Integer.Sparse.eval row19586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19586, Integer.Sparse.eval_collectBalanced, rawRowCheck19586]

theorem rawRowCheck19587 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form10 = rawRow19587 := by decide +kernel

theorem rowCheck19587 : row19587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19587 := by decide +kernel

theorem rowEval19587 (x : Key → ℝ) : Integer.Sparse.eval row19587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19587, Integer.Sparse.eval_collectBalanced, rawRowCheck19587]

theorem rawRowCheck19588 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form10 = rawRow19588 := by decide +kernel

theorem rowCheck19588 : row19588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19588 := by decide +kernel

theorem rowEval19588 (x : Key → ℝ) : Integer.Sparse.eval row19588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19588, Integer.Sparse.eval_collectBalanced, rawRowCheck19588]

theorem rawRowCheck19589 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form10 = rawRow19589 := by decide +kernel

theorem rowCheck19589 : row19589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19589 := by decide +kernel

theorem rowEval19589 (x : Key → ℝ) : Integer.Sparse.eval row19589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19589, Integer.Sparse.eval_collectBalanced, rawRowCheck19589]

theorem rawRowCheck19590 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form10 = rawRow19590 := by decide +kernel

theorem rowCheck19590 : row19590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19590 := by decide +kernel

theorem rowEval19590 (x : Key → ℝ) : Integer.Sparse.eval row19590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19590, Integer.Sparse.eval_collectBalanced, rawRowCheck19590]

theorem rawRowCheck19591 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form10 = rawRow19591 := by decide +kernel

theorem rowCheck19591 : row19591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19591 := by decide +kernel

theorem rowEval19591 (x : Key → ℝ) : Integer.Sparse.eval row19591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19591, Integer.Sparse.eval_collectBalanced, rawRowCheck19591]

theorem rawRowCheck19592 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form10 = rawRow19592 := by decide +kernel

theorem rowCheck19592 : row19592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19592 := by decide +kernel

theorem rowEval19592 (x : Key → ℝ) : Integer.Sparse.eval row19592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19592, Integer.Sparse.eval_collectBalanced, rawRowCheck19592]

theorem rawRowCheck19593 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form10 = rawRow19593 := by decide +kernel

theorem rowCheck19593 : row19593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19593 := by decide +kernel

theorem rowEval19593 (x : Key → ℝ) : Integer.Sparse.eval row19593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19593, Integer.Sparse.eval_collectBalanced, rawRowCheck19593]

theorem rawRowCheck19594 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form10 = rawRow19594 := by decide +kernel

theorem rowCheck19594 : row19594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19594 := by decide +kernel

theorem rowEval19594 (x : Key → ℝ) : Integer.Sparse.eval row19594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19594, Integer.Sparse.eval_collectBalanced, rawRowCheck19594]

theorem rawRowCheck19595 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form10 = rawRow19595 := by decide +kernel

theorem rowCheck19595 : row19595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19595 := by decide +kernel

theorem rowEval19595 (x : Key → ℝ) : Integer.Sparse.eval row19595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19595, Integer.Sparse.eval_collectBalanced, rawRowCheck19595]

theorem rawRowCheck19596 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form10 = rawRow19596 := by decide +kernel

theorem rowCheck19596 : row19596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19596 := by decide +kernel

theorem rowEval19596 (x : Key → ℝ) : Integer.Sparse.eval row19596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19596, Integer.Sparse.eval_collectBalanced, rawRowCheck19596]

theorem rawRowCheck19597 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form10 = rawRow19597 := by decide +kernel

theorem rowCheck19597 : row19597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19597 := by decide +kernel

theorem rowEval19597 (x : Key → ℝ) : Integer.Sparse.eval row19597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19597, Integer.Sparse.eval_collectBalanced, rawRowCheck19597]

theorem rawRowCheck19598 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form10 = rawRow19598 := by decide +kernel

theorem rowCheck19598 : row19598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19598 := by decide +kernel

theorem rowEval19598 (x : Key → ℝ) : Integer.Sparse.eval row19598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19598, Integer.Sparse.eval_collectBalanced, rawRowCheck19598]

theorem rawRowCheck19599 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form10 = rawRow19599 := by decide +kernel

theorem rowCheck19599 : row19599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19599 := by decide +kernel

theorem rowEval19599 (x : Key → ℝ) : Integer.Sparse.eval row19599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19599, Integer.Sparse.eval_collectBalanced, rawRowCheck19599]

theorem rawRowCheck19600 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form10 = rawRow19600 := by decide +kernel

theorem rowCheck19600 : row19600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19600 := by decide +kernel

theorem rowEval19600 (x : Key → ℝ) : Integer.Sparse.eval row19600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19600, Integer.Sparse.eval_collectBalanced, rawRowCheck19600]

theorem rawRowCheck19601 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form10 = rawRow19601 := by decide +kernel

theorem rowCheck19601 : row19601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19601 := by decide +kernel

theorem rowEval19601 (x : Key → ℝ) : Integer.Sparse.eval row19601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19601, Integer.Sparse.eval_collectBalanced, rawRowCheck19601]

theorem rawRowCheck19602 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form10 = rawRow19602 := by decide +kernel

theorem rowCheck19602 : row19602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19602 := by decide +kernel

theorem rowEval19602 (x : Key → ℝ) : Integer.Sparse.eval row19602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck19602, Integer.Sparse.eval_collectBalanced, rawRowCheck19602]

theorem rawRowCheck19603 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form10 = rawRow19603 := by decide +kernel

theorem rowCheck19603 : row19603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19603 := by decide +kernel

theorem rowEval19603 (x : Key → ℝ) : Integer.Sparse.eval row19603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck19603, Integer.Sparse.eval_collectBalanced, rawRowCheck19603]

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

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19384 x
  · exact rowEval19385 x
  · exact rowEval19386 x
  · exact rowEval19387 x
  · exact rowEval19388 x
  · exact rowEval19389 x
  · exact rowEval19390 x
  · exact rowEval19391 x
  · exact rowEval19392 x
  · exact rowEval19393 x
  · exact rowEval19394 x
  · exact rowEval19395 x
  · exact rowEval19396 x
  · exact rowEval19397 x
  · exact rowEval19398 x
  · exact rowEval19399 x
  · exact rowEval19400 x
  · exact rowEval19401 x
  · exact rowEval19402 x
  · exact rowEval19403 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19404 x
  · exact rowEval19405 x
  · exact rowEval19406 x
  · exact rowEval19407 x
  · exact rowEval19408 x
  · exact rowEval19409 x
  · exact rowEval19410 x
  · exact rowEval19411 x
  · exact rowEval19412 x
  · exact rowEval19413 x
  · exact rowEval19414 x
  · exact rowEval19415 x
  · exact rowEval19416 x
  · exact rowEval19417 x
  · exact rowEval19418 x
  · exact rowEval19419 x
  · exact rowEval19420 x
  · exact rowEval19421 x
  · exact rowEval19422 x
  · exact rowEval19423 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval19424 x
  · exact rowEval19425 x
  · exact rowEval19426 x
  · exact rowEval19427 x
  · exact rowEval19428 x
  · exact rowEval19429 x
  · exact rowEval19430 x
  · exact rowEval19431 x
  · exact rowEval19432 x
  · exact rowEval19433 x
  · exact rowEval19434 x
  · exact rowEval19435 x
  · exact rowEval19436 x
  · exact rowEval19437 x
  · exact rowEval19438 x
  · exact rowEval19439 x
  · exact rowEval19440 x
  · exact rowEval19441 x
  · exact rowEval19442 x
  · exact rowEval19443 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19444 x
  · exact rowEval19445 x
  · exact rowEval19446 x
  · exact rowEval19447 x
  · exact rowEval19448 x
  · exact rowEval19449 x
  · exact rowEval19450 x
  · exact rowEval19451 x
  · exact rowEval19452 x
  · exact rowEval19453 x
  · exact rowEval19454 x
  · exact rowEval19455 x
  · exact rowEval19456 x
  · exact rowEval19457 x
  · exact rowEval19458 x
  · exact rowEval19459 x
  · exact rowEval19460 x
  · exact rowEval19461 x
  · exact rowEval19462 x
  · exact rowEval19463 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19464 x
  · exact rowEval19465 x
  · exact rowEval19466 x
  · exact rowEval19467 x
  · exact rowEval19468 x
  · exact rowEval19469 x
  · exact rowEval19470 x
  · exact rowEval19471 x
  · exact rowEval19472 x
  · exact rowEval19473 x
  · exact rowEval19474 x
  · exact rowEval19475 x
  · exact rowEval19476 x
  · exact rowEval19477 x
  · exact rowEval19478 x
  · exact rowEval19479 x
  · exact rowEval19480 x
  · exact rowEval19481 x
  · exact rowEval19482 x
  · exact rowEval19483 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

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

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19504 x
  · exact rowEval19505 x
  · exact rowEval19506 x
  · exact rowEval19507 x
  · exact rowEval19508 x
  · exact rowEval19509 x
  · exact rowEval19510 x
  · exact rowEval19511 x
  · exact rowEval19512 x
  · exact rowEval19513 x
  · exact rowEval19514 x
  · exact rowEval19515 x
  · exact rowEval19516 x
  · exact rowEval19517 x
  · exact rowEval19518 x
  · exact rowEval19519 x
  · exact rowEval19520 x
  · exact rowEval19521 x
  · exact rowEval19522 x
  · exact rowEval19523 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval19524 x
  · exact rowEval19525 x
  · exact rowEval19526 x
  · exact rowEval19527 x
  · exact rowEval19528 x
  · exact rowEval19529 x
  · exact rowEval19530 x
  · exact rowEval19531 x
  · exact rowEval19532 x
  · exact rowEval19533 x
  · exact rowEval19534 x
  · exact rowEval19535 x
  · exact rowEval19536 x
  · exact rowEval19537 x
  · exact rowEval19538 x
  · exact rowEval19539 x
  · exact rowEval19540 x
  · exact rowEval19541 x
  · exact rowEval19542 x
  · exact rowEval19543 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval19544 x
  · exact rowEval19545 x
  · exact rowEval19546 x
  · exact rowEval19547 x
  · exact rowEval19548 x
  · exact rowEval19549 x
  · exact rowEval19550 x
  · exact rowEval19551 x
  · exact rowEval19552 x
  · exact rowEval19553 x
  · exact rowEval19554 x
  · exact rowEval19555 x
  · exact rowEval19556 x
  · exact rowEval19557 x
  · exact rowEval19558 x
  · exact rowEval19559 x
  · exact rowEval19560 x
  · exact rowEval19561 x
  · exact rowEval19562 x
  · exact rowEval19563 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form9) x := by
  fin_cases k
  · exact rowEval19564 x
  · exact rowEval19565 x
  · exact rowEval19566 x
  · exact rowEval19567 x
  · exact rowEval19568 x
  · exact rowEval19569 x
  · exact rowEval19570 x
  · exact rowEval19571 x
  · exact rowEval19572 x
  · exact rowEval19573 x
  · exact rowEval19574 x
  · exact rowEval19575 x
  · exact rowEval19576 x
  · exact rowEval19577 x
  · exact rowEval19578 x
  · exact rowEval19579 x
  · exact rowEval19580 x
  · exact rowEval19581 x
  · exact rowEval19582 x
  · exact rowEval19583 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form10) x := by
  fin_cases k
  · exact rowEval19584 x
  · exact rowEval19585 x
  · exact rowEval19586 x
  · exact rowEval19587 x
  · exact rowEval19588 x
  · exact rowEval19589 x
  · exact rowEval19590 x
  · exact rowEval19591 x
  · exact rowEval19592 x
  · exact rowEval19593 x
  · exact rowEval19594 x
  · exact rowEval19595 x
  · exact rowEval19596 x
  · exact rowEval19597 x
  · exact rowEval19598 x
  · exact rowEval19599 x
  · exact rowEval19600 x
  · exact rowEval19601 x
  · exact rowEval19602 x
  · exact rowEval19603 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

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

theorem entryEvalRow10_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 10 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 10).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval10_0 B hB
  · exact entryEval10_1 B hB
  · exact entryEval10_2 B hB
  · exact entryEval10_3 B hB
  · exact entryEval10_4 B hB
  · exact entryEval10_5 B hB
  · exact entryEval10_6 B hB
  · exact entryEval10_7 B hB
  · exact entryEval10_8 B hB
  · exact entryEval10_9 B hB
  · exact entryEval10_10 B hB
  · exact (entryEval11_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10_e_oai
