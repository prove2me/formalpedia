-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:19:23.14903+00:00
-- url     : https://prove2.me/submissions/ebd0e325-4d79-4ad6-b0b4-502532a109fe

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E033
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E057
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval21_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval9_6_e

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

theorem rawRowCheck8581 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8581 := by decide +kernel

theorem rowCheck8581 : row8581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8581 := by decide +kernel

theorem rowEval8581 (x : Key → ℝ) : Integer.Sparse.eval row8581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8581, Integer.Sparse.eval_collectBalanced, rawRowCheck8581]

theorem rawRowCheck8582 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8582 := by decide +kernel

theorem rowCheck8582 : row8582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8582 := by decide +kernel

theorem rowEval8582 (x : Key → ℝ) : Integer.Sparse.eval row8582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8582, Integer.Sparse.eval_collectBalanced, rawRowCheck8582]

theorem rawRowCheck8583 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8583 := by decide +kernel

theorem rowCheck8583 : row8583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8583 := by decide +kernel

theorem rowEval8583 (x : Key → ℝ) : Integer.Sparse.eval row8583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8583, Integer.Sparse.eval_collectBalanced, rawRowCheck8583]

theorem rawRowCheck8584 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8584 := by decide +kernel

theorem rowCheck8584 : row8584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8584 := by decide +kernel

theorem rowEval8584 (x : Key → ℝ) : Integer.Sparse.eval row8584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8584, Integer.Sparse.eval_collectBalanced, rawRowCheck8584]

theorem rawRowCheck8585 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow8585 := by decide +kernel

theorem rowCheck8585 : row8585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8585 := by decide +kernel

theorem rowEval8585 (x : Key → ℝ) : Integer.Sparse.eval row8585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8585, Integer.Sparse.eval_collectBalanced, rawRowCheck8585]

theorem rawRowCheck8586 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow8586 := by decide +kernel

theorem rowCheck8586 : row8586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8586 := by decide +kernel

theorem rowEval8586 (x : Key → ℝ) : Integer.Sparse.eval row8586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8586, Integer.Sparse.eval_collectBalanced, rawRowCheck8586]

theorem rawRowCheck8587 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow8587 := by decide +kernel

theorem rowCheck8587 : row8587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8587 := by decide +kernel

theorem rowEval8587 (x : Key → ℝ) : Integer.Sparse.eval row8587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8587, Integer.Sparse.eval_collectBalanced, rawRowCheck8587]

theorem rawRowCheck8588 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8588 := by decide +kernel

theorem rowCheck8588 : row8588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8588 := by decide +kernel

theorem rowEval8588 (x : Key → ℝ) : Integer.Sparse.eval row8588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8588, Integer.Sparse.eval_collectBalanced, rawRowCheck8588]

theorem rawRowCheck8589 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8589 := by decide +kernel

theorem rowCheck8589 : row8589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8589 := by decide +kernel

theorem rowEval8589 (x : Key → ℝ) : Integer.Sparse.eval row8589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8589, Integer.Sparse.eval_collectBalanced, rawRowCheck8589]

theorem rawRowCheck8590 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8590 := by decide +kernel

theorem rowCheck8590 : row8590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8590 := by decide +kernel

theorem rowEval8590 (x : Key → ℝ) : Integer.Sparse.eval row8590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8590, Integer.Sparse.eval_collectBalanced, rawRowCheck8590]

theorem rawRowCheck8591 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form6 = rawRow8591 := by decide +kernel

theorem rowCheck8591 : row8591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8591 := by decide +kernel

theorem rowEval8591 (x : Key → ℝ) : Integer.Sparse.eval row8591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8591, Integer.Sparse.eval_collectBalanced, rawRowCheck8591]

theorem rawRowCheck8592 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form6 = rawRow8592 := by decide +kernel

theorem rowCheck8592 : row8592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8592 := by decide +kernel

theorem rowEval8592 (x : Key → ℝ) : Integer.Sparse.eval row8592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8592, Integer.Sparse.eval_collectBalanced, rawRowCheck8592]

theorem rawRowCheck8593 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form6 = rawRow8593 := by decide +kernel

theorem rowCheck8593 : row8593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8593 := by decide +kernel

theorem rowEval8593 (x : Key → ℝ) : Integer.Sparse.eval row8593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8593, Integer.Sparse.eval_collectBalanced, rawRowCheck8593]

theorem rawRowCheck8594 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form6 = rawRow8594 := by decide +kernel

theorem rowCheck8594 : row8594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8594 := by decide +kernel

theorem rowEval8594 (x : Key → ℝ) : Integer.Sparse.eval row8594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8594, Integer.Sparse.eval_collectBalanced, rawRowCheck8594]

theorem rawRowCheck8595 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form6 = rawRow8595 := by decide +kernel

theorem rowCheck8595 : row8595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8595 := by decide +kernel

theorem rowEval8595 (x : Key → ℝ) : Integer.Sparse.eval row8595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8595, Integer.Sparse.eval_collectBalanced, rawRowCheck8595]

theorem rawRowCheck8596 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form6 = rawRow8596 := by decide +kernel

theorem rowCheck8596 : row8596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8596 := by decide +kernel

theorem rowEval8596 (x : Key → ℝ) : Integer.Sparse.eval row8596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8596, Integer.Sparse.eval_collectBalanced, rawRowCheck8596]

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

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8581 x
  · exact rowEval8582 x
  · exact rowEval8583 x
  · exact rowEval8584 x
  · exact rowEval8585 x
  · exact rowEval8586 x
  · exact rowEval8587 x
  · exact rowEval8588 x
  · exact rowEval8589 x
  · exact rowEval8590 x
  · exact rowEval8591 x
  · exact rowEval8592 x
  · exact rowEval8593 x
  · exact rowEval8594 x
  · exact rowEval8595 x
  · exact rowEval8596 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

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

theorem rawRowCheck8785 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8785 := by decide +kernel

theorem rowCheck8785 : row8785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8785 := by decide +kernel

theorem rowEval8785 (x : Key → ℝ) : Integer.Sparse.eval row8785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8785, Integer.Sparse.eval_collectBalanced, rawRowCheck8785]

theorem rawRowCheck8786 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8786 := by decide +kernel

theorem rowCheck8786 : row8786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8786 := by decide +kernel

theorem rowEval8786 (x : Key → ℝ) : Integer.Sparse.eval row8786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8786, Integer.Sparse.eval_collectBalanced, rawRowCheck8786]

theorem rawRowCheck8787 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8787 := by decide +kernel

theorem rowCheck8787 : row8787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8787 := by decide +kernel

theorem rowEval8787 (x : Key → ℝ) : Integer.Sparse.eval row8787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8787, Integer.Sparse.eval_collectBalanced, rawRowCheck8787]

theorem rawRowCheck8788 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8788 := by decide +kernel

theorem rowCheck8788 : row8788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8788 := by decide +kernel

theorem rowEval8788 (x : Key → ℝ) : Integer.Sparse.eval row8788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8788, Integer.Sparse.eval_collectBalanced, rawRowCheck8788]

theorem rawRowCheck8789 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8789 := by decide +kernel

theorem rowCheck8789 : row8789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8789 := by decide +kernel

theorem rowEval8789 (x : Key → ℝ) : Integer.Sparse.eval row8789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8789, Integer.Sparse.eval_collectBalanced, rawRowCheck8789]

theorem rawRowCheck8790 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form6 = rawRow8790 := by decide +kernel

theorem rowCheck8790 : row8790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8790 := by decide +kernel

theorem rowEval8790 (x : Key → ℝ) : Integer.Sparse.eval row8790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8790, Integer.Sparse.eval_collectBalanced, rawRowCheck8790]

theorem rawRowCheck8791 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form6 = rawRow8791 := by decide +kernel

theorem rowCheck8791 : row8791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8791 := by decide +kernel

theorem rowEval8791 (x : Key → ℝ) : Integer.Sparse.eval row8791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8791, Integer.Sparse.eval_collectBalanced, rawRowCheck8791]

theorem rawRowCheck8792 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form6 = rawRow8792 := by decide +kernel

theorem rowCheck8792 : row8792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8792 := by decide +kernel

theorem rowEval8792 (x : Key → ℝ) : Integer.Sparse.eval row8792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck8792, Integer.Sparse.eval_collectBalanced, rawRowCheck8792]

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

theorem rawRowCheck8937 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8937 := by decide +kernel

theorem rowCheck8937 : row8937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8937 := by decide +kernel

theorem rowEval8937 (x : Key → ℝ) : Integer.Sparse.eval row8937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8937, Integer.Sparse.eval_collectBalanced, rawRowCheck8937]

theorem rawRowCheck8938 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8938 := by decide +kernel

theorem rowCheck8938 : row8938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8938 := by decide +kernel

theorem rowEval8938 (x : Key → ℝ) : Integer.Sparse.eval row8938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8938, Integer.Sparse.eval_collectBalanced, rawRowCheck8938]

theorem rawRowCheck8939 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8939 := by decide +kernel

theorem rowCheck8939 : row8939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8939 := by decide +kernel

theorem rowEval8939 (x : Key → ℝ) : Integer.Sparse.eval row8939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8939, Integer.Sparse.eval_collectBalanced, rawRowCheck8939]

theorem rawRowCheck8940 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8940 := by decide +kernel

theorem rowCheck8940 : row8940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8940 := by decide +kernel

theorem rowEval8940 (x : Key → ℝ) : Integer.Sparse.eval row8940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8940, Integer.Sparse.eval_collectBalanced, rawRowCheck8940]

theorem rawRowCheck8941 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8941 := by decide +kernel

theorem rowCheck8941 : row8941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8941 := by decide +kernel

theorem rowEval8941 (x : Key → ℝ) : Integer.Sparse.eval row8941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8941, Integer.Sparse.eval_collectBalanced, rawRowCheck8941]

theorem rawRowCheck8942 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8942 := by decide +kernel

theorem rowCheck8942 : row8942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8942 := by decide +kernel

theorem rowEval8942 (x : Key → ℝ) : Integer.Sparse.eval row8942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8942, Integer.Sparse.eval_collectBalanced, rawRowCheck8942]

theorem rawRowCheck8943 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8943 := by decide +kernel

theorem rowCheck8943 : row8943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8943 := by decide +kernel

theorem rowEval8943 (x : Key → ℝ) : Integer.Sparse.eval row8943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8943, Integer.Sparse.eval_collectBalanced, rawRowCheck8943]

theorem rawRowCheck8944 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form6 = rawRow8944 := by decide +kernel

theorem rowCheck8944 : row8944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8944 := by decide +kernel

theorem rowEval8944 (x : Key → ℝ) : Integer.Sparse.eval row8944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8944, Integer.Sparse.eval_collectBalanced, rawRowCheck8944]

theorem rawRowCheck8945 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form6 = rawRow8945 := by decide +kernel

theorem rowCheck8945 : row8945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8945 := by decide +kernel

theorem rowEval8945 (x : Key → ℝ) : Integer.Sparse.eval row8945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8945, Integer.Sparse.eval_collectBalanced, rawRowCheck8945]

theorem rawRowCheck8946 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form6 = rawRow8946 := by decide +kernel

theorem rowCheck8946 : row8946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8946 := by decide +kernel

theorem rowEval8946 (x : Key → ℝ) : Integer.Sparse.eval row8946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8946, Integer.Sparse.eval_collectBalanced, rawRowCheck8946]

theorem rawRowCheck8947 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form6 = rawRow8947 := by decide +kernel

theorem rowCheck8947 : row8947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8947 := by decide +kernel

theorem rowEval8947 (x : Key → ℝ) : Integer.Sparse.eval row8947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8947, Integer.Sparse.eval_collectBalanced, rawRowCheck8947]

theorem rawRowCheck8948 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form6 = rawRow8948 := by decide +kernel

theorem rowCheck8948 : row8948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8948 := by decide +kernel

theorem rowEval8948 (x : Key → ℝ) : Integer.Sparse.eval row8948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8948, Integer.Sparse.eval_collectBalanced, rawRowCheck8948]

theorem rawRowCheck8949 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form6 = rawRow8949 := by decide +kernel

theorem rowCheck8949 : row8949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8949 := by decide +kernel

theorem rowEval8949 (x : Key → ℝ) : Integer.Sparse.eval row8949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8949, Integer.Sparse.eval_collectBalanced, rawRowCheck8949]

theorem rawRowCheck8950 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow8950 := by decide +kernel

theorem rowCheck8950 : row8950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8950 := by decide +kernel

theorem rowEval8950 (x : Key → ℝ) : Integer.Sparse.eval row8950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8950, Integer.Sparse.eval_collectBalanced, rawRowCheck8950]

theorem rawRowCheck8951 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow8951 := by decide +kernel

theorem rowCheck8951 : row8951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8951 := by decide +kernel

theorem rowEval8951 (x : Key → ℝ) : Integer.Sparse.eval row8951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8951, Integer.Sparse.eval_collectBalanced, rawRowCheck8951]

theorem rawRowCheck8952 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow8952 := by decide +kernel

theorem rowCheck8952 : row8952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8952 := by decide +kernel

theorem rowEval8952 (x : Key → ℝ) : Integer.Sparse.eval row8952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8952, Integer.Sparse.eval_collectBalanced, rawRowCheck8952]

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

theorem entryCheck12_6 : entry12_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_6 k)) := by decide +kernel

theorem rowsSound12_6 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8785 x
  · exact rowEval8786 x
  · exact rowEval8787 x
  · exact rowEval8788 x
  · exact rowEval8789 x
  · exact rowEval8790 x
  · exact rowEval8791 x
  · exact rowEval8792 x

theorem entryEval12_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_6 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck12_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_6]

end MUB6.Certificate.GramEntries.Block3

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

theorem entryCheck13_6 : entry13_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_6 k)) := by decide +kernel

theorem rowsSound13_6 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8937 x
  · exact rowEval8938 x
  · exact rowEval8939 x
  · exact rowEval8940 x
  · exact rowEval8941 x
  · exact rowEval8942 x
  · exact rowEval8943 x
  · exact rowEval8944 x
  · exact rowEval8945 x
  · exact rowEval8946 x
  · exact rowEval8947 x
  · exact rowEval8948 x
  · exact rowEval8949 x
  · exact rowEval8950 x
  · exact rowEval8951 x
  · exact rowEval8952 x

theorem entryEval13_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_6 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck13_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_6]

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

theorem rawRowCheck9101 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow9101 := by decide +kernel

theorem rowCheck9101 : row9101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9101 := by decide +kernel

theorem rowEval9101 (x : Key → ℝ) : Integer.Sparse.eval row9101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9101, Integer.Sparse.eval_collectBalanced, rawRowCheck9101]

theorem rawRowCheck9102 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow9102 := by decide +kernel

theorem rowCheck9102 : row9102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9102 := by decide +kernel

theorem rowEval9102 (x : Key → ℝ) : Integer.Sparse.eval row9102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9102, Integer.Sparse.eval_collectBalanced, rawRowCheck9102]

theorem rawRowCheck9103 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow9103 := by decide +kernel

theorem rowCheck9103 : row9103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9103 := by decide +kernel

theorem rowEval9103 (x : Key → ℝ) : Integer.Sparse.eval row9103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9103, Integer.Sparse.eval_collectBalanced, rawRowCheck9103]

theorem rawRowCheck9104 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow9104 := by decide +kernel

theorem rowCheck9104 : row9104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9104 := by decide +kernel

theorem rowEval9104 (x : Key → ℝ) : Integer.Sparse.eval row9104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9104, Integer.Sparse.eval_collectBalanced, rawRowCheck9104]

theorem rawRowCheck9105 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form6 = rawRow9105 := by decide +kernel

theorem rowCheck9105 : row9105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9105 := by decide +kernel

theorem rowEval9105 (x : Key → ℝ) : Integer.Sparse.eval row9105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9105, Integer.Sparse.eval_collectBalanced, rawRowCheck9105]

theorem rawRowCheck9106 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form6 = rawRow9106 := by decide +kernel

theorem rowCheck9106 : row9106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9106 := by decide +kernel

theorem rowEval9106 (x : Key → ℝ) : Integer.Sparse.eval row9106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9106, Integer.Sparse.eval_collectBalanced, rawRowCheck9106]

theorem rawRowCheck9107 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form6 = rawRow9107 := by decide +kernel

theorem rowCheck9107 : row9107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9107 := by decide +kernel

theorem rowEval9107 (x : Key → ℝ) : Integer.Sparse.eval row9107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9107, Integer.Sparse.eval_collectBalanced, rawRowCheck9107]

theorem rawRowCheck9108 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form6 = rawRow9108 := by decide +kernel

theorem rowCheck9108 : row9108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9108 := by decide +kernel

theorem rowEval9108 (x : Key → ℝ) : Integer.Sparse.eval row9108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9108, Integer.Sparse.eval_collectBalanced, rawRowCheck9108]

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

theorem entryCheck14_6 : entry14_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_6 k)) := by decide +kernel

theorem rowsSound14_6 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval9101 x
  · exact rowEval9102 x
  · exact rowEval9103 x
  · exact rowEval9104 x
  · exact rowEval9105 x
  · exact rowEval9106 x
  · exact rowEval9107 x
  · exact rowEval9108 x

theorem entryEval14_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_6 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck14_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_6]

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

theorem rawRowCheck9245 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form6 = rawRow9245 := by decide +kernel

theorem rowCheck9245 : row9245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9245 := by decide +kernel

theorem rowEval9245 (x : Key → ℝ) : Integer.Sparse.eval row9245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9245, Integer.Sparse.eval_collectBalanced, rawRowCheck9245]

theorem rawRowCheck9246 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form6 = rawRow9246 := by decide +kernel

theorem rowCheck9246 : row9246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9246 := by decide +kernel

theorem rowEval9246 (x : Key → ℝ) : Integer.Sparse.eval row9246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9246, Integer.Sparse.eval_collectBalanced, rawRowCheck9246]

theorem rawRowCheck9247 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form6 = rawRow9247 := by decide +kernel

theorem rowCheck9247 : row9247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9247 := by decide +kernel

theorem rowEval9247 (x : Key → ℝ) : Integer.Sparse.eval row9247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9247, Integer.Sparse.eval_collectBalanced, rawRowCheck9247]

theorem rawRowCheck9248 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form6 = rawRow9248 := by decide +kernel

theorem rowCheck9248 : row9248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9248 := by decide +kernel

theorem rowEval9248 (x : Key → ℝ) : Integer.Sparse.eval row9248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9248, Integer.Sparse.eval_collectBalanced, rawRowCheck9248]

theorem rawRowCheck9249 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form6 = rawRow9249 := by decide +kernel

theorem rowCheck9249 : row9249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9249 := by decide +kernel

theorem rowEval9249 (x : Key → ℝ) : Integer.Sparse.eval row9249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9249, Integer.Sparse.eval_collectBalanced, rawRowCheck9249]

theorem rawRowCheck9250 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form6 = rawRow9250 := by decide +kernel

theorem rowCheck9250 : row9250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9250 := by decide +kernel

theorem rowEval9250 (x : Key → ℝ) : Integer.Sparse.eval row9250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9250, Integer.Sparse.eval_collectBalanced, rawRowCheck9250]

theorem rawRowCheck9251 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form6 = rawRow9251 := by decide +kernel

theorem rowCheck9251 : row9251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9251 := by decide +kernel

theorem rowEval9251 (x : Key → ℝ) : Integer.Sparse.eval row9251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9251, Integer.Sparse.eval_collectBalanced, rawRowCheck9251]

theorem rawRowCheck9252 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form6 = rawRow9252 := by decide +kernel

theorem rowCheck9252 : row9252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9252 := by decide +kernel

theorem rowEval9252 (x : Key → ℝ) : Integer.Sparse.eval row9252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9252, Integer.Sparse.eval_collectBalanced, rawRowCheck9252]

theorem rawRowCheck9253 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form6 = rawRow9253 := by decide +kernel

theorem rowCheck9253 : row9253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9253 := by decide +kernel

theorem rowEval9253 (x : Key → ℝ) : Integer.Sparse.eval row9253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9253, Integer.Sparse.eval_collectBalanced, rawRowCheck9253]

theorem rawRowCheck9254 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form6 = rawRow9254 := by decide +kernel

theorem rowCheck9254 : row9254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9254 := by decide +kernel

theorem rowEval9254 (x : Key → ℝ) : Integer.Sparse.eval row9254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9254, Integer.Sparse.eval_collectBalanced, rawRowCheck9254]

theorem rawRowCheck9255 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form6 = rawRow9255 := by decide +kernel

theorem rowCheck9255 : row9255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9255 := by decide +kernel

theorem rowEval9255 (x : Key → ℝ) : Integer.Sparse.eval row9255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9255, Integer.Sparse.eval_collectBalanced, rawRowCheck9255]

theorem rawRowCheck9256 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form6 = rawRow9256 := by decide +kernel

theorem rowCheck9256 : row9256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9256 := by decide +kernel

theorem rowEval9256 (x : Key → ℝ) : Integer.Sparse.eval row9256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9256, Integer.Sparse.eval_collectBalanced, rawRowCheck9256]

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

theorem rawRowCheck9413 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form6 = rawRow9413 := by decide +kernel

theorem rowCheck9413 : row9413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9413 := by decide +kernel

theorem rowEval9413 (x : Key → ℝ) : Integer.Sparse.eval row9413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9413, Integer.Sparse.eval_collectBalanced, rawRowCheck9413]

theorem rawRowCheck9414 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form6 = rawRow9414 := by decide +kernel

theorem rowCheck9414 : row9414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9414 := by decide +kernel

theorem rowEval9414 (x : Key → ℝ) : Integer.Sparse.eval row9414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9414, Integer.Sparse.eval_collectBalanced, rawRowCheck9414]

theorem rawRowCheck9415 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form6 = rawRow9415 := by decide +kernel

theorem rowCheck9415 : row9415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9415 := by decide +kernel

theorem rowEval9415 (x : Key → ℝ) : Integer.Sparse.eval row9415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9415, Integer.Sparse.eval_collectBalanced, rawRowCheck9415]

theorem rawRowCheck9416 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form6 = rawRow9416 := by decide +kernel

theorem rowCheck9416 : row9416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9416 := by decide +kernel

theorem rowEval9416 (x : Key → ℝ) : Integer.Sparse.eval row9416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9416, Integer.Sparse.eval_collectBalanced, rawRowCheck9416]

theorem rawRowCheck9417 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow9417 := by decide +kernel

theorem rowCheck9417 : row9417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9417 := by decide +kernel

theorem rowEval9417 (x : Key → ℝ) : Integer.Sparse.eval row9417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9417, Integer.Sparse.eval_collectBalanced, rawRowCheck9417]

theorem rawRowCheck9418 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6 = rawRow9418 := by decide +kernel

theorem rowCheck9418 : row9418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9418 := by decide +kernel

theorem rowEval9418 (x : Key → ℝ) : Integer.Sparse.eval row9418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9418, Integer.Sparse.eval_collectBalanced, rawRowCheck9418]

theorem rawRowCheck9419 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6 = rawRow9419 := by decide +kernel

theorem rowCheck9419 : row9419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9419 := by decide +kernel

theorem rowEval9419 (x : Key → ℝ) : Integer.Sparse.eval row9419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9419, Integer.Sparse.eval_collectBalanced, rawRowCheck9419]

theorem rawRowCheck9420 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6 = rawRow9420 := by decide +kernel

theorem rowCheck9420 : row9420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9420 := by decide +kernel

theorem rowEval9420 (x : Key → ℝ) : Integer.Sparse.eval row9420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9420, Integer.Sparse.eval_collectBalanced, rawRowCheck9420]

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

theorem entryCheck15_6 : entry15_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_6 k)) := by decide +kernel

theorem rowsSound15_6 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8709 x
  · exact rowEval8710 x
  · exact rowEval8711 x
  · exact rowEval8712 x
  · exact rowEval9245 x
  · exact rowEval9246 x
  · exact rowEval9247 x
  · exact rowEval9248 x
  · exact rowEval9249 x
  · exact rowEval9250 x
  · exact rowEval9251 x
  · exact rowEval9252 x
  · exact rowEval9253 x
  · exact rowEval9254 x
  · exact rowEval9255 x
  · exact rowEval9256 x

theorem entryEval15_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_6 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck15_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_6]

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

theorem entryCheck16_6 : entry16_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_6 k)) := by decide +kernel

theorem rowsSound16_6 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval9413 x
  · exact rowEval9414 x
  · exact rowEval9415 x
  · exact rowEval9416 x
  · exact rowEval9417 x
  · exact rowEval9418 x
  · exact rowEval9419 x
  · exact rowEval9420 x

theorem entryEval16_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_6 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck16_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_6]

end MUB6.Certificate.GramEntries.Block3

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10449 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form6 = rawRow10449 := by decide +kernel

theorem rowCheck10449 : row10449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10449 := by decide +kernel

theorem rowEval10449 (x : Key → ℝ) : Integer.Sparse.eval row10449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10449, Integer.Sparse.eval_collectBalanced, rawRowCheck10449]

theorem rawRowCheck10450 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form6 = rawRow10450 := by decide +kernel

theorem rowCheck10450 : row10450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10450 := by decide +kernel

theorem rowEval10450 (x : Key → ℝ) : Integer.Sparse.eval row10450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10450, Integer.Sparse.eval_collectBalanced, rawRowCheck10450]

theorem rawRowCheck10451 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form6 = rawRow10451 := by decide +kernel

theorem rowCheck10451 : row10451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10451 := by decide +kernel

theorem rowEval10451 (x : Key → ℝ) : Integer.Sparse.eval row10451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10451, Integer.Sparse.eval_collectBalanced, rawRowCheck10451]

theorem rawRowCheck10452 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form6 = rawRow10452 := by decide +kernel

theorem rowCheck10452 : row10452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10452 := by decide +kernel

theorem rowEval10452 (x : Key → ℝ) : Integer.Sparse.eval row10452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10452, Integer.Sparse.eval_collectBalanced, rawRowCheck10452]

theorem rawRowCheck10453 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form6 = rawRow10453 := by decide +kernel

theorem rowCheck10453 : row10453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10453 := by decide +kernel

theorem rowEval10453 (x : Key → ℝ) : Integer.Sparse.eval row10453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10453, Integer.Sparse.eval_collectBalanced, rawRowCheck10453]

theorem rawRowCheck10454 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form6 = rawRow10454 := by decide +kernel

theorem rowCheck10454 : row10454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10454 := by decide +kernel

theorem rowEval10454 (x : Key → ℝ) : Integer.Sparse.eval row10454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10454, Integer.Sparse.eval_collectBalanced, rawRowCheck10454]

theorem rawRowCheck10455 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form6 = rawRow10455 := by decide +kernel

theorem rowCheck10455 : row10455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10455 := by decide +kernel

theorem rowEval10455 (x : Key → ℝ) : Integer.Sparse.eval row10455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10455, Integer.Sparse.eval_collectBalanced, rawRowCheck10455]

theorem rawRowCheck10456 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form6 = rawRow10456 := by decide +kernel

theorem rowCheck10456 : row10456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10456 := by decide +kernel

theorem rowEval10456 (x : Key → ℝ) : Integer.Sparse.eval row10456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10456, Integer.Sparse.eval_collectBalanced, rawRowCheck10456]

theorem rawRowCheck10457 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form6 = rawRow10457 := by decide +kernel

theorem rowCheck10457 : row10457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10457 := by decide +kernel

theorem rowEval10457 (x : Key → ℝ) : Integer.Sparse.eval row10457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10457, Integer.Sparse.eval_collectBalanced, rawRowCheck10457]

theorem rawRowCheck10458 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form6 = rawRow10458 := by decide +kernel

theorem rowCheck10458 : row10458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10458 := by decide +kernel

theorem rowEval10458 (x : Key → ℝ) : Integer.Sparse.eval row10458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10458, Integer.Sparse.eval_collectBalanced, rawRowCheck10458]

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

theorem rawRowCheck10619 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow10619 := by decide +kernel

theorem rowCheck10619 : row10619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10619 := by decide +kernel

theorem rowEval10619 (x : Key → ℝ) : Integer.Sparse.eval row10619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10619, Integer.Sparse.eval_collectBalanced, rawRowCheck10619]

theorem rawRowCheck10620 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow10620 := by decide +kernel

theorem rowCheck10620 : row10620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10620 := by decide +kernel

theorem rowEval10620 (x : Key → ℝ) : Integer.Sparse.eval row10620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10620, Integer.Sparse.eval_collectBalanced, rawRowCheck10620]

theorem rawRowCheck10621 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow10621 := by decide +kernel

theorem rowCheck10621 : row10621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10621 := by decide +kernel

theorem rowEval10621 (x : Key → ℝ) : Integer.Sparse.eval row10621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10621, Integer.Sparse.eval_collectBalanced, rawRowCheck10621]

theorem rawRowCheck10622 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow10622 := by decide +kernel

theorem rowCheck10622 : row10622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10622 := by decide +kernel

theorem rowEval10622 (x : Key → ℝ) : Integer.Sparse.eval row10622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10622, Integer.Sparse.eval_collectBalanced, rawRowCheck10622]

theorem rawRowCheck10623 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form6 = rawRow10623 := by decide +kernel

theorem rowCheck10623 : row10623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10623 := by decide +kernel

theorem rowEval10623 (x : Key → ℝ) : Integer.Sparse.eval row10623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10623, Integer.Sparse.eval_collectBalanced, rawRowCheck10623]

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

theorem entryCheck19_6 : entry19_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_6 k)) := by decide +kernel

theorem rowsSound19_6 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval10449 x
  · exact rowEval10450 x
  · exact rowEval10451 x
  · exact rowEval10452 x
  · exact rowEval10453 x
  · exact rowEval10454 x
  · exact rowEval10455 x
  · exact rowEval10456 x
  · exact rowEval10457 x
  · exact rowEval10458 x

theorem entryEval19_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_6 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck19_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_6]

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

theorem entryCheck20_6 : entry20_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_6 k)) := by decide +kernel

theorem rowsSound20_6 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval10619 x
  · exact rowEval10620 x
  · exact rowEval10621 x
  · exact rowEval10622 x
  · exact rowEval10623 x

theorem entryEval20_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_6 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck20_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_6]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10910 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form6 = rawRow10910 := by decide +kernel

theorem rowCheck10910 : row10910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10910 := by decide +kernel

theorem rowEval10910 (x : Key → ℝ) : Integer.Sparse.eval row10910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10910, Integer.Sparse.eval_collectBalanced, rawRowCheck10910]

theorem rawRowCheck10911 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form6 = rawRow10911 := by decide +kernel

theorem rowCheck10911 : row10911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10911 := by decide +kernel

theorem rowEval10911 (x : Key → ℝ) : Integer.Sparse.eval row10911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10911, Integer.Sparse.eval_collectBalanced, rawRowCheck10911]

theorem rawRowCheck10912 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form6 = rawRow10912 := by decide +kernel

theorem rowCheck10912 : row10912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10912 := by decide +kernel

theorem rowEval10912 (x : Key → ℝ) : Integer.Sparse.eval row10912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10912, Integer.Sparse.eval_collectBalanced, rawRowCheck10912]

theorem rawRowCheck10913 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form6 = rawRow10913 := by decide +kernel

theorem rowCheck10913 : row10913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10913 := by decide +kernel

theorem rowEval10913 (x : Key → ℝ) : Integer.Sparse.eval row10913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10913, Integer.Sparse.eval_collectBalanced, rawRowCheck10913]

theorem rawRowCheck10914 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form6 = rawRow10914 := by decide +kernel

theorem rowCheck10914 : row10914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10914 := by decide +kernel

theorem rowEval10914 (x : Key → ℝ) : Integer.Sparse.eval row10914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10914, Integer.Sparse.eval_collectBalanced, rawRowCheck10914]

theorem rawRowCheck10915 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form6 = rawRow10915 := by decide +kernel

theorem rowCheck10915 : row10915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10915 := by decide +kernel

theorem rowEval10915 (x : Key → ℝ) : Integer.Sparse.eval row10915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10915, Integer.Sparse.eval_collectBalanced, rawRowCheck10915]

theorem rawRowCheck10916 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form6 = rawRow10916 := by decide +kernel

theorem rowCheck10916 : row10916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10916 := by decide +kernel

theorem rowEval10916 (x : Key → ℝ) : Integer.Sparse.eval row10916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10916, Integer.Sparse.eval_collectBalanced, rawRowCheck10916]

theorem rawRowCheck10917 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form6 = rawRow10917 := by decide +kernel

theorem rowCheck10917 : row10917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10917 := by decide +kernel

theorem rowEval10917 (x : Key → ℝ) : Integer.Sparse.eval row10917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10917, Integer.Sparse.eval_collectBalanced, rawRowCheck10917]

theorem rawRowCheck10918 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form6 = rawRow10918 := by decide +kernel

theorem rowCheck10918 : row10918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10918 := by decide +kernel

theorem rowEval10918 (x : Key → ℝ) : Integer.Sparse.eval row10918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10918, Integer.Sparse.eval_collectBalanced, rawRowCheck10918]

theorem rawRowCheck10919 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form6 = rawRow10919 := by decide +kernel

theorem rowCheck10919 : row10919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10919 := by decide +kernel

theorem rowEval10919 (x : Key → ℝ) : Integer.Sparse.eval row10919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10919, Integer.Sparse.eval_collectBalanced, rawRowCheck10919]

theorem rawRowCheck10920 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form6 = rawRow10920 := by decide +kernel

theorem rowCheck10920 : row10920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10920 := by decide +kernel

theorem rowEval10920 (x : Key → ℝ) : Integer.Sparse.eval row10920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10920, Integer.Sparse.eval_collectBalanced, rawRowCheck10920]

theorem rawRowCheck10921 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form6 = rawRow10921 := by decide +kernel

theorem rowCheck10921 : row10921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10921 := by decide +kernel

theorem rowEval10921 (x : Key → ℝ) : Integer.Sparse.eval row10921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10921, Integer.Sparse.eval_collectBalanced, rawRowCheck10921]

theorem rawRowCheck10922 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form6 = rawRow10922 := by decide +kernel

theorem rowCheck10922 : row10922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10922 := by decide +kernel

theorem rowEval10922 (x : Key → ℝ) : Integer.Sparse.eval row10922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10922, Integer.Sparse.eval_collectBalanced, rawRowCheck10922]

theorem rawRowCheck10923 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form6 = rawRow10923 := by decide +kernel

theorem rowCheck10923 : row10923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10923 := by decide +kernel

theorem rowEval10923 (x : Key → ℝ) : Integer.Sparse.eval row10923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10923, Integer.Sparse.eval_collectBalanced, rawRowCheck10923]

theorem rawRowCheck10924 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form6 = rawRow10924 := by decide +kernel

theorem rowCheck10924 : row10924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10924 := by decide +kernel

theorem rowEval10924 (x : Key → ℝ) : Integer.Sparse.eval row10924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10924, Integer.Sparse.eval_collectBalanced, rawRowCheck10924]

theorem rawRowCheck10925 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form6 = rawRow10925 := by decide +kernel

theorem rowCheck10925 : row10925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10925 := by decide +kernel

theorem rowEval10925 (x : Key → ℝ) : Integer.Sparse.eval row10925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10925, Integer.Sparse.eval_collectBalanced, rawRowCheck10925]

theorem rawRowCheck10926 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form6 = rawRow10926 := by decide +kernel

theorem rowCheck10926 : row10926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10926 := by decide +kernel

theorem rowEval10926 (x : Key → ℝ) : Integer.Sparse.eval row10926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10926, Integer.Sparse.eval_collectBalanced, rawRowCheck10926]

theorem rawRowCheck10927 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form6 = rawRow10927 := by decide +kernel

theorem rowCheck10927 : row10927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10927 := by decide +kernel

theorem rowEval10927 (x : Key → ℝ) : Integer.Sparse.eval row10927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10927, Integer.Sparse.eval_collectBalanced, rawRowCheck10927]

theorem rawRowCheck10928 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form6 = rawRow10928 := by decide +kernel

theorem rowCheck10928 : row10928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10928 := by decide +kernel

theorem rowEval10928 (x : Key → ℝ) : Integer.Sparse.eval row10928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10928, Integer.Sparse.eval_collectBalanced, rawRowCheck10928]

theorem rawRowCheck10929 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form6 = rawRow10929 := by decide +kernel

theorem rowCheck10929 : row10929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10929 := by decide +kernel

theorem rowEval10929 (x : Key → ℝ) : Integer.Sparse.eval row10929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10929, Integer.Sparse.eval_collectBalanced, rawRowCheck10929]

theorem rawRowCheck10930 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form6 = rawRow10930 := by decide +kernel

theorem rowCheck10930 : row10930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10930 := by decide +kernel

theorem rowEval10930 (x : Key → ℝ) : Integer.Sparse.eval row10930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10930, Integer.Sparse.eval_collectBalanced, rawRowCheck10930]

theorem rawRowCheck10931 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form6 = rawRow10931 := by decide +kernel

theorem rowCheck10931 : row10931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10931 := by decide +kernel

theorem rowEval10931 (x : Key → ℝ) : Integer.Sparse.eval row10931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10931, Integer.Sparse.eval_collectBalanced, rawRowCheck10931]

theorem rawRowCheck10932 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form6 = rawRow10932 := by decide +kernel

theorem rowCheck10932 : row10932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10932 := by decide +kernel

theorem rowEval10932 (x : Key → ℝ) : Integer.Sparse.eval row10932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10932, Integer.Sparse.eval_collectBalanced, rawRowCheck10932]

theorem rawRowCheck10933 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form6 = rawRow10933 := by decide +kernel

theorem rowCheck10933 : row10933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10933 := by decide +kernel

theorem rowEval10933 (x : Key → ℝ) : Integer.Sparse.eval row10933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10933, Integer.Sparse.eval_collectBalanced, rawRowCheck10933]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11558 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form6 = rawRow11558 := by decide +kernel

theorem rowCheck11558 : row11558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11558 := by decide +kernel

theorem rowEval11558 (x : Key → ℝ) : Integer.Sparse.eval row11558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11558, Integer.Sparse.eval_collectBalanced, rawRowCheck11558]

theorem rawRowCheck11559 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form6 = rawRow11559 := by decide +kernel

theorem rowCheck11559 : row11559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11559 := by decide +kernel

theorem rowEval11559 (x : Key → ℝ) : Integer.Sparse.eval row11559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11559, Integer.Sparse.eval_collectBalanced, rawRowCheck11559]

theorem rawRowCheck11560 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form6 = rawRow11560 := by decide +kernel

theorem rowCheck11560 : row11560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11560 := by decide +kernel

theorem rowEval11560 (x : Key → ℝ) : Integer.Sparse.eval row11560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11560, Integer.Sparse.eval_collectBalanced, rawRowCheck11560]

theorem rawRowCheck11561 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form6 = rawRow11561 := by decide +kernel

theorem rowCheck11561 : row11561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11561 := by decide +kernel

theorem rowEval11561 (x : Key → ℝ) : Integer.Sparse.eval row11561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11561, Integer.Sparse.eval_collectBalanced, rawRowCheck11561]

theorem rawRowCheck11562 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form6 = rawRow11562 := by decide +kernel

theorem rowCheck11562 : row11562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11562 := by decide +kernel

theorem rowEval11562 (x : Key → ℝ) : Integer.Sparse.eval row11562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11562, Integer.Sparse.eval_collectBalanced, rawRowCheck11562]

theorem rawRowCheck11563 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form6 = rawRow11563 := by decide +kernel

theorem rowCheck11563 : row11563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11563 := by decide +kernel

theorem rowEval11563 (x : Key → ℝ) : Integer.Sparse.eval row11563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11563, Integer.Sparse.eval_collectBalanced, rawRowCheck11563]

theorem rawRowCheck11564 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form6 = rawRow11564 := by decide +kernel

theorem rowCheck11564 : row11564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11564 := by decide +kernel

theorem rowEval11564 (x : Key → ℝ) : Integer.Sparse.eval row11564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11564, Integer.Sparse.eval_collectBalanced, rawRowCheck11564]

theorem rawRowCheck11565 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form6 = rawRow11565 := by decide +kernel

theorem rowCheck11565 : row11565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11565 := by decide +kernel

theorem rowEval11565 (x : Key → ℝ) : Integer.Sparse.eval row11565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11565, Integer.Sparse.eval_collectBalanced, rawRowCheck11565]

theorem rawRowCheck11566 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form6 = rawRow11566 := by decide +kernel

theorem rowCheck11566 : row11566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11566 := by decide +kernel

theorem rowEval11566 (x : Key → ℝ) : Integer.Sparse.eval row11566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11566, Integer.Sparse.eval_collectBalanced, rawRowCheck11566]

theorem rawRowCheck11567 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow11567 := by decide +kernel

theorem rowCheck11567 : row11567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11567 := by decide +kernel

theorem rowEval11567 (x : Key → ℝ) : Integer.Sparse.eval row11567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11567, Integer.Sparse.eval_collectBalanced, rawRowCheck11567]

theorem rawRowCheck11568 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow11568 := by decide +kernel

theorem rowCheck11568 : row11568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11568 := by decide +kernel

theorem rowEval11568 (x : Key → ℝ) : Integer.Sparse.eval row11568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11568, Integer.Sparse.eval_collectBalanced, rawRowCheck11568]

theorem rawRowCheck11569 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow11569 := by decide +kernel

theorem rowCheck11569 : row11569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11569 := by decide +kernel

theorem rowEval11569 (x : Key → ℝ) : Integer.Sparse.eval row11569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11569, Integer.Sparse.eval_collectBalanced, rawRowCheck11569]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck11882 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form6 = rawRow11882 := by decide +kernel

theorem rowCheck11882 : row11882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11882 := by decide +kernel

theorem rowEval11882 (x : Key → ℝ) : Integer.Sparse.eval row11882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11882, Integer.Sparse.eval_collectBalanced, rawRowCheck11882]

theorem rawRowCheck11883 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form6 = rawRow11883 := by decide +kernel

theorem rowCheck11883 : row11883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11883 := by decide +kernel

theorem rowEval11883 (x : Key → ℝ) : Integer.Sparse.eval row11883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11883, Integer.Sparse.eval_collectBalanced, rawRowCheck11883]

theorem rawRowCheck11884 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form6 = rawRow11884 := by decide +kernel

theorem rowCheck11884 : row11884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11884 := by decide +kernel

theorem rowEval11884 (x : Key → ℝ) : Integer.Sparse.eval row11884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11884, Integer.Sparse.eval_collectBalanced, rawRowCheck11884]

theorem rawRowCheck11885 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form6 = rawRow11885 := by decide +kernel

theorem rowCheck11885 : row11885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11885 := by decide +kernel

theorem rowEval11885 (x : Key → ℝ) : Integer.Sparse.eval row11885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11885, Integer.Sparse.eval_collectBalanced, rawRowCheck11885]

theorem rawRowCheck11886 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form6 = rawRow11886 := by decide +kernel

theorem rowCheck11886 : row11886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11886 := by decide +kernel

theorem rowEval11886 (x : Key → ℝ) : Integer.Sparse.eval row11886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11886, Integer.Sparse.eval_collectBalanced, rawRowCheck11886]

theorem rawRowCheck11887 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form6 = rawRow11887 := by decide +kernel

theorem rowCheck11887 : row11887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11887 := by decide +kernel

theorem rowEval11887 (x : Key → ℝ) : Integer.Sparse.eval row11887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11887, Integer.Sparse.eval_collectBalanced, rawRowCheck11887]

theorem rawRowCheck11888 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6 = rawRow11888 := by decide +kernel

theorem rowCheck11888 : row11888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11888 := by decide +kernel

theorem rowEval11888 (x : Key → ℝ) : Integer.Sparse.eval row11888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11888, Integer.Sparse.eval_collectBalanced, rawRowCheck11888]

theorem rawRowCheck11889 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6 = rawRow11889 := by decide +kernel

theorem rowCheck11889 : row11889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11889 := by decide +kernel

theorem rowEval11889 (x : Key → ℝ) : Integer.Sparse.eval row11889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11889, Integer.Sparse.eval_collectBalanced, rawRowCheck11889]

theorem rawRowCheck11890 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6 = rawRow11890 := by decide +kernel

theorem rowCheck11890 : row11890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11890 := by decide +kernel

theorem rowEval11890 (x : Key → ℝ) : Integer.Sparse.eval row11890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11890, Integer.Sparse.eval_collectBalanced, rawRowCheck11890]

theorem rawRowCheck11891 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6 = rawRow11891 := by decide +kernel

theorem rowCheck11891 : row11891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11891 := by decide +kernel

theorem rowEval11891 (x : Key → ℝ) : Integer.Sparse.eval row11891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11891, Integer.Sparse.eval_collectBalanced, rawRowCheck11891]

theorem rawRowCheck11892 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6 = rawRow11892 := by decide +kernel

theorem rowCheck11892 : row11892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11892 := by decide +kernel

theorem rowEval11892 (x : Key → ℝ) : Integer.Sparse.eval row11892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11892, Integer.Sparse.eval_collectBalanced, rawRowCheck11892]

theorem rawRowCheck11893 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6 = rawRow11893 := by decide +kernel

theorem rowCheck11893 : row11893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11893 := by decide +kernel

theorem rowEval11893 (x : Key → ℝ) : Integer.Sparse.eval row11893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11893, Integer.Sparse.eval_collectBalanced, rawRowCheck11893]

theorem rawRowCheck11894 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6 = rawRow11894 := by decide +kernel

theorem rowCheck11894 : row11894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11894 := by decide +kernel

theorem rowEval11894 (x : Key → ℝ) : Integer.Sparse.eval row11894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11894, Integer.Sparse.eval_collectBalanced, rawRowCheck11894]

theorem rawRowCheck11895 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6 = rawRow11895 := by decide +kernel

theorem rowCheck11895 : row11895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11895 := by decide +kernel

theorem rowEval11895 (x : Key → ℝ) : Integer.Sparse.eval row11895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11895, Integer.Sparse.eval_collectBalanced, rawRowCheck11895]

theorem rawRowCheck11896 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6 = rawRow11896 := by decide +kernel

theorem rowCheck11896 : row11896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11896 := by decide +kernel

theorem rowEval11896 (x : Key → ℝ) : Integer.Sparse.eval row11896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11896, Integer.Sparse.eval_collectBalanced, rawRowCheck11896]

theorem rawRowCheck11897 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6 = rawRow11897 := by decide +kernel

theorem rowCheck11897 : row11897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11897 := by decide +kernel

theorem rowEval11897 (x : Key → ℝ) : Integer.Sparse.eval row11897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11897, Integer.Sparse.eval_collectBalanced, rawRowCheck11897]

theorem rawRowCheck11898 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6 = rawRow11898 := by decide +kernel

theorem rowCheck11898 : row11898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11898 := by decide +kernel

theorem rowEval11898 (x : Key → ℝ) : Integer.Sparse.eval row11898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11898, Integer.Sparse.eval_collectBalanced, rawRowCheck11898]

theorem rawRowCheck11899 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6 = rawRow11899 := by decide +kernel

theorem rowCheck11899 : row11899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11899 := by decide +kernel

theorem rowEval11899 (x : Key → ℝ) : Integer.Sparse.eval row11899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck11899, Integer.Sparse.eval_collectBalanced, rawRowCheck11899]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck22_6 : entry22_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_6 k)) := by decide +kernel

theorem rowsSound22_6 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval11558 x
  · exact rowEval11559 x
  · exact rowEval11560 x
  · exact rowEval11561 x
  · exact rowEval11562 x
  · exact rowEval11563 x
  · exact rowEval11564 x
  · exact rowEval11565 x
  · exact rowEval11566 x
  · exact rowEval11567 x
  · exact rowEval11568 x
  · exact rowEval11569 x
  · exact rowEval10910 x
  · exact rowEval10911 x
  · exact rowEval10912 x
  · exact rowEval10913 x
  · exact rowEval10914 x
  · exact rowEval10915 x
  · exact rowEval10916 x
  · exact rowEval10917 x
  · exact rowEval10918 x
  · exact rowEval10919 x
  · exact rowEval10920 x
  · exact rowEval10921 x
  · exact rowEval10922 x
  · exact rowEval10923 x
  · exact rowEval10924 x
  · exact rowEval10925 x
  · exact rowEval10926 x
  · exact rowEval10927 x
  · exact rowEval10928 x
  · exact rowEval10929 x
  · exact rowEval10930 x
  · exact rowEval10931 x
  · exact rowEval10932 x
  · exact rowEval10933 x

theorem entryEval22_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_6 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck22_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_6]

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

theorem rawRowCheck12236 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form6 = rawRow12236 := by decide +kernel

theorem rowCheck12236 : row12236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12236 := by decide +kernel

theorem rowEval12236 (x : Key → ℝ) : Integer.Sparse.eval row12236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12236, Integer.Sparse.eval_collectBalanced, rawRowCheck12236]

theorem rawRowCheck12237 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow12237 := by decide +kernel

theorem rowCheck12237 : row12237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12237 := by decide +kernel

theorem rowEval12237 (x : Key → ℝ) : Integer.Sparse.eval row12237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12237, Integer.Sparse.eval_collectBalanced, rawRowCheck12237]

theorem rawRowCheck12238 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form6 = rawRow12238 := by decide +kernel

theorem rowCheck12238 : row12238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12238 := by decide +kernel

theorem rowEval12238 (x : Key → ℝ) : Integer.Sparse.eval row12238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12238, Integer.Sparse.eval_collectBalanced, rawRowCheck12238]

theorem rawRowCheck12239 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form6 = rawRow12239 := by decide +kernel

theorem rowCheck12239 : row12239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12239 := by decide +kernel

theorem rowEval12239 (x : Key → ℝ) : Integer.Sparse.eval row12239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12239, Integer.Sparse.eval_collectBalanced, rawRowCheck12239]

theorem rawRowCheck12240 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form6 = rawRow12240 := by decide +kernel

theorem rowCheck12240 : row12240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12240 := by decide +kernel

theorem rowEval12240 (x : Key → ℝ) : Integer.Sparse.eval row12240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12240, Integer.Sparse.eval_collectBalanced, rawRowCheck12240]

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

theorem entryCheck23_6 : entry23_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_6 k)) := by decide +kernel

theorem rowsSound23_6 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval11882 x
  · exact rowEval11883 x
  · exact rowEval11884 x
  · exact rowEval11885 x
  · exact rowEval11886 x
  · exact rowEval11887 x
  · exact rowEval11888 x
  · exact rowEval11889 x
  · exact rowEval11890 x
  · exact rowEval11891 x
  · exact rowEval11892 x
  · exact rowEval11893 x
  · exact rowEval11894 x
  · exact rowEval11895 x
  · exact rowEval11896 x
  · exact rowEval11897 x
  · exact rowEval11898 x
  · exact rowEval11899 x

theorem entryEval23_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_6 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck23_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_6]

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

theorem rawRowCheck12379 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form6 = rawRow12379 := by decide +kernel

theorem rowCheck12379 : row12379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12379 := by decide +kernel

theorem rowEval12379 (x : Key → ℝ) : Integer.Sparse.eval row12379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12379, Integer.Sparse.eval_collectBalanced, rawRowCheck12379]

theorem rawRowCheck12380 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form6 = rawRow12380 := by decide +kernel

theorem rowCheck12380 : row12380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12380 := by decide +kernel

theorem rowEval12380 (x : Key → ℝ) : Integer.Sparse.eval row12380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12380, Integer.Sparse.eval_collectBalanced, rawRowCheck12380]

theorem rawRowCheck12381 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form6 = rawRow12381 := by decide +kernel

theorem rowCheck12381 : row12381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12381 := by decide +kernel

theorem rowEval12381 (x : Key → ℝ) : Integer.Sparse.eval row12381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12381, Integer.Sparse.eval_collectBalanced, rawRowCheck12381]

theorem rawRowCheck12382 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form6 = rawRow12382 := by decide +kernel

theorem rowCheck12382 : row12382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12382 := by decide +kernel

theorem rowEval12382 (x : Key → ℝ) : Integer.Sparse.eval row12382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12382, Integer.Sparse.eval_collectBalanced, rawRowCheck12382]

theorem rawRowCheck12383 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form6 = rawRow12383 := by decide +kernel

theorem rowCheck12383 : row12383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12383 := by decide +kernel

theorem rowEval12383 (x : Key → ℝ) : Integer.Sparse.eval row12383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12383, Integer.Sparse.eval_collectBalanced, rawRowCheck12383]

theorem rawRowCheck12384 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form6 = rawRow12384 := by decide +kernel

theorem rowCheck12384 : row12384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12384 := by decide +kernel

theorem rowEval12384 (x : Key → ℝ) : Integer.Sparse.eval row12384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12384, Integer.Sparse.eval_collectBalanced, rawRowCheck12384]

theorem rawRowCheck12385 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form6 = rawRow12385 := by decide +kernel

theorem rowCheck12385 : row12385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12385 := by decide +kernel

theorem rowEval12385 (x : Key → ℝ) : Integer.Sparse.eval row12385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12385, Integer.Sparse.eval_collectBalanced, rawRowCheck12385]

theorem rawRowCheck12386 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form6 = rawRow12386 := by decide +kernel

theorem rowCheck12386 : row12386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12386 := by decide +kernel

theorem rowEval12386 (x : Key → ℝ) : Integer.Sparse.eval row12386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12386, Integer.Sparse.eval_collectBalanced, rawRowCheck12386]

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

theorem entryCheck24_6 : entry24_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_6 k)) := by decide +kernel

theorem rowsSound24_6 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval12236 x
  · exact rowEval12237 x
  · exact rowEval12238 x
  · exact rowEval12239 x
  · exact rowEval12240 x

theorem entryEval24_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_6 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck24_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_6]

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

theorem entryCheck25_6 : entry25_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_6 k)) := by decide +kernel

theorem rowsSound25_6 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval12379 x
  · exact rowEval12380 x
  · exact rowEval12381 x
  · exact rowEval12382 x
  · exact rowEval12383 x
  · exact rowEval12384 x
  · exact rowEval12385 x
  · exact rowEval12386 x

theorem entryEval25_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_6 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck25_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_6]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12683 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form6 = rawRow12683 := by decide +kernel

theorem rowCheck12683 : row12683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12683 := by decide +kernel

theorem rowEval12683 (x : Key → ℝ) : Integer.Sparse.eval row12683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12683, Integer.Sparse.eval_collectBalanced, rawRowCheck12683]

theorem rawRowCheck12684 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form6 = rawRow12684 := by decide +kernel

theorem rowCheck12684 : row12684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12684 := by decide +kernel

theorem rowEval12684 (x : Key → ℝ) : Integer.Sparse.eval row12684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12684, Integer.Sparse.eval_collectBalanced, rawRowCheck12684]

theorem rawRowCheck12685 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form6 = rawRow12685 := by decide +kernel

theorem rowCheck12685 : row12685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12685 := by decide +kernel

theorem rowEval12685 (x : Key → ℝ) : Integer.Sparse.eval row12685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12685, Integer.Sparse.eval_collectBalanced, rawRowCheck12685]

theorem rawRowCheck12686 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form6 = rawRow12686 := by decide +kernel

theorem rowCheck12686 : row12686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12686 := by decide +kernel

theorem rowEval12686 (x : Key → ℝ) : Integer.Sparse.eval row12686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12686, Integer.Sparse.eval_collectBalanced, rawRowCheck12686]

theorem rawRowCheck12687 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form6 = rawRow12687 := by decide +kernel

theorem rowCheck12687 : row12687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12687 := by decide +kernel

theorem rowEval12687 (x : Key → ℝ) : Integer.Sparse.eval row12687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12687, Integer.Sparse.eval_collectBalanced, rawRowCheck12687]

theorem rawRowCheck12688 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form6 = rawRow12688 := by decide +kernel

theorem rowCheck12688 : row12688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12688 := by decide +kernel

theorem rowEval12688 (x : Key → ℝ) : Integer.Sparse.eval row12688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12688, Integer.Sparse.eval_collectBalanced, rawRowCheck12688]

theorem rawRowCheck12689 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form6 = rawRow12689 := by decide +kernel

theorem rowCheck12689 : row12689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12689 := by decide +kernel

theorem rowEval12689 (x : Key → ℝ) : Integer.Sparse.eval row12689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12689, Integer.Sparse.eval_collectBalanced, rawRowCheck12689]

theorem rawRowCheck12690 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form6 = rawRow12690 := by decide +kernel

theorem rowCheck12690 : row12690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12690 := by decide +kernel

theorem rowEval12690 (x : Key → ℝ) : Integer.Sparse.eval row12690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12690, Integer.Sparse.eval_collectBalanced, rawRowCheck12690]

theorem rawRowCheck12691 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form6 = rawRow12691 := by decide +kernel

theorem rowCheck12691 : row12691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12691 := by decide +kernel

theorem rowEval12691 (x : Key → ℝ) : Integer.Sparse.eval row12691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12691, Integer.Sparse.eval_collectBalanced, rawRowCheck12691]

theorem rawRowCheck12692 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form6 = rawRow12692 := by decide +kernel

theorem rowCheck12692 : row12692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12692 := by decide +kernel

theorem rowEval12692 (x : Key → ℝ) : Integer.Sparse.eval row12692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12692, Integer.Sparse.eval_collectBalanced, rawRowCheck12692]

theorem rawRowCheck12693 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form6 = rawRow12693 := by decide +kernel

theorem rowCheck12693 : row12693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12693 := by decide +kernel

theorem rowEval12693 (x : Key → ℝ) : Integer.Sparse.eval row12693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12693, Integer.Sparse.eval_collectBalanced, rawRowCheck12693]

theorem rawRowCheck12694 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form6 = rawRow12694 := by decide +kernel

theorem rowCheck12694 : row12694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12694 := by decide +kernel

theorem rowEval12694 (x : Key → ℝ) : Integer.Sparse.eval row12694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12694, Integer.Sparse.eval_collectBalanced, rawRowCheck12694]

theorem rawRowCheck12695 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form6 = rawRow12695 := by decide +kernel

theorem rowCheck12695 : row12695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12695 := by decide +kernel

theorem rowEval12695 (x : Key → ℝ) : Integer.Sparse.eval row12695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12695, Integer.Sparse.eval_collectBalanced, rawRowCheck12695]

theorem rawRowCheck12696 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form6 = rawRow12696 := by decide +kernel

theorem rowCheck12696 : row12696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12696 := by decide +kernel

theorem rowEval12696 (x : Key → ℝ) : Integer.Sparse.eval row12696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12696, Integer.Sparse.eval_collectBalanced, rawRowCheck12696]

theorem rawRowCheck12697 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form6 = rawRow12697 := by decide +kernel

theorem rowCheck12697 : row12697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12697 := by decide +kernel

theorem rowEval12697 (x : Key → ℝ) : Integer.Sparse.eval row12697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12697, Integer.Sparse.eval_collectBalanced, rawRowCheck12697]

theorem rawRowCheck12698 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form6 = rawRow12698 := by decide +kernel

theorem rowCheck12698 : row12698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12698 := by decide +kernel

theorem rowEval12698 (x : Key → ℝ) : Integer.Sparse.eval row12698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12698, Integer.Sparse.eval_collectBalanced, rawRowCheck12698]

theorem rawRowCheck12699 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form6 = rawRow12699 := by decide +kernel

theorem rowCheck12699 : row12699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12699 := by decide +kernel

theorem rowEval12699 (x : Key → ℝ) : Integer.Sparse.eval row12699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12699, Integer.Sparse.eval_collectBalanced, rawRowCheck12699]

theorem rawRowCheck12700 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form6 = rawRow12700 := by decide +kernel

theorem rowCheck12700 : row12700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12700 := by decide +kernel

theorem rowEval12700 (x : Key → ℝ) : Integer.Sparse.eval row12700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12700, Integer.Sparse.eval_collectBalanced, rawRowCheck12700]

theorem rawRowCheck12701 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form6 = rawRow12701 := by decide +kernel

theorem rowCheck12701 : row12701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12701 := by decide +kernel

theorem rowEval12701 (x : Key → ℝ) : Integer.Sparse.eval row12701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12701, Integer.Sparse.eval_collectBalanced, rawRowCheck12701]

theorem rawRowCheck12702 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form6 = rawRow12702 := by decide +kernel

theorem rowCheck12702 : row12702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12702 := by decide +kernel

theorem rowEval12702 (x : Key → ℝ) : Integer.Sparse.eval row12702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12702, Integer.Sparse.eval_collectBalanced, rawRowCheck12702]

theorem rawRowCheck12703 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form6 = rawRow12703 := by decide +kernel

theorem rowCheck12703 : row12703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12703 := by decide +kernel

theorem rowEval12703 (x : Key → ℝ) : Integer.Sparse.eval row12703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12703, Integer.Sparse.eval_collectBalanced, rawRowCheck12703]

theorem rawRowCheck12704 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow12704 := by decide +kernel

theorem rowCheck12704 : row12704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12704 := by decide +kernel

theorem rowEval12704 (x : Key → ℝ) : Integer.Sparse.eval row12704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12704, Integer.Sparse.eval_collectBalanced, rawRowCheck12704]

theorem rawRowCheck12705 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow12705 := by decide +kernel

theorem rowCheck12705 : row12705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12705 := by decide +kernel

theorem rowEval12705 (x : Key → ℝ) : Integer.Sparse.eval row12705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12705, Integer.Sparse.eval_collectBalanced, rawRowCheck12705]

theorem rawRowCheck12706 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow12706 := by decide +kernel

theorem rowCheck12706 : row12706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12706 := by decide +kernel

theorem rowEval12706 (x : Key → ℝ) : Integer.Sparse.eval row12706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12706, Integer.Sparse.eval_collectBalanced, rawRowCheck12706]

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

theorem entryCheck26_6 : entry26_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_6 k)) := by decide +kernel

theorem rowsSound26_6 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval12683 x
  · exact rowEval12684 x
  · exact rowEval12685 x
  · exact rowEval12686 x
  · exact rowEval12687 x
  · exact rowEval12688 x
  · exact rowEval12689 x
  · exact rowEval12690 x
  · exact rowEval12691 x
  · exact rowEval12692 x
  · exact rowEval12693 x
  · exact rowEval12694 x
  · exact rowEval12695 x
  · exact rowEval12696 x
  · exact rowEval12697 x
  · exact rowEval12698 x
  · exact rowEval12699 x
  · exact rowEval12700 x
  · exact rowEval12701 x
  · exact rowEval12702 x
  · exact rowEval12703 x
  · exact rowEval12704 x
  · exact rowEval12705 x
  · exact rowEval12706 x

theorem entryEval26_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_6 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck26_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_6]

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

theorem rawRowCheck7795 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7795 := by decide +kernel

theorem rowCheck7795 : row7795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7795 := by decide +kernel

theorem rowEval7795 (x : Key → ℝ) : Integer.Sparse.eval row7795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7795, Integer.Sparse.eval_collectBalanced, rawRowCheck7795]

theorem rawRowCheck7796 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7796 := by decide +kernel

theorem rowCheck7796 : row7796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7796 := by decide +kernel

theorem rowEval7796 (x : Key → ℝ) : Integer.Sparse.eval row7796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7796, Integer.Sparse.eval_collectBalanced, rawRowCheck7796]

theorem rawRowCheck7797 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7797 := by decide +kernel

theorem rowCheck7797 : row7797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7797 := by decide +kernel

theorem rowEval7797 (x : Key → ℝ) : Integer.Sparse.eval row7797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7797, Integer.Sparse.eval_collectBalanced, rawRowCheck7797]

theorem rawRowCheck7798 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7798 := by decide +kernel

theorem rowCheck7798 : row7798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7798 := by decide +kernel

theorem rowEval7798 (x : Key → ℝ) : Integer.Sparse.eval row7798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7798, Integer.Sparse.eval_collectBalanced, rawRowCheck7798]

theorem rawRowCheck7799 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7799 := by decide +kernel

theorem rowCheck7799 : row7799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7799 := by decide +kernel

theorem rowEval7799 (x : Key → ℝ) : Integer.Sparse.eval row7799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7799, Integer.Sparse.eval_collectBalanced, rawRowCheck7799]

theorem rawRowCheck7800 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7800 := by decide +kernel

theorem rowCheck7800 : row7800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7800 := by decide +kernel

theorem rowEval7800 (x : Key → ℝ) : Integer.Sparse.eval row7800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7800, Integer.Sparse.eval_collectBalanced, rawRowCheck7800]

theorem rawRowCheck7801 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7801 := by decide +kernel

theorem rowCheck7801 : row7801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7801 := by decide +kernel

theorem rowEval7801 (x : Key → ℝ) : Integer.Sparse.eval row7801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7801, Integer.Sparse.eval_collectBalanced, rawRowCheck7801]

theorem rawRowCheck7802 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow7802 := by decide +kernel

theorem rowCheck7802 : row7802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7802 := by decide +kernel

theorem rowEval7802 (x : Key → ℝ) : Integer.Sparse.eval row7802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7802, Integer.Sparse.eval_collectBalanced, rawRowCheck7802]

theorem rawRowCheck7803 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow7803 := by decide +kernel

theorem rowCheck7803 : row7803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7803 := by decide +kernel

theorem rowEval7803 (x : Key → ℝ) : Integer.Sparse.eval row7803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7803, Integer.Sparse.eval_collectBalanced, rawRowCheck7803]

theorem rawRowCheck7804 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow7804 := by decide +kernel

theorem rowCheck7804 : row7804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7804 := by decide +kernel

theorem rowEval7804 (x : Key → ℝ) : Integer.Sparse.eval row7804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7804, Integer.Sparse.eval_collectBalanced, rawRowCheck7804]

theorem rawRowCheck7805 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7805 := by decide +kernel

theorem rowCheck7805 : row7805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7805 := by decide +kernel

theorem rowEval7805 (x : Key → ℝ) : Integer.Sparse.eval row7805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7805, Integer.Sparse.eval_collectBalanced, rawRowCheck7805]

theorem rawRowCheck7806 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7806 := by decide +kernel

theorem rowCheck7806 : row7806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7806 := by decide +kernel

theorem rowEval7806 (x : Key → ℝ) : Integer.Sparse.eval row7806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7806, Integer.Sparse.eval_collectBalanced, rawRowCheck7806]

theorem rawRowCheck7807 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow7807 := by decide +kernel

theorem rowCheck7807 : row7807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7807 := by decide +kernel

theorem rowEval7807 (x : Key → ℝ) : Integer.Sparse.eval row7807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7807, Integer.Sparse.eval_collectBalanced, rawRowCheck7807]

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

theorem rawRowCheck7808 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow7808 := by decide +kernel

theorem rowCheck7808 : row7808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7808 := by decide +kernel

theorem rowEval7808 (x : Key → ℝ) : Integer.Sparse.eval row7808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7808, Integer.Sparse.eval_collectBalanced, rawRowCheck7808]

theorem rawRowCheck7809 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow7809 := by decide +kernel

theorem rowCheck7809 : row7809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7809 := by decide +kernel

theorem rowEval7809 (x : Key → ℝ) : Integer.Sparse.eval row7809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7809, Integer.Sparse.eval_collectBalanced, rawRowCheck7809]

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

theorem rawRowCheck7815 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form5 = rawRow7815 := by decide +kernel

theorem rowCheck7815 : row7815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7815 := by decide +kernel

theorem rowEval7815 (x : Key → ℝ) : Integer.Sparse.eval row7815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7815, Integer.Sparse.eval_collectBalanced, rawRowCheck7815]

theorem rawRowCheck7816 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form5 = rawRow7816 := by decide +kernel

theorem rowCheck7816 : row7816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7816 := by decide +kernel

theorem rowEval7816 (x : Key → ℝ) : Integer.Sparse.eval row7816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7816, Integer.Sparse.eval_collectBalanced, rawRowCheck7816]

theorem rawRowCheck7817 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form5 = rawRow7817 := by decide +kernel

theorem rowCheck7817 : row7817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7817 := by decide +kernel

theorem rowEval7817 (x : Key → ℝ) : Integer.Sparse.eval row7817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7817, Integer.Sparse.eval_collectBalanced, rawRowCheck7817]

theorem rawRowCheck7818 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form5 = rawRow7818 := by decide +kernel

theorem rowCheck7818 : row7818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7818 := by decide +kernel

theorem rowEval7818 (x : Key → ℝ) : Integer.Sparse.eval row7818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7818, Integer.Sparse.eval_collectBalanced, rawRowCheck7818]

theorem rawRowCheck7819 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form5 = rawRow7819 := by decide +kernel

theorem rowCheck7819 : row7819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7819 := by decide +kernel

theorem rowEval7819 (x : Key → ℝ) : Integer.Sparse.eval row7819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck7819, Integer.Sparse.eval_collectBalanced, rawRowCheck7819]

theorem rawRowCheck7820 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form6 = rawRow7820 := by decide +kernel

theorem rowCheck7820 : row7820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7820 := by decide +kernel

theorem rowEval7820 (x : Key → ℝ) : Integer.Sparse.eval row7820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7820, Integer.Sparse.eval_collectBalanced, rawRowCheck7820]

theorem rawRowCheck7821 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form6 = rawRow7821 := by decide +kernel

theorem rowCheck7821 : row7821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7821 := by decide +kernel

theorem rowEval7821 (x : Key → ℝ) : Integer.Sparse.eval row7821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7821, Integer.Sparse.eval_collectBalanced, rawRowCheck7821]

theorem rawRowCheck7822 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form6 = rawRow7822 := by decide +kernel

theorem rowCheck7822 : row7822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7822 := by decide +kernel

theorem rowEval7822 (x : Key → ℝ) : Integer.Sparse.eval row7822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7822, Integer.Sparse.eval_collectBalanced, rawRowCheck7822]

theorem rawRowCheck7823 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form6 = rawRow7823 := by decide +kernel

theorem rowCheck7823 : row7823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7823 := by decide +kernel

theorem rowEval7823 (x : Key → ℝ) : Integer.Sparse.eval row7823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7823, Integer.Sparse.eval_collectBalanced, rawRowCheck7823]

theorem rawRowCheck7824 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form6 = rawRow7824 := by decide +kernel

theorem rowCheck7824 : row7824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7824 := by decide +kernel

theorem rowEval7824 (x : Key → ℝ) : Integer.Sparse.eval row7824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck7824, Integer.Sparse.eval_collectBalanced, rawRowCheck7824]

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

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7795 x
  · exact rowEval7796 x
  · exact rowEval7797 x
  · exact rowEval7798 x
  · exact rowEval7799 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

theorem entryCheck6_2 : entry6_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_2 k)) := by decide +kernel

theorem rowsSound6_2 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7800 x
  · exact rowEval7801 x
  · exact rowEval7802 x
  · exact rowEval7803 x
  · exact rowEval7804 x

theorem entryEval6_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_2 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck6_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_2]

theorem entryCheck6_3 : entry6_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_3 k)) := by decide +kernel

theorem rowsSound6_3 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7805 x
  · exact rowEval7806 x
  · exact rowEval7807 x
  · exact rowEval7808 x
  · exact rowEval7809 x

theorem entryEval6_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_3 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck6_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_3]

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

theorem entryCheck6_5 : entry6_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_5 k)) := by decide +kernel

theorem rowsSound6_5 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval7815 x
  · exact rowEval7816 x
  · exact rowEval7817 x
  · exact rowEval7818 x
  · exact rowEval7819 x

theorem entryEval6_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_5 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck6_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_5]

theorem entryCheck6_6 : entry6_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form6.terms k).coefficient) (rows6_6 k)) := by decide +kernel

theorem rowsSound6_6 (k : Fin GramFunctions.Block3.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form6.terms k).tag (GramFunctions.Block3.form6.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval7820 x
  · exact rowEval7821 x
  · exact rowEval7822 x
  · exact rowEval7823 x
  · exact rowEval7824 x

theorem entryEval6_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_6 (GramNormalization.eval B) = GramFunctions.Block3.form6.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck6_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form6 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_6]

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

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8161 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8161 := by decide +kernel

theorem rowCheck8161 : row8161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8161 := by decide +kernel

theorem rowEval8161 (x : Key → ℝ) : Integer.Sparse.eval row8161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8161, Integer.Sparse.eval_collectBalanced, rawRowCheck8161]

theorem rawRowCheck8162 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8162 := by decide +kernel

theorem rowCheck8162 : row8162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8162 := by decide +kernel

theorem rowEval8162 (x : Key → ℝ) : Integer.Sparse.eval row8162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8162, Integer.Sparse.eval_collectBalanced, rawRowCheck8162]

theorem rawRowCheck8163 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8163 := by decide +kernel

theorem rowCheck8163 : row8163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8163 := by decide +kernel

theorem rowEval8163 (x : Key → ℝ) : Integer.Sparse.eval row8163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8163, Integer.Sparse.eval_collectBalanced, rawRowCheck8163]

theorem rawRowCheck8164 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form6 = rawRow8164 := by decide +kernel

theorem rowCheck8164 : row8164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8164 := by decide +kernel

theorem rowEval8164 (x : Key → ℝ) : Integer.Sparse.eval row8164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8164, Integer.Sparse.eval_collectBalanced, rawRowCheck8164]

theorem rawRowCheck8165 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form6 = rawRow8165 := by decide +kernel

theorem rowCheck8165 : row8165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8165 := by decide +kernel

theorem rowEval8165 (x : Key → ℝ) : Integer.Sparse.eval row8165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8165, Integer.Sparse.eval_collectBalanced, rawRowCheck8165]

theorem rawRowCheck8166 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form6 = rawRow8166 := by decide +kernel

theorem rowCheck8166 : row8166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8166 := by decide +kernel

theorem rowEval8166 (x : Key → ℝ) : Integer.Sparse.eval row8166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8166, Integer.Sparse.eval_collectBalanced, rawRowCheck8166]

theorem rawRowCheck8167 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form6 = rawRow8167 := by decide +kernel

theorem rowCheck8167 : row8167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8167 := by decide +kernel

theorem rowEval8167 (x : Key → ℝ) : Integer.Sparse.eval row8167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8167, Integer.Sparse.eval_collectBalanced, rawRowCheck8167]

theorem rawRowCheck8168 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form6 = rawRow8168 := by decide +kernel

theorem rowCheck8168 : row8168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8168 := by decide +kernel

theorem rowEval8168 (x : Key → ℝ) : Integer.Sparse.eval row8168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8168, Integer.Sparse.eval_collectBalanced, rawRowCheck8168]

theorem rawRowCheck8169 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form6 = rawRow8169 := by decide +kernel

theorem rowCheck8169 : row8169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8169 := by decide +kernel

theorem rowEval8169 (x : Key → ℝ) : Integer.Sparse.eval row8169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8169, Integer.Sparse.eval_collectBalanced, rawRowCheck8169]

theorem rawRowCheck8170 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8170 := by decide +kernel

theorem rowCheck8170 : row8170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8170 := by decide +kernel

theorem rowEval8170 (x : Key → ℝ) : Integer.Sparse.eval row8170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8170, Integer.Sparse.eval_collectBalanced, rawRowCheck8170]

theorem rawRowCheck8171 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8171 := by decide +kernel

theorem rowCheck8171 : row8171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8171 := by decide +kernel

theorem rowEval8171 (x : Key → ℝ) : Integer.Sparse.eval row8171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8171, Integer.Sparse.eval_collectBalanced, rawRowCheck8171]

theorem rawRowCheck8172 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8172 := by decide +kernel

theorem rowCheck8172 : row8172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8172 := by decide +kernel

theorem rowEval8172 (x : Key → ℝ) : Integer.Sparse.eval row8172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8172, Integer.Sparse.eval_collectBalanced, rawRowCheck8172]

theorem rawRowCheck8173 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form6 = rawRow8173 := by decide +kernel

theorem rowCheck8173 : row8173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8173 := by decide +kernel

theorem rowEval8173 (x : Key → ℝ) : Integer.Sparse.eval row8173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8173, Integer.Sparse.eval_collectBalanced, rawRowCheck8173]

theorem rawRowCheck8174 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form6 = rawRow8174 := by decide +kernel

theorem rowCheck8174 : row8174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8174 := by decide +kernel

theorem rowEval8174 (x : Key → ℝ) : Integer.Sparse.eval row8174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8174, Integer.Sparse.eval_collectBalanced, rawRowCheck8174]

theorem rawRowCheck8175 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form6 = rawRow8175 := by decide +kernel

theorem rowCheck8175 : row8175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8175 := by decide +kernel

theorem rowEval8175 (x : Key → ℝ) : Integer.Sparse.eval row8175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8175, Integer.Sparse.eval_collectBalanced, rawRowCheck8175]

theorem rawRowCheck8176 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form6 = rawRow8176 := by decide +kernel

theorem rowCheck8176 : row8176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8176 := by decide +kernel

theorem rowEval8176 (x : Key → ℝ) : Integer.Sparse.eval row8176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8176, Integer.Sparse.eval_collectBalanced, rawRowCheck8176]

theorem rawRowCheck8177 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form6 = rawRow8177 := by decide +kernel

theorem rowCheck8177 : row8177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8177 := by decide +kernel

theorem rowEval8177 (x : Key → ℝ) : Integer.Sparse.eval row8177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8177, Integer.Sparse.eval_collectBalanced, rawRowCheck8177]

theorem rawRowCheck8178 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form6 = rawRow8178 := by decide +kernel

theorem rowCheck8178 : row8178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8178 := by decide +kernel

theorem rowEval8178 (x : Key → ℝ) : Integer.Sparse.eval row8178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8178, Integer.Sparse.eval_collectBalanced, rawRowCheck8178]

theorem rawRowCheck8179 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form6 = rawRow8179 := by decide +kernel

theorem rowCheck8179 : row8179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8179 := by decide +kernel

theorem rowEval8179 (x : Key → ℝ) : Integer.Sparse.eval row8179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8179, Integer.Sparse.eval_collectBalanced, rawRowCheck8179]

theorem rawRowCheck8180 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form6 = rawRow8180 := by decide +kernel

theorem rowCheck8180 : row8180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8180 := by decide +kernel

theorem rowEval8180 (x : Key → ℝ) : Integer.Sparse.eval row8180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8180, Integer.Sparse.eval_collectBalanced, rawRowCheck8180]

theorem rawRowCheck8181 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form6 = rawRow8181 := by decide +kernel

theorem rowCheck8181 : row8181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8181 := by decide +kernel

theorem rowEval8181 (x : Key → ℝ) : Integer.Sparse.eval row8181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8181, Integer.Sparse.eval_collectBalanced, rawRowCheck8181]

theorem rawRowCheck8182 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form6 = rawRow8182 := by decide +kernel

theorem rowCheck8182 : row8182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8182 := by decide +kernel

theorem rowEval8182 (x : Key → ℝ) : Integer.Sparse.eval row8182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8182, Integer.Sparse.eval_collectBalanced, rawRowCheck8182]

theorem rawRowCheck8183 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form6 = rawRow8183 := by decide +kernel

theorem rowCheck8183 : row8183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8183 := by decide +kernel

theorem rowEval8183 (x : Key → ℝ) : Integer.Sparse.eval row8183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8183, Integer.Sparse.eval_collectBalanced, rawRowCheck8183]

theorem rawRowCheck8184 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form6 = rawRow8184 := by decide +kernel

theorem rowCheck8184 : row8184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8184 := by decide +kernel

theorem rowEval8184 (x : Key → ℝ) : Integer.Sparse.eval row8184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8184, Integer.Sparse.eval_collectBalanced, rawRowCheck8184]

theorem rawRowCheck8185 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form6 = rawRow8185 := by decide +kernel

theorem rowCheck8185 : row8185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8185 := by decide +kernel

theorem rowEval8185 (x : Key → ℝ) : Integer.Sparse.eval row8185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8185, Integer.Sparse.eval_collectBalanced, rawRowCheck8185]

theorem rawRowCheck8186 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form6 = rawRow8186 := by decide +kernel

theorem rowCheck8186 : row8186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8186 := by decide +kernel

theorem rowEval8186 (x : Key → ℝ) : Integer.Sparse.eval row8186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8186, Integer.Sparse.eval_collectBalanced, rawRowCheck8186]

theorem rawRowCheck8187 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form6 = rawRow8187 := by decide +kernel

theorem rowCheck8187 : row8187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8187 := by decide +kernel

theorem rowEval8187 (x : Key → ℝ) : Integer.Sparse.eval row8187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8187, Integer.Sparse.eval_collectBalanced, rawRowCheck8187]

theorem rawRowCheck8188 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form6 = rawRow8188 := by decide +kernel

theorem rowCheck8188 : row8188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8188 := by decide +kernel

theorem rowEval8188 (x : Key → ℝ) : Integer.Sparse.eval row8188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8188, Integer.Sparse.eval_collectBalanced, rawRowCheck8188]

theorem rawRowCheck8189 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form6 = rawRow8189 := by decide +kernel

theorem rowCheck8189 : row8189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8189 := by decide +kernel

theorem rowEval8189 (x : Key → ℝ) : Integer.Sparse.eval row8189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8189, Integer.Sparse.eval_collectBalanced, rawRowCheck8189]

theorem rawRowCheck8190 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form6 = rawRow8190 := by decide +kernel

theorem rowCheck8190 : row8190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8190 := by decide +kernel

theorem rowEval8190 (x : Key → ℝ) : Integer.Sparse.eval row8190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8190, Integer.Sparse.eval_collectBalanced, rawRowCheck8190]

theorem rawRowCheck8191 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form6 = rawRow8191 := by decide +kernel

theorem rowCheck8191 : row8191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8191 := by decide +kernel

theorem rowEval8191 (x : Key → ℝ) : Integer.Sparse.eval row8191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8191, Integer.Sparse.eval_collectBalanced, rawRowCheck8191]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8192 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form6 = rawRow8192 := by decide +kernel

theorem rowCheck8192 : row8192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8192 := by decide +kernel

theorem rowEval8192 (x : Key → ℝ) : Integer.Sparse.eval row8192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8192, Integer.Sparse.eval_collectBalanced, rawRowCheck8192]

theorem rawRowCheck8193 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form6 = rawRow8193 := by decide +kernel

theorem rowCheck8193 : row8193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8193 := by decide +kernel

theorem rowEval8193 (x : Key → ℝ) : Integer.Sparse.eval row8193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8193, Integer.Sparse.eval_collectBalanced, rawRowCheck8193]

theorem rawRowCheck8194 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form6 = rawRow8194 := by decide +kernel

theorem rowCheck8194 : row8194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8194 := by decide +kernel

theorem rowEval8194 (x : Key → ℝ) : Integer.Sparse.eval row8194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8194, Integer.Sparse.eval_collectBalanced, rawRowCheck8194]

theorem rawRowCheck8195 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form6 = rawRow8195 := by decide +kernel

theorem rowCheck8195 : row8195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8195 := by decide +kernel

theorem rowEval8195 (x : Key → ℝ) : Integer.Sparse.eval row8195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8195, Integer.Sparse.eval_collectBalanced, rawRowCheck8195]

theorem rawRowCheck8196 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form6 = rawRow8196 := by decide +kernel

theorem rowCheck8196 : row8196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8196 := by decide +kernel

theorem rowEval8196 (x : Key → ℝ) : Integer.Sparse.eval row8196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8196, Integer.Sparse.eval_collectBalanced, rawRowCheck8196]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_6 : entry8_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_6 k)) := by decide +kernel

theorem rowsSound8_6 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8161 x
  · exact rowEval8162 x
  · exact rowEval8163 x
  · exact rowEval8164 x
  · exact rowEval8165 x
  · exact rowEval8166 x
  · exact rowEval8167 x
  · exact rowEval8168 x
  · exact rowEval8169 x
  · exact rowEval8170 x
  · exact rowEval8171 x
  · exact rowEval8172 x
  · exact rowEval8173 x
  · exact rowEval8174 x
  · exact rowEval8175 x
  · exact rowEval8176 x
  · exact rowEval8177 x
  · exact rowEval8178 x
  · exact rowEval8179 x
  · exact rowEval8180 x
  · exact rowEval8181 x
  · exact rowEval8182 x
  · exact rowEval8183 x
  · exact rowEval8184 x
  · exact rowEval8185 x
  · exact rowEval8186 x
  · exact rowEval8187 x
  · exact rowEval8188 x
  · exact rowEval8189 x
  · exact rowEval8190 x
  · exact rowEval8191 x
  · exact rowEval8192 x
  · exact rowEval8193 x
  · exact rowEval8194 x
  · exact rowEval8195 x
  · exact rowEval8196 x

theorem entryEval8_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_6 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck8_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_6]

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

theorem entryEvalRow6_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 6 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 6).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval6_0 B hB
  · exact entryEval6_1 B hB
  · exact entryEval6_2 B hB
  · exact entryEval6_3 B hB
  · exact entryEval6_4 B hB
  · exact entryEval6_5 B hB
  · exact entryEval6_6 B hB
  · exact (entryEval7_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_6_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_6_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e_oai
