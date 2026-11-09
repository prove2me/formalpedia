-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:13:19.564369+00:00
-- url     : https://prove2.me/submissions/d3e74c7b-6d12-4bf3-a894-e1a39257b12b

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

theorem rawRowCheck7446 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7446 := by decide +kernel

theorem rowCheck7446 : row7446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7446 := by decide +kernel

theorem rowEval7446 (x : Key → ℝ) : Integer.Sparse.eval row7446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7446, Integer.Sparse.eval_collectBalanced, rawRowCheck7446]

theorem rawRowCheck7447 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7447 := by decide +kernel

theorem rowCheck7447 : row7447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7447 := by decide +kernel

theorem rowEval7447 (x : Key → ℝ) : Integer.Sparse.eval row7447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7447, Integer.Sparse.eval_collectBalanced, rawRowCheck7447]

theorem rawRowCheck7448 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7448 := by decide +kernel

theorem rowCheck7448 : row7448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7448 := by decide +kernel

theorem rowEval7448 (x : Key → ℝ) : Integer.Sparse.eval row7448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7448, Integer.Sparse.eval_collectBalanced, rawRowCheck7448]

theorem rawRowCheck7449 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7449 := by decide +kernel

theorem rowCheck7449 : row7449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7449 := by decide +kernel

theorem rowEval7449 (x : Key → ℝ) : Integer.Sparse.eval row7449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7449, Integer.Sparse.eval_collectBalanced, rawRowCheck7449]

theorem rawRowCheck7462 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7462 := by decide +kernel

theorem rowCheck7462 : row7462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7462 := by decide +kernel

theorem rowEval7462 (x : Key → ℝ) : Integer.Sparse.eval row7462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7462, Integer.Sparse.eval_collectBalanced, rawRowCheck7462]

theorem rawRowCheck7463 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2 = rawRow7463 := by decide +kernel

theorem rowCheck7463 : row7463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7463 := by decide +kernel

theorem rowEval7463 (x : Key → ℝ) : Integer.Sparse.eval row7463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7463, Integer.Sparse.eval_collectBalanced, rawRowCheck7463]

theorem rawRowCheck7464 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2 = rawRow7464 := by decide +kernel

theorem rowCheck7464 : row7464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7464 := by decide +kernel

theorem rowEval7464 (x : Key → ℝ) : Integer.Sparse.eval row7464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7464, Integer.Sparse.eval_collectBalanced, rawRowCheck7464]

theorem rawRowCheck7465 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2 = rawRow7465 := by decide +kernel

theorem rowCheck7465 : row7465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7465 := by decide +kernel

theorem rowEval7465 (x : Key → ℝ) : Integer.Sparse.eval row7465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7465, Integer.Sparse.eval_collectBalanced, rawRowCheck7465]

theorem rawRowCheck7478 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7478 := by decide +kernel

theorem rowCheck7478 : row7478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7478 := by decide +kernel

theorem rowEval7478 (x : Key → ℝ) : Integer.Sparse.eval row7478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7478, Integer.Sparse.eval_collectBalanced, rawRowCheck7478]

theorem rawRowCheck7479 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3 = rawRow7479 := by decide +kernel

theorem rowCheck7479 : row7479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7479 := by decide +kernel

theorem rowEval7479 (x : Key → ℝ) : Integer.Sparse.eval row7479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7479, Integer.Sparse.eval_collectBalanced, rawRowCheck7479]

theorem rawRowCheck7480 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3 = rawRow7480 := by decide +kernel

theorem rowCheck7480 : row7480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7480 := by decide +kernel

theorem rowEval7480 (x : Key → ℝ) : Integer.Sparse.eval row7480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7480, Integer.Sparse.eval_collectBalanced, rawRowCheck7480]

theorem rawRowCheck7481 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3 = rawRow7481 := by decide +kernel

theorem rowCheck7481 : row7481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7481 := by decide +kernel

theorem rowEval7481 (x : Key → ℝ) : Integer.Sparse.eval row7481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7481, Integer.Sparse.eval_collectBalanced, rawRowCheck7481]

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

theorem rawRowCheck9385 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form1 = rawRow9385 := by decide +kernel

theorem rowCheck9385 : row9385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9385 := by decide +kernel

theorem rowEval9385 (x : Key → ℝ) : Integer.Sparse.eval row9385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9385, Integer.Sparse.eval_collectBalanced, rawRowCheck9385]

theorem rawRowCheck9386 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form1 = rawRow9386 := by decide +kernel

theorem rowCheck9386 : row9386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9386 := by decide +kernel

theorem rowEval9386 (x : Key → ℝ) : Integer.Sparse.eval row9386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9386, Integer.Sparse.eval_collectBalanced, rawRowCheck9386]

theorem rawRowCheck9387 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form1 = rawRow9387 := by decide +kernel

theorem rowCheck9387 : row9387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9387 := by decide +kernel

theorem rowEval9387 (x : Key → ℝ) : Integer.Sparse.eval row9387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9387, Integer.Sparse.eval_collectBalanced, rawRowCheck9387]

theorem rawRowCheck9388 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form1 = rawRow9388 := by decide +kernel

theorem rowCheck9388 : row9388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9388 := by decide +kernel

theorem rowEval9388 (x : Key → ℝ) : Integer.Sparse.eval row9388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9388, Integer.Sparse.eval_collectBalanced, rawRowCheck9388]

theorem rawRowCheck9389 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form2 = rawRow9389 := by decide +kernel

theorem rowCheck9389 : row9389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9389 := by decide +kernel

theorem rowEval9389 (x : Key → ℝ) : Integer.Sparse.eval row9389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9389, Integer.Sparse.eval_collectBalanced, rawRowCheck9389]

theorem rawRowCheck9390 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form2 = rawRow9390 := by decide +kernel

theorem rowCheck9390 : row9390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9390 := by decide +kernel

theorem rowEval9390 (x : Key → ℝ) : Integer.Sparse.eval row9390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9390, Integer.Sparse.eval_collectBalanced, rawRowCheck9390]

theorem rawRowCheck9391 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form2 = rawRow9391 := by decide +kernel

theorem rowCheck9391 : row9391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9391 := by decide +kernel

theorem rowEval9391 (x : Key → ℝ) : Integer.Sparse.eval row9391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9391, Integer.Sparse.eval_collectBalanced, rawRowCheck9391]

theorem rawRowCheck9392 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form2 = rawRow9392 := by decide +kernel

theorem rowCheck9392 : row9392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9392 := by decide +kernel

theorem rowEval9392 (x : Key → ℝ) : Integer.Sparse.eval row9392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9392, Integer.Sparse.eval_collectBalanced, rawRowCheck9392]

theorem rawRowCheck9393 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9393 := by decide +kernel

theorem rowCheck9393 : row9393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9393 := by decide +kernel

theorem rowEval9393 (x : Key → ℝ) : Integer.Sparse.eval row9393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9393, Integer.Sparse.eval_collectBalanced, rawRowCheck9393]

theorem rawRowCheck9394 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form3 = rawRow9394 := by decide +kernel

theorem rowCheck9394 : row9394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9394 := by decide +kernel

theorem rowEval9394 (x : Key → ℝ) : Integer.Sparse.eval row9394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9394, Integer.Sparse.eval_collectBalanced, rawRowCheck9394]

theorem rawRowCheck9395 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form3 = rawRow9395 := by decide +kernel

theorem rowCheck9395 : row9395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9395 := by decide +kernel

theorem rowEval9395 (x : Key → ℝ) : Integer.Sparse.eval row9395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9395, Integer.Sparse.eval_collectBalanced, rawRowCheck9395]

theorem rawRowCheck9396 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form3 = rawRow9396 := by decide +kernel

theorem rowCheck9396 : row9396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9396 := by decide +kernel

theorem rowEval9396 (x : Key → ℝ) : Integer.Sparse.eval row9396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9396, Integer.Sparse.eval_collectBalanced, rawRowCheck9396]

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

theorem rawRowCheck9405 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form5 = rawRow9405 := by decide +kernel

theorem rowCheck9405 : row9405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9405 := by decide +kernel

theorem rowEval9405 (x : Key → ℝ) : Integer.Sparse.eval row9405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9405, Integer.Sparse.eval_collectBalanced, rawRowCheck9405]

theorem rawRowCheck9406 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form5 = rawRow9406 := by decide +kernel

theorem rowCheck9406 : row9406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9406 := by decide +kernel

theorem rowEval9406 (x : Key → ℝ) : Integer.Sparse.eval row9406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9406, Integer.Sparse.eval_collectBalanced, rawRowCheck9406]

theorem rawRowCheck9407 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form5 = rawRow9407 := by decide +kernel

theorem rowCheck9407 : row9407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9407 := by decide +kernel

theorem rowEval9407 (x : Key → ℝ) : Integer.Sparse.eval row9407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9407, Integer.Sparse.eval_collectBalanced, rawRowCheck9407]

theorem rawRowCheck9408 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form5 = rawRow9408 := by decide +kernel

theorem rowCheck9408 : row9408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9408 := by decide +kernel

theorem rowEval9408 (x : Key → ℝ) : Integer.Sparse.eval row9408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9408, Integer.Sparse.eval_collectBalanced, rawRowCheck9408]

theorem rawRowCheck9409 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow9409 := by decide +kernel

theorem rowCheck9409 : row9409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9409 := by decide +kernel

theorem rowEval9409 (x : Key → ℝ) : Integer.Sparse.eval row9409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9409, Integer.Sparse.eval_collectBalanced, rawRowCheck9409]

theorem rawRowCheck9410 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form5 = rawRow9410 := by decide +kernel

theorem rowCheck9410 : row9410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9410 := by decide +kernel

theorem rowEval9410 (x : Key → ℝ) : Integer.Sparse.eval row9410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9410, Integer.Sparse.eval_collectBalanced, rawRowCheck9410]

theorem rawRowCheck9411 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form5 = rawRow9411 := by decide +kernel

theorem rowCheck9411 : row9411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9411 := by decide +kernel

theorem rowEval9411 (x : Key → ℝ) : Integer.Sparse.eval row9411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9411, Integer.Sparse.eval_collectBalanced, rawRowCheck9411]

theorem rawRowCheck9412 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form5 = rawRow9412 := by decide +kernel

theorem rowCheck9412 : row9412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9412 := by decide +kernel

theorem rowEval9412 (x : Key → ℝ) : Integer.Sparse.eval row9412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9412, Integer.Sparse.eval_collectBalanced, rawRowCheck9412]

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

theorem rawRowCheck9429 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form8 = rawRow9429 := by decide +kernel

theorem rowCheck9429 : row9429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9429 := by decide +kernel

theorem rowEval9429 (x : Key → ℝ) : Integer.Sparse.eval row9429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9429, Integer.Sparse.eval_collectBalanced, rawRowCheck9429]

theorem rawRowCheck9430 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form8 = rawRow9430 := by decide +kernel

theorem rowCheck9430 : row9430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9430 := by decide +kernel

theorem rowEval9430 (x : Key → ℝ) : Integer.Sparse.eval row9430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9430, Integer.Sparse.eval_collectBalanced, rawRowCheck9430]

theorem rawRowCheck9431 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form8 = rawRow9431 := by decide +kernel

theorem rowCheck9431 : row9431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9431 := by decide +kernel

theorem rowEval9431 (x : Key → ℝ) : Integer.Sparse.eval row9431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9431, Integer.Sparse.eval_collectBalanced, rawRowCheck9431]

theorem rawRowCheck9432 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form8 = rawRow9432 := by decide +kernel

theorem rowCheck9432 : row9432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9432 := by decide +kernel

theorem rowEval9432 (x : Key → ℝ) : Integer.Sparse.eval row9432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9432, Integer.Sparse.eval_collectBalanced, rawRowCheck9432]

theorem rawRowCheck9433 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow9433 := by decide +kernel

theorem rowCheck9433 : row9433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9433 := by decide +kernel

theorem rowEval9433 (x : Key → ℝ) : Integer.Sparse.eval row9433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9433, Integer.Sparse.eval_collectBalanced, rawRowCheck9433]

theorem rawRowCheck9434 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form8 = rawRow9434 := by decide +kernel

theorem rowCheck9434 : row9434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9434 := by decide +kernel

theorem rowEval9434 (x : Key → ℝ) : Integer.Sparse.eval row9434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9434, Integer.Sparse.eval_collectBalanced, rawRowCheck9434]

theorem rawRowCheck9435 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form8 = rawRow9435 := by decide +kernel

theorem rowCheck9435 : row9435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9435 := by decide +kernel

theorem rowEval9435 (x : Key → ℝ) : Integer.Sparse.eval row9435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9435, Integer.Sparse.eval_collectBalanced, rawRowCheck9435]

theorem rawRowCheck9436 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form8 = rawRow9436 := by decide +kernel

theorem rowCheck9436 : row9436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9436 := by decide +kernel

theorem rowEval9436 (x : Key → ℝ) : Integer.Sparse.eval row9436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9436, Integer.Sparse.eval_collectBalanced, rawRowCheck9436]

theorem rawRowCheck9437 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form9 = rawRow9437 := by decide +kernel

theorem rowCheck9437 : row9437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9437 := by decide +kernel

theorem rowEval9437 (x : Key → ℝ) : Integer.Sparse.eval row9437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9437, Integer.Sparse.eval_collectBalanced, rawRowCheck9437]

theorem rawRowCheck9438 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form9 = rawRow9438 := by decide +kernel

theorem rowCheck9438 : row9438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9438 := by decide +kernel

theorem rowEval9438 (x : Key → ℝ) : Integer.Sparse.eval row9438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9438, Integer.Sparse.eval_collectBalanced, rawRowCheck9438]

theorem rawRowCheck9439 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form9 = rawRow9439 := by decide +kernel

theorem rowCheck9439 : row9439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9439 := by decide +kernel

theorem rowEval9439 (x : Key → ℝ) : Integer.Sparse.eval row9439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9439, Integer.Sparse.eval_collectBalanced, rawRowCheck9439]

theorem rawRowCheck9440 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form9 = rawRow9440 := by decide +kernel

theorem rowCheck9440 : row9440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9440 := by decide +kernel

theorem rowEval9440 (x : Key → ℝ) : Integer.Sparse.eval row9440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9440, Integer.Sparse.eval_collectBalanced, rawRowCheck9440]

theorem rawRowCheck9441 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow9441 := by decide +kernel

theorem rowCheck9441 : row9441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9441 := by decide +kernel

theorem rowEval9441 (x : Key → ℝ) : Integer.Sparse.eval row9441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9441, Integer.Sparse.eval_collectBalanced, rawRowCheck9441]

theorem rawRowCheck9442 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form9 = rawRow9442 := by decide +kernel

theorem rowCheck9442 : row9442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9442 := by decide +kernel

theorem rowEval9442 (x : Key → ℝ) : Integer.Sparse.eval row9442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9442, Integer.Sparse.eval_collectBalanced, rawRowCheck9442]

theorem rawRowCheck9443 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form9 = rawRow9443 := by decide +kernel

theorem rowCheck9443 : row9443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9443 := by decide +kernel

theorem rowEval9443 (x : Key → ℝ) : Integer.Sparse.eval row9443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9443, Integer.Sparse.eval_collectBalanced, rawRowCheck9443]

theorem rawRowCheck9444 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form9 = rawRow9444 := by decide +kernel

theorem rowCheck9444 : row9444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9444 := by decide +kernel

theorem rowEval9444 (x : Key → ℝ) : Integer.Sparse.eval row9444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9444, Integer.Sparse.eval_collectBalanced, rawRowCheck9444]

theorem rawRowCheck9445 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9445 := by decide +kernel

theorem rowCheck9445 : row9445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9445 := by decide +kernel

theorem rowEval9445 (x : Key → ℝ) : Integer.Sparse.eval row9445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9445, Integer.Sparse.eval_collectBalanced, rawRowCheck9445]

theorem rawRowCheck9446 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form10 = rawRow9446 := by decide +kernel

theorem rowCheck9446 : row9446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9446 := by decide +kernel

theorem rowEval9446 (x : Key → ℝ) : Integer.Sparse.eval row9446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9446, Integer.Sparse.eval_collectBalanced, rawRowCheck9446]

theorem rawRowCheck9447 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form10 = rawRow9447 := by decide +kernel

theorem rowCheck9447 : row9447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9447 := by decide +kernel

theorem rowEval9447 (x : Key → ℝ) : Integer.Sparse.eval row9447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9447, Integer.Sparse.eval_collectBalanced, rawRowCheck9447]

theorem rawRowCheck9448 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form10 = rawRow9448 := by decide +kernel

theorem rowCheck9448 : row9448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9448 := by decide +kernel

theorem rowEval9448 (x : Key → ℝ) : Integer.Sparse.eval row9448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9448, Integer.Sparse.eval_collectBalanced, rawRowCheck9448]

theorem rawRowCheck9449 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9449 := by decide +kernel

theorem rowCheck9449 : row9449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9449 := by decide +kernel

theorem rowEval9449 (x : Key → ℝ) : Integer.Sparse.eval row9449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9449, Integer.Sparse.eval_collectBalanced, rawRowCheck9449]

theorem rawRowCheck9450 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10 = rawRow9450 := by decide +kernel

theorem rowCheck9450 : row9450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9450 := by decide +kernel

theorem rowEval9450 (x : Key → ℝ) : Integer.Sparse.eval row9450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9450, Integer.Sparse.eval_collectBalanced, rawRowCheck9450]

theorem rawRowCheck9451 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10 = rawRow9451 := by decide +kernel

theorem rowCheck9451 : row9451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9451 := by decide +kernel

theorem rowEval9451 (x : Key → ℝ) : Integer.Sparse.eval row9451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9451, Integer.Sparse.eval_collectBalanced, rawRowCheck9451]

theorem rawRowCheck9452 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10 = rawRow9452 := by decide +kernel

theorem rowCheck9452 : row9452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9452 := by decide +kernel

theorem rowEval9452 (x : Key → ℝ) : Integer.Sparse.eval row9452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9452, Integer.Sparse.eval_collectBalanced, rawRowCheck9452]

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

theorem rawRowCheck9461 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9461 := by decide +kernel

theorem rowCheck9461 : row9461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9461 := by decide +kernel

theorem rowEval9461 (x : Key → ℝ) : Integer.Sparse.eval row9461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9461, Integer.Sparse.eval_collectBalanced, rawRowCheck9461]

theorem rawRowCheck9462 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form12 = rawRow9462 := by decide +kernel

theorem rowCheck9462 : row9462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9462 := by decide +kernel

theorem rowEval9462 (x : Key → ℝ) : Integer.Sparse.eval row9462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9462, Integer.Sparse.eval_collectBalanced, rawRowCheck9462]

theorem rawRowCheck9463 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form12 = rawRow9463 := by decide +kernel

theorem rowCheck9463 : row9463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9463 := by decide +kernel

theorem rowEval9463 (x : Key → ℝ) : Integer.Sparse.eval row9463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9463, Integer.Sparse.eval_collectBalanced, rawRowCheck9463]

theorem rawRowCheck9464 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form12 = rawRow9464 := by decide +kernel

theorem rowCheck9464 : row9464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9464 := by decide +kernel

theorem rowEval9464 (x : Key → ℝ) : Integer.Sparse.eval row9464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9464, Integer.Sparse.eval_collectBalanced, rawRowCheck9464]

theorem rawRowCheck9465 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9465 := by decide +kernel

theorem rowCheck9465 : row9465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9465 := by decide +kernel

theorem rowEval9465 (x : Key → ℝ) : Integer.Sparse.eval row9465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9465, Integer.Sparse.eval_collectBalanced, rawRowCheck9465]

theorem rawRowCheck9466 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form12 = rawRow9466 := by decide +kernel

theorem rowCheck9466 : row9466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9466 := by decide +kernel

theorem rowEval9466 (x : Key → ℝ) : Integer.Sparse.eval row9466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9466, Integer.Sparse.eval_collectBalanced, rawRowCheck9466]

theorem rawRowCheck9467 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form12 = rawRow9467 := by decide +kernel

theorem rowCheck9467 : row9467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9467 := by decide +kernel

theorem rowEval9467 (x : Key → ℝ) : Integer.Sparse.eval row9467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9467, Integer.Sparse.eval_collectBalanced, rawRowCheck9467]

theorem rawRowCheck9468 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form12 = rawRow9468 := by decide +kernel

theorem rowCheck9468 : row9468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9468 := by decide +kernel

theorem rowEval9468 (x : Key → ℝ) : Integer.Sparse.eval row9468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9468, Integer.Sparse.eval_collectBalanced, rawRowCheck9468]

theorem rawRowCheck9469 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9469 := by decide +kernel

theorem rowCheck9469 : row9469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9469 := by decide +kernel

theorem rowEval9469 (x : Key → ℝ) : Integer.Sparse.eval row9469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9469, Integer.Sparse.eval_collectBalanced, rawRowCheck9469]

theorem rawRowCheck9470 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form13 = rawRow9470 := by decide +kernel

theorem rowCheck9470 : row9470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9470 := by decide +kernel

theorem rowEval9470 (x : Key → ℝ) : Integer.Sparse.eval row9470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9470, Integer.Sparse.eval_collectBalanced, rawRowCheck9470]

theorem rawRowCheck9471 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form13 = rawRow9471 := by decide +kernel

theorem rowCheck9471 : row9471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9471 := by decide +kernel

theorem rowEval9471 (x : Key → ℝ) : Integer.Sparse.eval row9471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9471, Integer.Sparse.eval_collectBalanced, rawRowCheck9471]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck9472 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form13 = rawRow9472 := by decide +kernel

theorem rowCheck9472 : row9472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9472 := by decide +kernel

theorem rowEval9472 (x : Key → ℝ) : Integer.Sparse.eval row9472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9472, Integer.Sparse.eval_collectBalanced, rawRowCheck9472]

theorem rawRowCheck9473 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9473 := by decide +kernel

theorem rowCheck9473 : row9473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9473 := by decide +kernel

theorem rowEval9473 (x : Key → ℝ) : Integer.Sparse.eval row9473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9473, Integer.Sparse.eval_collectBalanced, rawRowCheck9473]

theorem rawRowCheck9474 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form13 = rawRow9474 := by decide +kernel

theorem rowCheck9474 : row9474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9474 := by decide +kernel

theorem rowEval9474 (x : Key → ℝ) : Integer.Sparse.eval row9474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9474, Integer.Sparse.eval_collectBalanced, rawRowCheck9474]

theorem rawRowCheck9475 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form13 = rawRow9475 := by decide +kernel

theorem rowCheck9475 : row9475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9475 := by decide +kernel

theorem rowEval9475 (x : Key → ℝ) : Integer.Sparse.eval row9475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9475, Integer.Sparse.eval_collectBalanced, rawRowCheck9475]

theorem rawRowCheck9476 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form13 = rawRow9476 := by decide +kernel

theorem rowCheck9476 : row9476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9476 := by decide +kernel

theorem rowEval9476 (x : Key → ℝ) : Integer.Sparse.eval row9476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9476, Integer.Sparse.eval_collectBalanced, rawRowCheck9476]

theorem rawRowCheck9477 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9477 := by decide +kernel

theorem rowCheck9477 : row9477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9477 := by decide +kernel

theorem rowEval9477 (x : Key → ℝ) : Integer.Sparse.eval row9477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9477, Integer.Sparse.eval_collectBalanced, rawRowCheck9477]

theorem rawRowCheck9478 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form14 = rawRow9478 := by decide +kernel

theorem rowCheck9478 : row9478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9478 := by decide +kernel

theorem rowEval9478 (x : Key → ℝ) : Integer.Sparse.eval row9478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9478, Integer.Sparse.eval_collectBalanced, rawRowCheck9478]

theorem rawRowCheck9479 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form14 = rawRow9479 := by decide +kernel

theorem rowCheck9479 : row9479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9479 := by decide +kernel

theorem rowEval9479 (x : Key → ℝ) : Integer.Sparse.eval row9479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9479, Integer.Sparse.eval_collectBalanced, rawRowCheck9479]

theorem rawRowCheck9480 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form14 = rawRow9480 := by decide +kernel

theorem rowCheck9480 : row9480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9480 := by decide +kernel

theorem rowEval9480 (x : Key → ℝ) : Integer.Sparse.eval row9480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9480, Integer.Sparse.eval_collectBalanced, rawRowCheck9480]

theorem rawRowCheck9481 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9481 := by decide +kernel

theorem rowCheck9481 : row9481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9481 := by decide +kernel

theorem rowEval9481 (x : Key → ℝ) : Integer.Sparse.eval row9481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9481, Integer.Sparse.eval_collectBalanced, rawRowCheck9481]

theorem rawRowCheck9482 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form14 = rawRow9482 := by decide +kernel

theorem rowCheck9482 : row9482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9482 := by decide +kernel

theorem rowEval9482 (x : Key → ℝ) : Integer.Sparse.eval row9482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9482, Integer.Sparse.eval_collectBalanced, rawRowCheck9482]

theorem rawRowCheck9483 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form14 = rawRow9483 := by decide +kernel

theorem rowCheck9483 : row9483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9483 := by decide +kernel

theorem rowEval9483 (x : Key → ℝ) : Integer.Sparse.eval row9483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9483, Integer.Sparse.eval_collectBalanced, rawRowCheck9483]

theorem rawRowCheck9484 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form14 = rawRow9484 := by decide +kernel

theorem rowCheck9484 : row9484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9484 := by decide +kernel

theorem rowEval9484 (x : Key → ℝ) : Integer.Sparse.eval row9484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9484, Integer.Sparse.eval_collectBalanced, rawRowCheck9484]

theorem rawRowCheck9485 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form15 = rawRow9485 := by decide +kernel

theorem rowCheck9485 : row9485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9485 := by decide +kernel

theorem rowEval9485 (x : Key → ℝ) : Integer.Sparse.eval row9485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9485, Integer.Sparse.eval_collectBalanced, rawRowCheck9485]

theorem rawRowCheck9486 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form15 = rawRow9486 := by decide +kernel

theorem rowCheck9486 : row9486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9486 := by decide +kernel

theorem rowEval9486 (x : Key → ℝ) : Integer.Sparse.eval row9486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9486, Integer.Sparse.eval_collectBalanced, rawRowCheck9486]

theorem rawRowCheck9487 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form15 = rawRow9487 := by decide +kernel

theorem rowCheck9487 : row9487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9487 := by decide +kernel

theorem rowEval9487 (x : Key → ℝ) : Integer.Sparse.eval row9487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9487, Integer.Sparse.eval_collectBalanced, rawRowCheck9487]

theorem rawRowCheck9488 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form15 = rawRow9488 := by decide +kernel

theorem rowCheck9488 : row9488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9488 := by decide +kernel

theorem rowEval9488 (x : Key → ℝ) : Integer.Sparse.eval row9488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9488, Integer.Sparse.eval_collectBalanced, rawRowCheck9488]

theorem rawRowCheck9489 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow9489 := by decide +kernel

theorem rowCheck9489 : row9489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9489 := by decide +kernel

theorem rowEval9489 (x : Key → ℝ) : Integer.Sparse.eval row9489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9489, Integer.Sparse.eval_collectBalanced, rawRowCheck9489]

theorem rawRowCheck9490 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form15 = rawRow9490 := by decide +kernel

theorem rowCheck9490 : row9490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9490 := by decide +kernel

theorem rowEval9490 (x : Key → ℝ) : Integer.Sparse.eval row9490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9490, Integer.Sparse.eval_collectBalanced, rawRowCheck9490]

theorem rawRowCheck9491 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form15 = rawRow9491 := by decide +kernel

theorem rowCheck9491 : row9491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9491 := by decide +kernel

theorem rowEval9491 (x : Key → ℝ) : Integer.Sparse.eval row9491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9491, Integer.Sparse.eval_collectBalanced, rawRowCheck9491]

theorem rawRowCheck9492 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form15 = rawRow9492 := by decide +kernel

theorem rowCheck9492 : row9492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9492 := by decide +kernel

theorem rowEval9492 (x : Key → ℝ) : Integer.Sparse.eval row9492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9492, Integer.Sparse.eval_collectBalanced, rawRowCheck9492]

theorem rawRowCheck9493 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form16 = rawRow9493 := by decide +kernel

theorem rowCheck9493 : row9493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9493 := by decide +kernel

theorem rowEval9493 (x : Key → ℝ) : Integer.Sparse.eval row9493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9493, Integer.Sparse.eval_collectBalanced, rawRowCheck9493]

theorem rawRowCheck9494 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form16 = rawRow9494 := by decide +kernel

theorem rowCheck9494 : row9494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9494 := by decide +kernel

theorem rowEval9494 (x : Key → ℝ) : Integer.Sparse.eval row9494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9494, Integer.Sparse.eval_collectBalanced, rawRowCheck9494]

theorem rawRowCheck9495 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form16 = rawRow9495 := by decide +kernel

theorem rowCheck9495 : row9495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9495 := by decide +kernel

theorem rowEval9495 (x : Key → ℝ) : Integer.Sparse.eval row9495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9495, Integer.Sparse.eval_collectBalanced, rawRowCheck9495]

theorem rawRowCheck9496 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form16 = rawRow9496 := by decide +kernel

theorem rowCheck9496 : row9496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9496 := by decide +kernel

theorem rowEval9496 (x : Key → ℝ) : Integer.Sparse.eval row9496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9496, Integer.Sparse.eval_collectBalanced, rawRowCheck9496]

theorem rawRowCheck9497 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form16 = rawRow9497 := by decide +kernel

theorem rowCheck9497 : row9497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9497 := by decide +kernel

theorem rowEval9497 (x : Key → ℝ) : Integer.Sparse.eval row9497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9497, Integer.Sparse.eval_collectBalanced, rawRowCheck9497]

theorem rawRowCheck9498 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form16 = rawRow9498 := by decide +kernel

theorem rowCheck9498 : row9498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9498 := by decide +kernel

theorem rowEval9498 (x : Key → ℝ) : Integer.Sparse.eval row9498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9498, Integer.Sparse.eval_collectBalanced, rawRowCheck9498]

theorem rawRowCheck9499 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form16 = rawRow9499 := by decide +kernel

theorem rowCheck9499 : row9499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9499 := by decide +kernel

theorem rowEval9499 (x : Key → ℝ) : Integer.Sparse.eval row9499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9499, Integer.Sparse.eval_collectBalanced, rawRowCheck9499]

theorem rawRowCheck9500 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form16 = rawRow9500 := by decide +kernel

theorem rowCheck9500 : row9500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9500 := by decide +kernel

theorem rowEval9500 (x : Key → ℝ) : Integer.Sparse.eval row9500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9500, Integer.Sparse.eval_collectBalanced, rawRowCheck9500]

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

theorem entryCheck16_1 : entry16_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_1 k)) := by decide +kernel

theorem rowsSound16_1 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval9385 x
  · exact rowEval9386 x
  · exact rowEval9387 x
  · exact rowEval9388 x
  · exact rowEval7446 x
  · exact rowEval7447 x
  · exact rowEval7448 x
  · exact rowEval7449 x

theorem entryEval16_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_1 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck16_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_1]

theorem entryCheck16_2 : entry16_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_2 k)) := by decide +kernel

theorem rowsSound16_2 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval9389 x
  · exact rowEval9390 x
  · exact rowEval9391 x
  · exact rowEval9392 x
  · exact rowEval7462 x
  · exact rowEval7463 x
  · exact rowEval7464 x
  · exact rowEval7465 x

theorem entryEval16_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_2 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck16_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_2]

theorem entryCheck16_3 : entry16_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_3 k)) := by decide +kernel

theorem rowsSound16_3 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval9393 x
  · exact rowEval9394 x
  · exact rowEval9395 x
  · exact rowEval9396 x
  · exact rowEval7478 x
  · exact rowEval7479 x
  · exact rowEval7480 x
  · exact rowEval7481 x

theorem entryEval16_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_3 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck16_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_3]

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

theorem entryCheck16_5 : entry16_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_5 k)) := by decide +kernel

theorem rowsSound16_5 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval9405 x
  · exact rowEval9406 x
  · exact rowEval9407 x
  · exact rowEval9408 x
  · exact rowEval9409 x
  · exact rowEval9410 x
  · exact rowEval9411 x
  · exact rowEval9412 x

theorem entryEval16_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_5 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck16_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_5]

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

theorem entryCheck16_8 : entry16_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_8 k)) := by decide +kernel

theorem rowsSound16_8 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval9429 x
  · exact rowEval9430 x
  · exact rowEval9431 x
  · exact rowEval9432 x
  · exact rowEval9433 x
  · exact rowEval9434 x
  · exact rowEval9435 x
  · exact rowEval9436 x

theorem entryEval16_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_8 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck16_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_8]

theorem entryCheck16_9 : entry16_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_9 k)) := by decide +kernel

theorem rowsSound16_9 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval9437 x
  · exact rowEval9438 x
  · exact rowEval9439 x
  · exact rowEval9440 x
  · exact rowEval9441 x
  · exact rowEval9442 x
  · exact rowEval9443 x
  · exact rowEval9444 x

theorem entryEval16_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_9 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck16_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_9]

theorem entryCheck16_10 : entry16_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_10 k)) := by decide +kernel

theorem rowsSound16_10 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9445 x
  · exact rowEval9446 x
  · exact rowEval9447 x
  · exact rowEval9448 x
  · exact rowEval9449 x
  · exact rowEval9450 x
  · exact rowEval9451 x
  · exact rowEval9452 x

theorem entryEval16_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_10 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck16_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_10]

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

theorem entryCheck16_12 : entry16_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_12 k)) := by decide +kernel

theorem rowsSound16_12 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9461 x
  · exact rowEval9462 x
  · exact rowEval9463 x
  · exact rowEval9464 x
  · exact rowEval9465 x
  · exact rowEval9466 x
  · exact rowEval9467 x
  · exact rowEval9468 x

theorem entryEval16_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_12 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck16_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_12]

theorem entryCheck16_13 : entry16_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_13 k)) := by decide +kernel

theorem rowsSound16_13 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9469 x
  · exact rowEval9470 x
  · exact rowEval9471 x
  · exact rowEval9472 x
  · exact rowEval9473 x
  · exact rowEval9474 x
  · exact rowEval9475 x
  · exact rowEval9476 x

theorem entryEval16_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_13 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck16_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_13]

theorem entryCheck16_14 : entry16_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_14 k)) := by decide +kernel

theorem rowsSound16_14 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9477 x
  · exact rowEval9478 x
  · exact rowEval9479 x
  · exact rowEval9480 x
  · exact rowEval9481 x
  · exact rowEval9482 x
  · exact rowEval9483 x
  · exact rowEval9484 x

theorem entryEval16_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_14 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck16_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_14]

theorem entryCheck16_15 : entry16_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_15 k)) := by decide +kernel

theorem rowsSound16_15 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval9485 x
  · exact rowEval9486 x
  · exact rowEval9487 x
  · exact rowEval9488 x
  · exact rowEval9489 x
  · exact rowEval9490 x
  · exact rowEval9491 x
  · exact rowEval9492 x

theorem entryEval16_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_15 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck16_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_15]

theorem entryCheck16_16 : entry16_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_16 k)) := by decide +kernel

theorem rowsSound16_16 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval9493 x
  · exact rowEval9494 x
  · exact rowEval9495 x
  · exact rowEval9496 x
  · exact rowEval9497 x
  · exact rowEval9498 x
  · exact rowEval9499 x
  · exact rowEval9500 x

theorem entryEval16_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_16 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck16_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_16]

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

theorem rawRowCheck10549 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form16 = rawRow10549 := by decide +kernel

theorem rowCheck10549 : row10549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10549 := by decide +kernel

theorem rowEval10549 (x : Key → ℝ) : Integer.Sparse.eval row10549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10549, Integer.Sparse.eval_collectBalanced, rawRowCheck10549]

theorem rawRowCheck10550 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form16 = rawRow10550 := by decide +kernel

theorem rowCheck10550 : row10550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10550 := by decide +kernel

theorem rowEval10550 (x : Key → ℝ) : Integer.Sparse.eval row10550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10550, Integer.Sparse.eval_collectBalanced, rawRowCheck10550]

theorem rawRowCheck10551 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form16 = rawRow10551 := by decide +kernel

theorem rowCheck10551 : row10551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10551 := by decide +kernel

theorem rowEval10551 (x : Key → ℝ) : Integer.Sparse.eval row10551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10551, Integer.Sparse.eval_collectBalanced, rawRowCheck10551]

theorem rawRowCheck10552 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form16 = rawRow10552 := by decide +kernel

theorem rowCheck10552 : row10552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10552 := by decide +kernel

theorem rowEval10552 (x : Key → ℝ) : Integer.Sparse.eval row10552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10552, Integer.Sparse.eval_collectBalanced, rawRowCheck10552]

theorem rawRowCheck10553 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form16 = rawRow10553 := by decide +kernel

theorem rowCheck10553 : row10553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10553 := by decide +kernel

theorem rowEval10553 (x : Key → ℝ) : Integer.Sparse.eval row10553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10553, Integer.Sparse.eval_collectBalanced, rawRowCheck10553]

theorem rawRowCheck10554 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form16 = rawRow10554 := by decide +kernel

theorem rowCheck10554 : row10554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10554 := by decide +kernel

theorem rowEval10554 (x : Key → ℝ) : Integer.Sparse.eval row10554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10554, Integer.Sparse.eval_collectBalanced, rawRowCheck10554]

theorem rawRowCheck10555 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form16 = rawRow10555 := by decide +kernel

theorem rowCheck10555 : row10555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10555 := by decide +kernel

theorem rowEval10555 (x : Key → ℝ) : Integer.Sparse.eval row10555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10555, Integer.Sparse.eval_collectBalanced, rawRowCheck10555]

theorem rawRowCheck10556 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form16 = rawRow10556 := by decide +kernel

theorem rowCheck10556 : row10556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10556 := by decide +kernel

theorem rowEval10556 (x : Key → ℝ) : Integer.Sparse.eval row10556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10556, Integer.Sparse.eval_collectBalanced, rawRowCheck10556]

theorem rawRowCheck10557 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form16 = rawRow10557 := by decide +kernel

theorem rowCheck10557 : row10557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10557 := by decide +kernel

theorem rowEval10557 (x : Key → ℝ) : Integer.Sparse.eval row10557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10557, Integer.Sparse.eval_collectBalanced, rawRowCheck10557]

theorem rawRowCheck10558 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form16 = rawRow10558 := by decide +kernel

theorem rowCheck10558 : row10558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10558 := by decide +kernel

theorem rowEval10558 (x : Key → ℝ) : Integer.Sparse.eval row10558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10558, Integer.Sparse.eval_collectBalanced, rawRowCheck10558]

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

theorem entryCheck19_16 : entry19_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_16 k)) := by decide +kernel

theorem rowsSound19_16 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval10549 x
  · exact rowEval10550 x
  · exact rowEval10551 x
  · exact rowEval10552 x
  · exact rowEval10553 x
  · exact rowEval10554 x
  · exact rowEval10555 x
  · exact rowEval10556 x
  · exact rowEval10557 x
  · exact rowEval10558 x

theorem entryEval19_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_16 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck19_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_16]

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

theorem rawRowCheck10669 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form16 = rawRow10669 := by decide +kernel

theorem rowCheck10669 : row10669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10669 := by decide +kernel

theorem rowEval10669 (x : Key → ℝ) : Integer.Sparse.eval row10669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form16) x := by
  rw [rowCheck10669, Integer.Sparse.eval_collectBalanced, rawRowCheck10669]

theorem rawRowCheck10670 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form16 = rawRow10670 := by decide +kernel

theorem rowCheck10670 : row10670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10670 := by decide +kernel

theorem rowEval10670 (x : Key → ℝ) : Integer.Sparse.eval row10670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10670, Integer.Sparse.eval_collectBalanced, rawRowCheck10670]

theorem rawRowCheck10671 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form16 = rawRow10671 := by decide +kernel

theorem rowCheck10671 : row10671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10671 := by decide +kernel

theorem rowEval10671 (x : Key → ℝ) : Integer.Sparse.eval row10671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10671, Integer.Sparse.eval_collectBalanced, rawRowCheck10671]

theorem rawRowCheck10672 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form16 = rawRow10672 := by decide +kernel

theorem rowCheck10672 : row10672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10672 := by decide +kernel

theorem rowEval10672 (x : Key → ℝ) : Integer.Sparse.eval row10672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10672, Integer.Sparse.eval_collectBalanced, rawRowCheck10672]

theorem rawRowCheck10673 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form16 = rawRow10673 := by decide +kernel

theorem rowCheck10673 : row10673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10673 := by decide +kernel

theorem rowEval10673 (x : Key → ℝ) : Integer.Sparse.eval row10673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10673, Integer.Sparse.eval_collectBalanced, rawRowCheck10673]

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

theorem entryCheck20_16 : entry20_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_16 k)) := by decide +kernel

theorem rowsSound20_16 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval10669 x
  · exact rowEval10670 x
  · exact rowEval10671 x
  · exact rowEval10672 x
  · exact rowEval10673 x

theorem entryEval20_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_16 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck20_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_16]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11270 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form16 = rawRow11270 := by decide +kernel

theorem rowCheck11270 : row11270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11270 := by decide +kernel

theorem rowEval11270 (x : Key → ℝ) : Integer.Sparse.eval row11270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11270, Integer.Sparse.eval_collectBalanced, rawRowCheck11270]

theorem rawRowCheck11271 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form16 = rawRow11271 := by decide +kernel

theorem rowCheck11271 : row11271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11271 := by decide +kernel

theorem rowEval11271 (x : Key → ℝ) : Integer.Sparse.eval row11271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11271, Integer.Sparse.eval_collectBalanced, rawRowCheck11271]

theorem rawRowCheck11272 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form16 = rawRow11272 := by decide +kernel

theorem rowCheck11272 : row11272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11272 := by decide +kernel

theorem rowEval11272 (x : Key → ℝ) : Integer.Sparse.eval row11272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11272, Integer.Sparse.eval_collectBalanced, rawRowCheck11272]

theorem rawRowCheck11273 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form16 = rawRow11273 := by decide +kernel

theorem rowCheck11273 : row11273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11273 := by decide +kernel

theorem rowEval11273 (x : Key → ℝ) : Integer.Sparse.eval row11273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11273, Integer.Sparse.eval_collectBalanced, rawRowCheck11273]

theorem rawRowCheck11274 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form16 = rawRow11274 := by decide +kernel

theorem rowCheck11274 : row11274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11274 := by decide +kernel

theorem rowEval11274 (x : Key → ℝ) : Integer.Sparse.eval row11274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11274, Integer.Sparse.eval_collectBalanced, rawRowCheck11274]

theorem rawRowCheck11275 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form16 = rawRow11275 := by decide +kernel

theorem rowCheck11275 : row11275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11275 := by decide +kernel

theorem rowEval11275 (x : Key → ℝ) : Integer.Sparse.eval row11275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11275, Integer.Sparse.eval_collectBalanced, rawRowCheck11275]

theorem rawRowCheck11276 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form16 = rawRow11276 := by decide +kernel

theorem rowCheck11276 : row11276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11276 := by decide +kernel

theorem rowEval11276 (x : Key → ℝ) : Integer.Sparse.eval row11276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11276, Integer.Sparse.eval_collectBalanced, rawRowCheck11276]

theorem rawRowCheck11277 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form16 = rawRow11277 := by decide +kernel

theorem rowCheck11277 : row11277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11277 := by decide +kernel

theorem rowEval11277 (x : Key → ℝ) : Integer.Sparse.eval row11277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11277, Integer.Sparse.eval_collectBalanced, rawRowCheck11277]

theorem rawRowCheck11278 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form16 = rawRow11278 := by decide +kernel

theorem rowCheck11278 : row11278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11278 := by decide +kernel

theorem rowEval11278 (x : Key → ℝ) : Integer.Sparse.eval row11278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11278, Integer.Sparse.eval_collectBalanced, rawRowCheck11278]

theorem rawRowCheck11279 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form16 = rawRow11279 := by decide +kernel

theorem rowCheck11279 : row11279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11279 := by decide +kernel

theorem rowEval11279 (x : Key → ℝ) : Integer.Sparse.eval row11279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11279, Integer.Sparse.eval_collectBalanced, rawRowCheck11279]

theorem rawRowCheck11280 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form16 = rawRow11280 := by decide +kernel

theorem rowCheck11280 : row11280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11280 := by decide +kernel

theorem rowEval11280 (x : Key → ℝ) : Integer.Sparse.eval row11280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11280, Integer.Sparse.eval_collectBalanced, rawRowCheck11280]

theorem rawRowCheck11281 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form16 = rawRow11281 := by decide +kernel

theorem rowCheck11281 : row11281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11281 := by decide +kernel

theorem rowEval11281 (x : Key → ℝ) : Integer.Sparse.eval row11281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11281, Integer.Sparse.eval_collectBalanced, rawRowCheck11281]

theorem rawRowCheck11282 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form16 = rawRow11282 := by decide +kernel

theorem rowCheck11282 : row11282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11282 := by decide +kernel

theorem rowEval11282 (x : Key → ℝ) : Integer.Sparse.eval row11282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11282, Integer.Sparse.eval_collectBalanced, rawRowCheck11282]

theorem rawRowCheck11283 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form16 = rawRow11283 := by decide +kernel

theorem rowCheck11283 : row11283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11283 := by decide +kernel

theorem rowEval11283 (x : Key → ℝ) : Integer.Sparse.eval row11283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11283, Integer.Sparse.eval_collectBalanced, rawRowCheck11283]

theorem rawRowCheck11284 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form16 = rawRow11284 := by decide +kernel

theorem rowCheck11284 : row11284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11284 := by decide +kernel

theorem rowEval11284 (x : Key → ℝ) : Integer.Sparse.eval row11284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11284, Integer.Sparse.eval_collectBalanced, rawRowCheck11284]

theorem rawRowCheck11285 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form16 = rawRow11285 := by decide +kernel

theorem rowCheck11285 : row11285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11285 := by decide +kernel

theorem rowEval11285 (x : Key → ℝ) : Integer.Sparse.eval row11285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11285, Integer.Sparse.eval_collectBalanced, rawRowCheck11285]

theorem rawRowCheck11286 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form16 = rawRow11286 := by decide +kernel

theorem rowCheck11286 : row11286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11286 := by decide +kernel

theorem rowEval11286 (x : Key → ℝ) : Integer.Sparse.eval row11286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11286, Integer.Sparse.eval_collectBalanced, rawRowCheck11286]

theorem rawRowCheck11287 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form16 = rawRow11287 := by decide +kernel

theorem rowCheck11287 : row11287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11287 := by decide +kernel

theorem rowEval11287 (x : Key → ℝ) : Integer.Sparse.eval row11287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11287, Integer.Sparse.eval_collectBalanced, rawRowCheck11287]

theorem rawRowCheck11288 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form16 = rawRow11288 := by decide +kernel

theorem rowCheck11288 : row11288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11288 := by decide +kernel

theorem rowEval11288 (x : Key → ℝ) : Integer.Sparse.eval row11288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11288, Integer.Sparse.eval_collectBalanced, rawRowCheck11288]

theorem rawRowCheck11289 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form16 = rawRow11289 := by decide +kernel

theorem rowCheck11289 : row11289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11289 := by decide +kernel

theorem rowEval11289 (x : Key → ℝ) : Integer.Sparse.eval row11289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11289, Integer.Sparse.eval_collectBalanced, rawRowCheck11289]

theorem rawRowCheck11290 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form16 = rawRow11290 := by decide +kernel

theorem rowCheck11290 : row11290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11290 := by decide +kernel

theorem rowEval11290 (x : Key → ℝ) : Integer.Sparse.eval row11290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11290, Integer.Sparse.eval_collectBalanced, rawRowCheck11290]

theorem rawRowCheck11291 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form16 = rawRow11291 := by decide +kernel

theorem rowCheck11291 : row11291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11291 := by decide +kernel

theorem rowEval11291 (x : Key → ℝ) : Integer.Sparse.eval row11291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11291, Integer.Sparse.eval_collectBalanced, rawRowCheck11291]

theorem rawRowCheck11292 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form16 = rawRow11292 := by decide +kernel

theorem rowCheck11292 : row11292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11292 := by decide +kernel

theorem rowEval11292 (x : Key → ℝ) : Integer.Sparse.eval row11292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11292, Integer.Sparse.eval_collectBalanced, rawRowCheck11292]

theorem rawRowCheck11293 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form16 = rawRow11293 := by decide +kernel

theorem rowCheck11293 : row11293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11293 := by decide +kernel

theorem rowEval11293 (x : Key → ℝ) : Integer.Sparse.eval row11293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11293, Integer.Sparse.eval_collectBalanced, rawRowCheck11293]

theorem rawRowCheck11294 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form16 = rawRow11294 := by decide +kernel

theorem rowCheck11294 : row11294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11294 := by decide +kernel

theorem rowEval11294 (x : Key → ℝ) : Integer.Sparse.eval row11294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11294, Integer.Sparse.eval_collectBalanced, rawRowCheck11294]

theorem rawRowCheck11295 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form16 = rawRow11295 := by decide +kernel

theorem rowCheck11295 : row11295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11295 := by decide +kernel

theorem rowEval11295 (x : Key → ℝ) : Integer.Sparse.eval row11295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11295, Integer.Sparse.eval_collectBalanced, rawRowCheck11295]

theorem rawRowCheck11296 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form16 = rawRow11296 := by decide +kernel

theorem rowCheck11296 : row11296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11296 := by decide +kernel

theorem rowEval11296 (x : Key → ℝ) : Integer.Sparse.eval row11296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11296, Integer.Sparse.eval_collectBalanced, rawRowCheck11296]

theorem rawRowCheck11297 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow11297 := by decide +kernel

theorem rowCheck11297 : row11297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11297 := by decide +kernel

theorem rowEval11297 (x : Key → ℝ) : Integer.Sparse.eval row11297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11297, Integer.Sparse.eval_collectBalanced, rawRowCheck11297]

theorem rawRowCheck11298 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow11298 := by decide +kernel

theorem rowCheck11298 : row11298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11298 := by decide +kernel

theorem rowEval11298 (x : Key → ℝ) : Integer.Sparse.eval row11298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11298, Integer.Sparse.eval_collectBalanced, rawRowCheck11298]

theorem rawRowCheck11299 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow11299 := by decide +kernel

theorem rowCheck11299 : row11299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11299 := by decide +kernel

theorem rowEval11299 (x : Key → ℝ) : Integer.Sparse.eval row11299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11299, Integer.Sparse.eval_collectBalanced, rawRowCheck11299]

theorem rawRowCheck11300 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form16 = rawRow11300 := by decide +kernel

theorem rowCheck11300 : row11300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11300 := by decide +kernel

theorem rowEval11300 (x : Key → ℝ) : Integer.Sparse.eval row11300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11300, Integer.Sparse.eval_collectBalanced, rawRowCheck11300]

theorem rawRowCheck11301 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form16 = rawRow11301 := by decide +kernel

theorem rowCheck11301 : row11301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11301 := by decide +kernel

theorem rowEval11301 (x : Key → ℝ) : Integer.Sparse.eval row11301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11301, Integer.Sparse.eval_collectBalanced, rawRowCheck11301]

theorem rawRowCheck11302 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form16 = rawRow11302 := by decide +kernel

theorem rowCheck11302 : row11302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11302 := by decide +kernel

theorem rowEval11302 (x : Key → ℝ) : Integer.Sparse.eval row11302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11302, Integer.Sparse.eval_collectBalanced, rawRowCheck11302]

theorem rawRowCheck11303 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form16 = rawRow11303 := by decide +kernel

theorem rowCheck11303 : row11303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11303 := by decide +kernel

theorem rowEval11303 (x : Key → ℝ) : Integer.Sparse.eval row11303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11303, Integer.Sparse.eval_collectBalanced, rawRowCheck11303]

theorem rawRowCheck11304 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form16 = rawRow11304 := by decide +kernel

theorem rowCheck11304 : row11304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11304 := by decide +kernel

theorem rowEval11304 (x : Key → ℝ) : Integer.Sparse.eval row11304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11304, Integer.Sparse.eval_collectBalanced, rawRowCheck11304]

theorem rawRowCheck11305 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form16 = rawRow11305 := by decide +kernel

theorem rowCheck11305 : row11305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11305 := by decide +kernel

theorem rowEval11305 (x : Key → ℝ) : Integer.Sparse.eval row11305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11305, Integer.Sparse.eval_collectBalanced, rawRowCheck11305]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck21_16 : entry21_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_16 k)) := by decide +kernel

theorem rowsSound21_16 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval11270 x
  · exact rowEval11271 x
  · exact rowEval11272 x
  · exact rowEval11273 x
  · exact rowEval11274 x
  · exact rowEval11275 x
  · exact rowEval11276 x
  · exact rowEval11277 x
  · exact rowEval11278 x
  · exact rowEval11279 x
  · exact rowEval11280 x
  · exact rowEval11281 x
  · exact rowEval11282 x
  · exact rowEval11283 x
  · exact rowEval11284 x
  · exact rowEval11285 x
  · exact rowEval11286 x
  · exact rowEval11287 x
  · exact rowEval11288 x
  · exact rowEval11289 x
  · exact rowEval11290 x
  · exact rowEval11291 x
  · exact rowEval11292 x
  · exact rowEval11293 x
  · exact rowEval11294 x
  · exact rowEval11295 x
  · exact rowEval11296 x
  · exact rowEval11297 x
  · exact rowEval11298 x
  · exact rowEval11299 x
  · exact rowEval11300 x
  · exact rowEval11301 x
  · exact rowEval11302 x
  · exact rowEval11303 x
  · exact rowEval11304 x
  · exact rowEval11305 x

theorem entryEval21_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_16 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck21_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_16]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11678 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form16 = rawRow11678 := by decide +kernel

theorem rowCheck11678 : row11678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11678 := by decide +kernel

theorem rowEval11678 (x : Key → ℝ) : Integer.Sparse.eval row11678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11678, Integer.Sparse.eval_collectBalanced, rawRowCheck11678]

theorem rawRowCheck11679 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form16 = rawRow11679 := by decide +kernel

theorem rowCheck11679 : row11679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11679 := by decide +kernel

theorem rowEval11679 (x : Key → ℝ) : Integer.Sparse.eval row11679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11679, Integer.Sparse.eval_collectBalanced, rawRowCheck11679]

theorem rawRowCheck11680 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form16 = rawRow11680 := by decide +kernel

theorem rowCheck11680 : row11680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11680 := by decide +kernel

theorem rowEval11680 (x : Key → ℝ) : Integer.Sparse.eval row11680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11680, Integer.Sparse.eval_collectBalanced, rawRowCheck11680]

theorem rawRowCheck11681 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form16 = rawRow11681 := by decide +kernel

theorem rowCheck11681 : row11681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11681 := by decide +kernel

theorem rowEval11681 (x : Key → ℝ) : Integer.Sparse.eval row11681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11681, Integer.Sparse.eval_collectBalanced, rawRowCheck11681]

theorem rawRowCheck11682 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form16 = rawRow11682 := by decide +kernel

theorem rowCheck11682 : row11682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11682 := by decide +kernel

theorem rowEval11682 (x : Key → ℝ) : Integer.Sparse.eval row11682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11682, Integer.Sparse.eval_collectBalanced, rawRowCheck11682]

theorem rawRowCheck11683 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form16 = rawRow11683 := by decide +kernel

theorem rowCheck11683 : row11683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11683 := by decide +kernel

theorem rowEval11683 (x : Key → ℝ) : Integer.Sparse.eval row11683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11683, Integer.Sparse.eval_collectBalanced, rawRowCheck11683]

theorem rawRowCheck11684 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form16 = rawRow11684 := by decide +kernel

theorem rowCheck11684 : row11684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11684 := by decide +kernel

theorem rowEval11684 (x : Key → ℝ) : Integer.Sparse.eval row11684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11684, Integer.Sparse.eval_collectBalanced, rawRowCheck11684]

theorem rawRowCheck11685 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form16 = rawRow11685 := by decide +kernel

theorem rowCheck11685 : row11685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11685 := by decide +kernel

theorem rowEval11685 (x : Key → ℝ) : Integer.Sparse.eval row11685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11685, Integer.Sparse.eval_collectBalanced, rawRowCheck11685]

theorem rawRowCheck11686 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form16 = rawRow11686 := by decide +kernel

theorem rowCheck11686 : row11686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11686 := by decide +kernel

theorem rowEval11686 (x : Key → ℝ) : Integer.Sparse.eval row11686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11686, Integer.Sparse.eval_collectBalanced, rawRowCheck11686]

theorem rawRowCheck11687 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow11687 := by decide +kernel

theorem rowCheck11687 : row11687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11687 := by decide +kernel

theorem rowEval11687 (x : Key → ℝ) : Integer.Sparse.eval row11687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11687, Integer.Sparse.eval_collectBalanced, rawRowCheck11687]

theorem rawRowCheck11688 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow11688 := by decide +kernel

theorem rowCheck11688 : row11688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11688 := by decide +kernel

theorem rowEval11688 (x : Key → ℝ) : Integer.Sparse.eval row11688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11688, Integer.Sparse.eval_collectBalanced, rawRowCheck11688]

theorem rawRowCheck11689 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow11689 := by decide +kernel

theorem rowCheck11689 : row11689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11689 := by decide +kernel

theorem rowEval11689 (x : Key → ℝ) : Integer.Sparse.eval row11689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11689, Integer.Sparse.eval_collectBalanced, rawRowCheck11689]

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

theorem entryCheck22_16 : entry22_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_16 k)) := by decide +kernel

theorem rowsSound22_16 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval11678 x
  · exact rowEval11679 x
  · exact rowEval11680 x
  · exact rowEval11681 x
  · exact rowEval11682 x
  · exact rowEval11683 x
  · exact rowEval11684 x
  · exact rowEval11685 x
  · exact rowEval11686 x
  · exact rowEval11687 x
  · exact rowEval11688 x
  · exact rowEval11689 x
  · exact rowEval11270 x
  · exact rowEval11271 x
  · exact rowEval11272 x
  · exact rowEval11273 x
  · exact rowEval11274 x
  · exact rowEval11275 x
  · exact rowEval11276 x
  · exact rowEval11277 x
  · exact rowEval11278 x
  · exact rowEval11279 x
  · exact rowEval11280 x
  · exact rowEval11281 x
  · exact rowEval11282 x
  · exact rowEval11283 x
  · exact rowEval11284 x
  · exact rowEval11285 x
  · exact rowEval11286 x
  · exact rowEval11287 x
  · exact rowEval11288 x
  · exact rowEval11289 x
  · exact rowEval11290 x
  · exact rowEval11291 x
  · exact rowEval11292 x
  · exact rowEval11293 x

theorem entryEval22_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_16 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck22_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_16]

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

theorem rawRowCheck12062 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12062 := by decide +kernel

theorem rowCheck12062 : row12062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12062 := by decide +kernel

theorem rowEval12062 (x : Key → ℝ) : Integer.Sparse.eval row12062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12062, Integer.Sparse.eval_collectBalanced, rawRowCheck12062]

theorem rawRowCheck12063 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12063 := by decide +kernel

theorem rowCheck12063 : row12063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12063 := by decide +kernel

theorem rowEval12063 (x : Key → ℝ) : Integer.Sparse.eval row12063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12063, Integer.Sparse.eval_collectBalanced, rawRowCheck12063]

theorem rawRowCheck12064 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12064 := by decide +kernel

theorem rowCheck12064 : row12064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12064 := by decide +kernel

theorem rowEval12064 (x : Key → ℝ) : Integer.Sparse.eval row12064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12064, Integer.Sparse.eval_collectBalanced, rawRowCheck12064]

theorem rawRowCheck12065 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form16 = rawRow12065 := by decide +kernel

theorem rowCheck12065 : row12065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12065 := by decide +kernel

theorem rowEval12065 (x : Key → ℝ) : Integer.Sparse.eval row12065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12065, Integer.Sparse.eval_collectBalanced, rawRowCheck12065]

theorem rawRowCheck12066 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form16 = rawRow12066 := by decide +kernel

theorem rowCheck12066 : row12066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12066 := by decide +kernel

theorem rowEval12066 (x : Key → ℝ) : Integer.Sparse.eval row12066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12066, Integer.Sparse.eval_collectBalanced, rawRowCheck12066]

theorem rawRowCheck12067 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form16 = rawRow12067 := by decide +kernel

theorem rowCheck12067 : row12067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12067 := by decide +kernel

theorem rowEval12067 (x : Key → ℝ) : Integer.Sparse.eval row12067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12067, Integer.Sparse.eval_collectBalanced, rawRowCheck12067]

theorem rawRowCheck12068 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12068 := by decide +kernel

theorem rowCheck12068 : row12068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12068 := by decide +kernel

theorem rowEval12068 (x : Key → ℝ) : Integer.Sparse.eval row12068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12068, Integer.Sparse.eval_collectBalanced, rawRowCheck12068]

theorem rawRowCheck12069 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12069 := by decide +kernel

theorem rowCheck12069 : row12069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12069 := by decide +kernel

theorem rowEval12069 (x : Key → ℝ) : Integer.Sparse.eval row12069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12069, Integer.Sparse.eval_collectBalanced, rawRowCheck12069]

theorem rawRowCheck12070 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12070 := by decide +kernel

theorem rowCheck12070 : row12070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12070 := by decide +kernel

theorem rowEval12070 (x : Key → ℝ) : Integer.Sparse.eval row12070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12070, Integer.Sparse.eval_collectBalanced, rawRowCheck12070]

theorem rawRowCheck12071 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16 = rawRow12071 := by decide +kernel

theorem rowCheck12071 : row12071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12071 := by decide +kernel

theorem rowEval12071 (x : Key → ℝ) : Integer.Sparse.eval row12071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12071, Integer.Sparse.eval_collectBalanced, rawRowCheck12071]

theorem rawRowCheck12072 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16 = rawRow12072 := by decide +kernel

theorem rowCheck12072 : row12072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12072 := by decide +kernel

theorem rowEval12072 (x : Key → ℝ) : Integer.Sparse.eval row12072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12072, Integer.Sparse.eval_collectBalanced, rawRowCheck12072]

theorem rawRowCheck12073 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16 = rawRow12073 := by decide +kernel

theorem rowCheck12073 : row12073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12073 := by decide +kernel

theorem rowEval12073 (x : Key → ℝ) : Integer.Sparse.eval row12073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12073, Integer.Sparse.eval_collectBalanced, rawRowCheck12073]

theorem rawRowCheck12074 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16 = rawRow12074 := by decide +kernel

theorem rowCheck12074 : row12074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12074 := by decide +kernel

theorem rowEval12074 (x : Key → ℝ) : Integer.Sparse.eval row12074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12074, Integer.Sparse.eval_collectBalanced, rawRowCheck12074]

theorem rawRowCheck12075 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16 = rawRow12075 := by decide +kernel

theorem rowCheck12075 : row12075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12075 := by decide +kernel

theorem rowEval12075 (x : Key → ℝ) : Integer.Sparse.eval row12075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12075, Integer.Sparse.eval_collectBalanced, rawRowCheck12075]

theorem rawRowCheck12076 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16 = rawRow12076 := by decide +kernel

theorem rowCheck12076 : row12076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12076 := by decide +kernel

theorem rowEval12076 (x : Key → ℝ) : Integer.Sparse.eval row12076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12076, Integer.Sparse.eval_collectBalanced, rawRowCheck12076]

theorem rawRowCheck12077 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16 = rawRow12077 := by decide +kernel

theorem rowCheck12077 : row12077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12077 := by decide +kernel

theorem rowEval12077 (x : Key → ℝ) : Integer.Sparse.eval row12077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12077, Integer.Sparse.eval_collectBalanced, rawRowCheck12077]

theorem rawRowCheck12078 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16 = rawRow12078 := by decide +kernel

theorem rowCheck12078 : row12078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12078 := by decide +kernel

theorem rowEval12078 (x : Key → ℝ) : Integer.Sparse.eval row12078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12078, Integer.Sparse.eval_collectBalanced, rawRowCheck12078]

theorem rawRowCheck12079 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16 = rawRow12079 := by decide +kernel

theorem rowCheck12079 : row12079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12079 := by decide +kernel

theorem rowEval12079 (x : Key → ℝ) : Integer.Sparse.eval row12079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12079, Integer.Sparse.eval_collectBalanced, rawRowCheck12079]

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

theorem rawRowCheck12286 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form16 = rawRow12286 := by decide +kernel

theorem rowCheck12286 : row12286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12286 := by decide +kernel

theorem rowEval12286 (x : Key → ℝ) : Integer.Sparse.eval row12286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12286, Integer.Sparse.eval_collectBalanced, rawRowCheck12286]

theorem rawRowCheck12287 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form16 = rawRow12287 := by decide +kernel

theorem rowCheck12287 : row12287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12287 := by decide +kernel

theorem rowEval12287 (x : Key → ℝ) : Integer.Sparse.eval row12287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12287, Integer.Sparse.eval_collectBalanced, rawRowCheck12287]

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

theorem entryCheck23_16 : entry23_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_16 k)) := by decide +kernel

theorem rowsSound23_16 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12062 x
  · exact rowEval12063 x
  · exact rowEval12064 x
  · exact rowEval12065 x
  · exact rowEval12066 x
  · exact rowEval12067 x
  · exact rowEval12068 x
  · exact rowEval12069 x
  · exact rowEval12070 x
  · exact rowEval12071 x
  · exact rowEval12072 x
  · exact rowEval12073 x
  · exact rowEval12074 x
  · exact rowEval12075 x
  · exact rowEval12076 x
  · exact rowEval12077 x
  · exact rowEval12078 x
  · exact rowEval12079 x

theorem entryEval23_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_16 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck23_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_16]

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

theorem rawRowCheck12288 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form16 = rawRow12288 := by decide +kernel

theorem rowCheck12288 : row12288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12288 := by decide +kernel

theorem rowEval12288 (x : Key → ℝ) : Integer.Sparse.eval row12288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12288, Integer.Sparse.eval_collectBalanced, rawRowCheck12288]

theorem rawRowCheck12289 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form16 = rawRow12289 := by decide +kernel

theorem rowCheck12289 : row12289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12289 := by decide +kernel

theorem rowEval12289 (x : Key → ℝ) : Integer.Sparse.eval row12289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12289, Integer.Sparse.eval_collectBalanced, rawRowCheck12289]

theorem rawRowCheck12290 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form16 = rawRow12290 := by decide +kernel

theorem rowCheck12290 : row12290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12290 := by decide +kernel

theorem rowEval12290 (x : Key → ℝ) : Integer.Sparse.eval row12290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12290, Integer.Sparse.eval_collectBalanced, rawRowCheck12290]

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

theorem entryCheck24_16 : entry24_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_16 k)) := by decide +kernel

theorem rowsSound24_16 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12286 x
  · exact rowEval12287 x
  · exact rowEval12288 x
  · exact rowEval12289 x
  · exact rowEval12290 x

theorem entryEval24_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_16 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck24_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_16]

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

theorem rawRowCheck12459 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form16 = rawRow12459 := by decide +kernel

theorem rowCheck12459 : row12459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12459 := by decide +kernel

theorem rowEval12459 (x : Key → ℝ) : Integer.Sparse.eval row12459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12459, Integer.Sparse.eval_collectBalanced, rawRowCheck12459]

theorem rawRowCheck12460 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form16 = rawRow12460 := by decide +kernel

theorem rowCheck12460 : row12460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12460 := by decide +kernel

theorem rowEval12460 (x : Key → ℝ) : Integer.Sparse.eval row12460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12460, Integer.Sparse.eval_collectBalanced, rawRowCheck12460]

theorem rawRowCheck12461 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form16 = rawRow12461 := by decide +kernel

theorem rowCheck12461 : row12461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12461 := by decide +kernel

theorem rowEval12461 (x : Key → ℝ) : Integer.Sparse.eval row12461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12461, Integer.Sparse.eval_collectBalanced, rawRowCheck12461]

theorem rawRowCheck12462 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form16 = rawRow12462 := by decide +kernel

theorem rowCheck12462 : row12462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12462 := by decide +kernel

theorem rowEval12462 (x : Key → ℝ) : Integer.Sparse.eval row12462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12462, Integer.Sparse.eval_collectBalanced, rawRowCheck12462]

theorem rawRowCheck12463 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form16 = rawRow12463 := by decide +kernel

theorem rowCheck12463 : row12463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12463 := by decide +kernel

theorem rowEval12463 (x : Key → ℝ) : Integer.Sparse.eval row12463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12463, Integer.Sparse.eval_collectBalanced, rawRowCheck12463]

theorem rawRowCheck12464 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form16 = rawRow12464 := by decide +kernel

theorem rowCheck12464 : row12464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12464 := by decide +kernel

theorem rowEval12464 (x : Key → ℝ) : Integer.Sparse.eval row12464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12464, Integer.Sparse.eval_collectBalanced, rawRowCheck12464]

theorem rawRowCheck12465 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form16 = rawRow12465 := by decide +kernel

theorem rowCheck12465 : row12465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12465 := by decide +kernel

theorem rowEval12465 (x : Key → ℝ) : Integer.Sparse.eval row12465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12465, Integer.Sparse.eval_collectBalanced, rawRowCheck12465]

theorem rawRowCheck12466 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form16 = rawRow12466 := by decide +kernel

theorem rowCheck12466 : row12466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12466 := by decide +kernel

theorem rowEval12466 (x : Key → ℝ) : Integer.Sparse.eval row12466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12466, Integer.Sparse.eval_collectBalanced, rawRowCheck12466]

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

theorem entryCheck25_16 : entry25_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_16 k)) := by decide +kernel

theorem rowsSound25_16 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12459 x
  · exact rowEval12460 x
  · exact rowEval12461 x
  · exact rowEval12462 x
  · exact rowEval12463 x
  · exact rowEval12464 x
  · exact rowEval12465 x
  · exact rowEval12466 x

theorem entryEval25_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_16 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck25_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_16]

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

theorem rawRowCheck12923 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12923 := by decide +kernel

theorem rowCheck12923 : row12923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12923 := by decide +kernel

theorem rowEval12923 (x : Key → ℝ) : Integer.Sparse.eval row12923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12923, Integer.Sparse.eval_collectBalanced, rawRowCheck12923]

theorem rawRowCheck12924 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12924 := by decide +kernel

theorem rowCheck12924 : row12924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12924 := by decide +kernel

theorem rowEval12924 (x : Key → ℝ) : Integer.Sparse.eval row12924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12924, Integer.Sparse.eval_collectBalanced, rawRowCheck12924]

theorem rawRowCheck12925 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12925 := by decide +kernel

theorem rowCheck12925 : row12925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12925 := by decide +kernel

theorem rowEval12925 (x : Key → ℝ) : Integer.Sparse.eval row12925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12925, Integer.Sparse.eval_collectBalanced, rawRowCheck12925]

theorem rawRowCheck12926 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form16 = rawRow12926 := by decide +kernel

theorem rowCheck12926 : row12926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12926 := by decide +kernel

theorem rowEval12926 (x : Key → ℝ) : Integer.Sparse.eval row12926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12926, Integer.Sparse.eval_collectBalanced, rawRowCheck12926]

theorem rawRowCheck12927 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form16 = rawRow12927 := by decide +kernel

theorem rowCheck12927 : row12927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12927 := by decide +kernel

theorem rowEval12927 (x : Key → ℝ) : Integer.Sparse.eval row12927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12927, Integer.Sparse.eval_collectBalanced, rawRowCheck12927]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12928 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form16 = rawRow12928 := by decide +kernel

theorem rowCheck12928 : row12928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12928 := by decide +kernel

theorem rowEval12928 (x : Key → ℝ) : Integer.Sparse.eval row12928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12928, Integer.Sparse.eval_collectBalanced, rawRowCheck12928]

theorem rawRowCheck12929 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form16 = rawRow12929 := by decide +kernel

theorem rowCheck12929 : row12929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12929 := by decide +kernel

theorem rowEval12929 (x : Key → ℝ) : Integer.Sparse.eval row12929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12929, Integer.Sparse.eval_collectBalanced, rawRowCheck12929]

theorem rawRowCheck12930 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form16 = rawRow12930 := by decide +kernel

theorem rowCheck12930 : row12930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12930 := by decide +kernel

theorem rowEval12930 (x : Key → ℝ) : Integer.Sparse.eval row12930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12930, Integer.Sparse.eval_collectBalanced, rawRowCheck12930]

theorem rawRowCheck12931 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form16 = rawRow12931 := by decide +kernel

theorem rowCheck12931 : row12931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12931 := by decide +kernel

theorem rowEval12931 (x : Key → ℝ) : Integer.Sparse.eval row12931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12931, Integer.Sparse.eval_collectBalanced, rawRowCheck12931]

theorem rawRowCheck12932 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form16 = rawRow12932 := by decide +kernel

theorem rowCheck12932 : row12932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12932 := by decide +kernel

theorem rowEval12932 (x : Key → ℝ) : Integer.Sparse.eval row12932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12932, Integer.Sparse.eval_collectBalanced, rawRowCheck12932]

theorem rawRowCheck12933 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form16 = rawRow12933 := by decide +kernel

theorem rowCheck12933 : row12933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12933 := by decide +kernel

theorem rowEval12933 (x : Key → ℝ) : Integer.Sparse.eval row12933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12933, Integer.Sparse.eval_collectBalanced, rawRowCheck12933]

theorem rawRowCheck12934 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form16 = rawRow12934 := by decide +kernel

theorem rowCheck12934 : row12934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12934 := by decide +kernel

theorem rowEval12934 (x : Key → ℝ) : Integer.Sparse.eval row12934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12934, Integer.Sparse.eval_collectBalanced, rawRowCheck12934]

theorem rawRowCheck12935 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form16 = rawRow12935 := by decide +kernel

theorem rowCheck12935 : row12935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12935 := by decide +kernel

theorem rowEval12935 (x : Key → ℝ) : Integer.Sparse.eval row12935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12935, Integer.Sparse.eval_collectBalanced, rawRowCheck12935]

theorem rawRowCheck12936 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form16 = rawRow12936 := by decide +kernel

theorem rowCheck12936 : row12936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12936 := by decide +kernel

theorem rowEval12936 (x : Key → ℝ) : Integer.Sparse.eval row12936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12936, Integer.Sparse.eval_collectBalanced, rawRowCheck12936]

theorem rawRowCheck12937 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form16 = rawRow12937 := by decide +kernel

theorem rowCheck12937 : row12937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12937 := by decide +kernel

theorem rowEval12937 (x : Key → ℝ) : Integer.Sparse.eval row12937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12937, Integer.Sparse.eval_collectBalanced, rawRowCheck12937]

theorem rawRowCheck12938 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form16 = rawRow12938 := by decide +kernel

theorem rowCheck12938 : row12938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12938 := by decide +kernel

theorem rowEval12938 (x : Key → ℝ) : Integer.Sparse.eval row12938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12938, Integer.Sparse.eval_collectBalanced, rawRowCheck12938]

theorem rawRowCheck12939 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form16 = rawRow12939 := by decide +kernel

theorem rowCheck12939 : row12939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12939 := by decide +kernel

theorem rowEval12939 (x : Key → ℝ) : Integer.Sparse.eval row12939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12939, Integer.Sparse.eval_collectBalanced, rawRowCheck12939]

theorem rawRowCheck12940 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form16 = rawRow12940 := by decide +kernel

theorem rowCheck12940 : row12940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12940 := by decide +kernel

theorem rowEval12940 (x : Key → ℝ) : Integer.Sparse.eval row12940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12940, Integer.Sparse.eval_collectBalanced, rawRowCheck12940]

theorem rawRowCheck12941 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form16 = rawRow12941 := by decide +kernel

theorem rowCheck12941 : row12941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12941 := by decide +kernel

theorem rowEval12941 (x : Key → ℝ) : Integer.Sparse.eval row12941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12941, Integer.Sparse.eval_collectBalanced, rawRowCheck12941]

theorem rawRowCheck12942 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form16 = rawRow12942 := by decide +kernel

theorem rowCheck12942 : row12942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12942 := by decide +kernel

theorem rowEval12942 (x : Key → ℝ) : Integer.Sparse.eval row12942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12942, Integer.Sparse.eval_collectBalanced, rawRowCheck12942]

theorem rawRowCheck12943 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form16 = rawRow12943 := by decide +kernel

theorem rowCheck12943 : row12943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12943 := by decide +kernel

theorem rowEval12943 (x : Key → ℝ) : Integer.Sparse.eval row12943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12943, Integer.Sparse.eval_collectBalanced, rawRowCheck12943]

theorem rawRowCheck12944 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow12944 := by decide +kernel

theorem rowCheck12944 : row12944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12944 := by decide +kernel

theorem rowEval12944 (x : Key → ℝ) : Integer.Sparse.eval row12944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12944, Integer.Sparse.eval_collectBalanced, rawRowCheck12944]

theorem rawRowCheck12945 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow12945 := by decide +kernel

theorem rowCheck12945 : row12945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12945 := by decide +kernel

theorem rowEval12945 (x : Key → ℝ) : Integer.Sparse.eval row12945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12945, Integer.Sparse.eval_collectBalanced, rawRowCheck12945]

theorem rawRowCheck12946 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow12946 := by decide +kernel

theorem rowCheck12946 : row12946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12946 := by decide +kernel

theorem rowEval12946 (x : Key → ℝ) : Integer.Sparse.eval row12946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12946, Integer.Sparse.eval_collectBalanced, rawRowCheck12946]

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

theorem entryCheck26_16 : entry26_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_16 k)) := by decide +kernel

theorem rowsSound26_16 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12923 x
  · exact rowEval12924 x
  · exact rowEval12925 x
  · exact rowEval12926 x
  · exact rowEval12927 x
  · exact rowEval12928 x
  · exact rowEval12929 x
  · exact rowEval12930 x
  · exact rowEval12931 x
  · exact rowEval12932 x
  · exact rowEval12933 x
  · exact rowEval12934 x
  · exact rowEval12935 x
  · exact rowEval12936 x
  · exact rowEval12937 x
  · exact rowEval12938 x
  · exact rowEval12939 x
  · exact rowEval12940 x
  · exact rowEval12941 x
  · exact rowEval12942 x
  · exact rowEval12943 x
  · exact rowEval12944 x
  · exact rowEval12945 x
  · exact rowEval12946 x

theorem entryEval26_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_16 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck26_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_16]

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

theorem entryEvalRow16_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 16 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 16).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval16_0 B hB
  · exact entryEval16_1 B hB
  · exact entryEval16_2 B hB
  · exact entryEval16_3 B hB
  · exact entryEval16_4 B hB
  · exact entryEval16_5 B hB
  · exact entryEval16_6 B hB
  · exact entryEval16_7 B hB
  · exact entryEval16_8 B hB
  · exact entryEval16_9 B hB
  · exact entryEval16_10 B hB
  · exact entryEval16_11 B hB
  · exact entryEval16_12 B hB
  · exact entryEval16_13 B hB
  · exact entryEval16_14 B hB
  · exact entryEval16_15 B hB
  · exact entryEval16_16 B hB
  · exact (entryEval17_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e_oai
