-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:50:04.771147+00:00
-- url     : https://prove2.me/submissions/1fc00b97-d8cd-472c-8966-6f66b49b8500

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E038
import Definitions.Def_OAIQ106E041
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18449 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18449 := by decide +kernel

theorem rowCheck18449 : row18449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18449 := by decide +kernel

theorem rowEval18449 (x : Key → ℝ) : Integer.Sparse.eval row18449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18449, Integer.Sparse.eval_collectBalanced, rawRowCheck18449]

theorem rawRowCheck18450 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18450 := by decide +kernel

theorem rowCheck18450 : row18450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18450 := by decide +kernel

theorem rowEval18450 (x : Key → ℝ) : Integer.Sparse.eval row18450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18450, Integer.Sparse.eval_collectBalanced, rawRowCheck18450]

theorem rawRowCheck18451 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18451 := by decide +kernel

theorem rowCheck18451 : row18451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18451 := by decide +kernel

theorem rowEval18451 (x : Key → ℝ) : Integer.Sparse.eval row18451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18451, Integer.Sparse.eval_collectBalanced, rawRowCheck18451]

theorem rawRowCheck18452 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18452 := by decide +kernel

theorem rowCheck18452 : row18452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18452 := by decide +kernel

theorem rowEval18452 (x : Key → ℝ) : Integer.Sparse.eval row18452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18452, Integer.Sparse.eval_collectBalanced, rawRowCheck18452]

theorem rawRowCheck18453 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18453 := by decide +kernel

theorem rowCheck18453 : row18453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18453 := by decide +kernel

theorem rowEval18453 (x : Key → ℝ) : Integer.Sparse.eval row18453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18453, Integer.Sparse.eval_collectBalanced, rawRowCheck18453]

theorem rawRowCheck18454 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18454 := by decide +kernel

theorem rowCheck18454 : row18454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18454 := by decide +kernel

theorem rowEval18454 (x : Key → ℝ) : Integer.Sparse.eval row18454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18454, Integer.Sparse.eval_collectBalanced, rawRowCheck18454]

theorem rawRowCheck18455 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18455 := by decide +kernel

theorem rowCheck18455 : row18455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18455 := by decide +kernel

theorem rowEval18455 (x : Key → ℝ) : Integer.Sparse.eval row18455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18455, Integer.Sparse.eval_collectBalanced, rawRowCheck18455]

theorem rawRowCheck18456 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18456 := by decide +kernel

theorem rowCheck18456 : row18456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18456 := by decide +kernel

theorem rowEval18456 (x : Key → ℝ) : Integer.Sparse.eval row18456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18456, Integer.Sparse.eval_collectBalanced, rawRowCheck18456]

theorem rawRowCheck18457 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18457 := by decide +kernel

theorem rowCheck18457 : row18457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18457 := by decide +kernel

theorem rowEval18457 (x : Key → ℝ) : Integer.Sparse.eval row18457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18457, Integer.Sparse.eval_collectBalanced, rawRowCheck18457]

theorem rawRowCheck18458 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18458 := by decide +kernel

theorem rowCheck18458 : row18458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18458 := by decide +kernel

theorem rowEval18458 (x : Key → ℝ) : Integer.Sparse.eval row18458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18458, Integer.Sparse.eval_collectBalanced, rawRowCheck18458]

theorem rawRowCheck18519 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18519 := by decide +kernel

theorem rowCheck18519 : row18519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18519 := by decide +kernel

theorem rowEval18519 (x : Key → ℝ) : Integer.Sparse.eval row18519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18519, Integer.Sparse.eval_collectBalanced, rawRowCheck18519]

theorem rawRowCheck18520 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18520 := by decide +kernel

theorem rowCheck18520 : row18520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18520 := by decide +kernel

theorem rowEval18520 (x : Key → ℝ) : Integer.Sparse.eval row18520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18520, Integer.Sparse.eval_collectBalanced, rawRowCheck18520]

theorem rawRowCheck18521 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18521 := by decide +kernel

theorem rowCheck18521 : row18521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18521 := by decide +kernel

theorem rowEval18521 (x : Key → ℝ) : Integer.Sparse.eval row18521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18521, Integer.Sparse.eval_collectBalanced, rawRowCheck18521]

theorem rawRowCheck18522 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1 = rawRow18522 := by decide +kernel

theorem rowCheck18522 : row18522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18522 := by decide +kernel

theorem rowEval18522 (x : Key → ℝ) : Integer.Sparse.eval row18522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18522, Integer.Sparse.eval_collectBalanced, rawRowCheck18522]

theorem rawRowCheck18523 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1 = rawRow18523 := by decide +kernel

theorem rowCheck18523 : row18523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18523 := by decide +kernel

theorem rowEval18523 (x : Key → ℝ) : Integer.Sparse.eval row18523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18523, Integer.Sparse.eval_collectBalanced, rawRowCheck18523]

theorem rawRowCheck18524 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1 = rawRow18524 := by decide +kernel

theorem rowCheck18524 : row18524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18524 := by decide +kernel

theorem rowEval18524 (x : Key → ℝ) : Integer.Sparse.eval row18524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18524, Integer.Sparse.eval_collectBalanced, rawRowCheck18524]

theorem rawRowCheck18525 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1 = rawRow18525 := by decide +kernel

theorem rowCheck18525 : row18525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18525 := by decide +kernel

theorem rowEval18525 (x : Key → ℝ) : Integer.Sparse.eval row18525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18525, Integer.Sparse.eval_collectBalanced, rawRowCheck18525]

theorem rawRowCheck18526 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1 = rawRow18526 := by decide +kernel

theorem rowCheck18526 : row18526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18526 := by decide +kernel

theorem rowEval18526 (x : Key → ℝ) : Integer.Sparse.eval row18526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18526, Integer.Sparse.eval_collectBalanced, rawRowCheck18526]

theorem rawRowCheck18527 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1 = rawRow18527 := by decide +kernel

theorem rowCheck18527 : row18527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18527 := by decide +kernel

theorem rowEval18527 (x : Key → ℝ) : Integer.Sparse.eval row18527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18527, Integer.Sparse.eval_collectBalanced, rawRowCheck18527]

theorem rawRowCheck18528 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow18528 := by decide +kernel

theorem rowCheck18528 : row18528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18528 := by decide +kernel

theorem rowEval18528 (x : Key → ℝ) : Integer.Sparse.eval row18528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18528, Integer.Sparse.eval_collectBalanced, rawRowCheck18528]

theorem rawRowCheck18529 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow18529 := by decide +kernel

theorem rowCheck18529 : row18529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18529 := by decide +kernel

theorem rowEval18529 (x : Key → ℝ) : Integer.Sparse.eval row18529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18529, Integer.Sparse.eval_collectBalanced, rawRowCheck18529]

theorem rawRowCheck18530 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow18530 := by decide +kernel

theorem rowCheck18530 : row18530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18530 := by decide +kernel

theorem rowEval18530 (x : Key → ℝ) : Integer.Sparse.eval row18530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18530, Integer.Sparse.eval_collectBalanced, rawRowCheck18530]

theorem rawRowCheck18531 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18531 := by decide +kernel

theorem rowCheck18531 : row18531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18531 := by decide +kernel

theorem rowEval18531 (x : Key → ℝ) : Integer.Sparse.eval row18531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18531, Integer.Sparse.eval_collectBalanced, rawRowCheck18531]

theorem rawRowCheck18532 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18532 := by decide +kernel

theorem rowCheck18532 : row18532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18532 := by decide +kernel

theorem rowEval18532 (x : Key → ℝ) : Integer.Sparse.eval row18532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18532, Integer.Sparse.eval_collectBalanced, rawRowCheck18532]

theorem rawRowCheck18533 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18533 := by decide +kernel

theorem rowCheck18533 : row18533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18533 := by decide +kernel

theorem rowEval18533 (x : Key → ℝ) : Integer.Sparse.eval row18533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18533, Integer.Sparse.eval_collectBalanced, rawRowCheck18533]

theorem rawRowCheck18534 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1 = rawRow18534 := by decide +kernel

theorem rowCheck18534 : row18534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18534 := by decide +kernel

theorem rowEval18534 (x : Key → ℝ) : Integer.Sparse.eval row18534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18534, Integer.Sparse.eval_collectBalanced, rawRowCheck18534]

theorem rawRowCheck18535 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1 = rawRow18535 := by decide +kernel

theorem rowCheck18535 : row18535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18535 := by decide +kernel

theorem rowEval18535 (x : Key → ℝ) : Integer.Sparse.eval row18535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18535, Integer.Sparse.eval_collectBalanced, rawRowCheck18535]

theorem rawRowCheck18536 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1 = rawRow18536 := by decide +kernel

theorem rowCheck18536 : row18536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18536 := by decide +kernel

theorem rowEval18536 (x : Key → ℝ) : Integer.Sparse.eval row18536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18536, Integer.Sparse.eval_collectBalanced, rawRowCheck18536]

theorem rawRowCheck18537 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1 = rawRow18537 := by decide +kernel

theorem rowCheck18537 : row18537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18537 := by decide +kernel

theorem rowEval18537 (x : Key → ℝ) : Integer.Sparse.eval row18537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18537, Integer.Sparse.eval_collectBalanced, rawRowCheck18537]

theorem rawRowCheck18538 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1 = rawRow18538 := by decide +kernel

theorem rowCheck18538 : row18538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18538 := by decide +kernel

theorem rowEval18538 (x : Key → ℝ) : Integer.Sparse.eval row18538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18538, Integer.Sparse.eval_collectBalanced, rawRowCheck18538]

theorem rawRowCheck18539 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1 = rawRow18539 := by decide +kernel

theorem rowCheck18539 : row18539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18539 := by decide +kernel

theorem rowEval18539 (x : Key → ℝ) : Integer.Sparse.eval row18539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18539, Integer.Sparse.eval_collectBalanced, rawRowCheck18539]

theorem rawRowCheck18540 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1 = rawRow18540 := by decide +kernel

theorem rowCheck18540 : row18540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18540 := by decide +kernel

theorem rowEval18540 (x : Key → ℝ) : Integer.Sparse.eval row18540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18540, Integer.Sparse.eval_collectBalanced, rawRowCheck18540]

theorem rawRowCheck18541 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1 = rawRow18541 := by decide +kernel

theorem rowCheck18541 : row18541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18541 := by decide +kernel

theorem rowEval18541 (x : Key → ℝ) : Integer.Sparse.eval row18541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18541, Integer.Sparse.eval_collectBalanced, rawRowCheck18541]

theorem rawRowCheck18542 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1 = rawRow18542 := by decide +kernel

theorem rowCheck18542 : row18542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18542 := by decide +kernel

theorem rowEval18542 (x : Key → ℝ) : Integer.Sparse.eval row18542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18542, Integer.Sparse.eval_collectBalanced, rawRowCheck18542]

theorem rawRowCheck18543 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1 = rawRow18543 := by decide +kernel

theorem rowCheck18543 : row18543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18543 := by decide +kernel

theorem rowEval18543 (x : Key → ℝ) : Integer.Sparse.eval row18543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18543, Integer.Sparse.eval_collectBalanced, rawRowCheck18543]

theorem rawRowCheck18544 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1 = rawRow18544 := by decide +kernel

theorem rowCheck18544 : row18544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18544 := by decide +kernel

theorem rowEval18544 (x : Key → ℝ) : Integer.Sparse.eval row18544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18544, Integer.Sparse.eval_collectBalanced, rawRowCheck18544]

theorem rawRowCheck18545 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1 = rawRow18545 := by decide +kernel

theorem rowCheck18545 : row18545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18545 := by decide +kernel

theorem rowEval18545 (x : Key → ℝ) : Integer.Sparse.eval row18545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18545, Integer.Sparse.eval_collectBalanced, rawRowCheck18545]

theorem rawRowCheck18546 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1 = rawRow18546 := by decide +kernel

theorem rowCheck18546 : row18546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18546 := by decide +kernel

theorem rowEval18546 (x : Key → ℝ) : Integer.Sparse.eval row18546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18546, Integer.Sparse.eval_collectBalanced, rawRowCheck18546]

theorem rawRowCheck18547 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1 = rawRow18547 := by decide +kernel

theorem rowCheck18547 : row18547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18547 := by decide +kernel

theorem rowEval18547 (x : Key → ℝ) : Integer.Sparse.eval row18547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18547, Integer.Sparse.eval_collectBalanced, rawRowCheck18547]

theorem rawRowCheck18548 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1 = rawRow18548 := by decide +kernel

theorem rowCheck18548 : row18548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18548 := by decide +kernel

theorem rowEval18548 (x : Key → ℝ) : Integer.Sparse.eval row18548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18548, Integer.Sparse.eval_collectBalanced, rawRowCheck18548]

theorem rawRowCheck18549 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1 = rawRow18549 := by decide +kernel

theorem rowCheck18549 : row18549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18549 := by decide +kernel

theorem rowEval18549 (x : Key → ℝ) : Integer.Sparse.eval row18549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18549, Integer.Sparse.eval_collectBalanced, rawRowCheck18549]

theorem rawRowCheck18550 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1 = rawRow18550 := by decide +kernel

theorem rowCheck18550 : row18550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18550 := by decide +kernel

theorem rowEval18550 (x : Key → ℝ) : Integer.Sparse.eval row18550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18550, Integer.Sparse.eval_collectBalanced, rawRowCheck18550]

theorem rawRowCheck18551 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1 = rawRow18551 := by decide +kernel

theorem rowCheck18551 : row18551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18551 := by decide +kernel

theorem rowEval18551 (x : Key → ℝ) : Integer.Sparse.eval row18551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18551, Integer.Sparse.eval_collectBalanced, rawRowCheck18551]

theorem rawRowCheck18552 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1 = rawRow18552 := by decide +kernel

theorem rowCheck18552 : row18552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18552 := by decide +kernel

theorem rowEval18552 (x : Key → ℝ) : Integer.Sparse.eval row18552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18552, Integer.Sparse.eval_collectBalanced, rawRowCheck18552]

theorem rawRowCheck18553 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1 = rawRow18553 := by decide +kernel

theorem rowCheck18553 : row18553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18553 := by decide +kernel

theorem rowEval18553 (x : Key → ℝ) : Integer.Sparse.eval row18553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18553, Integer.Sparse.eval_collectBalanced, rawRowCheck18553]

theorem rawRowCheck18554 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1 = rawRow18554 := by decide +kernel

theorem rowCheck18554 : row18554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18554 := by decide +kernel

theorem rowEval18554 (x : Key → ℝ) : Integer.Sparse.eval row18554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18554, Integer.Sparse.eval_collectBalanced, rawRowCheck18554]

theorem rawRowCheck18555 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1 = rawRow18555 := by decide +kernel

theorem rowCheck18555 : row18555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18555 := by decide +kernel

theorem rowEval18555 (x : Key → ℝ) : Integer.Sparse.eval row18555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18555, Integer.Sparse.eval_collectBalanced, rawRowCheck18555]

theorem rawRowCheck18556 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1 = rawRow18556 := by decide +kernel

theorem rowCheck18556 : row18556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18556 := by decide +kernel

theorem rowEval18556 (x : Key → ℝ) : Integer.Sparse.eval row18556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18556, Integer.Sparse.eval_collectBalanced, rawRowCheck18556]

theorem rawRowCheck18557 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1 = rawRow18557 := by decide +kernel

theorem rowCheck18557 : row18557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18557 := by decide +kernel

theorem rowEval18557 (x : Key → ℝ) : Integer.Sparse.eval row18557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18557, Integer.Sparse.eval_collectBalanced, rawRowCheck18557]

theorem rawRowCheck18558 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1 = rawRow18558 := by decide +kernel

theorem rowCheck18558 : row18558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18558 := by decide +kernel

theorem rowEval18558 (x : Key → ℝ) : Integer.Sparse.eval row18558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18558, Integer.Sparse.eval_collectBalanced, rawRowCheck18558]

theorem rawRowCheck18559 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1 = rawRow18559 := by decide +kernel

theorem rowCheck18559 : row18559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18559 := by decide +kernel

theorem rowEval18559 (x : Key → ℝ) : Integer.Sparse.eval row18559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18559, Integer.Sparse.eval_collectBalanced, rawRowCheck18559]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block5.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form1.terms k).tag (GramFunctions.Block5.form1.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18449 x
  · exact rowEval18450 x
  · exact rowEval18451 x
  · exact rowEval18452 x
  · exact rowEval18453 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block5.form1.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form1 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block5.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form1.terms k).tag (GramFunctions.Block5.form1.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18454 x
  · exact rowEval18455 x
  · exact rowEval18456 x
  · exact rowEval18457 x
  · exact rowEval18458 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block5.form1.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form1 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block5

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

theorem rawRowCheck19664 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19664 := by decide +kernel

theorem rowCheck19664 : row19664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19664 := by decide +kernel

theorem rowEval19664 (x : Key → ℝ) : Integer.Sparse.eval row19664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19664, Integer.Sparse.eval_collectBalanced, rawRowCheck19664]

theorem rawRowCheck19665 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19665 := by decide +kernel

theorem rowCheck19665 : row19665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19665 := by decide +kernel

theorem rowEval19665 (x : Key → ℝ) : Integer.Sparse.eval row19665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19665, Integer.Sparse.eval_collectBalanced, rawRowCheck19665]

theorem rawRowCheck19666 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19666 := by decide +kernel

theorem rowCheck19666 : row19666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19666 := by decide +kernel

theorem rowEval19666 (x : Key → ℝ) : Integer.Sparse.eval row19666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19666, Integer.Sparse.eval_collectBalanced, rawRowCheck19666]

theorem rawRowCheck19667 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1 = rawRow19667 := by decide +kernel

theorem rowCheck19667 : row19667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19667 := by decide +kernel

theorem rowEval19667 (x : Key → ℝ) : Integer.Sparse.eval row19667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19667, Integer.Sparse.eval_collectBalanced, rawRowCheck19667]

theorem rawRowCheck19668 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1 = rawRow19668 := by decide +kernel

theorem rowCheck19668 : row19668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19668 := by decide +kernel

theorem rowEval19668 (x : Key → ℝ) : Integer.Sparse.eval row19668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19668, Integer.Sparse.eval_collectBalanced, rawRowCheck19668]

theorem rawRowCheck19669 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1 = rawRow19669 := by decide +kernel

theorem rowCheck19669 : row19669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19669 := by decide +kernel

theorem rowEval19669 (x : Key → ℝ) : Integer.Sparse.eval row19669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19669, Integer.Sparse.eval_collectBalanced, rawRowCheck19669]

theorem rawRowCheck19670 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1 = rawRow19670 := by decide +kernel

theorem rowCheck19670 : row19670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19670 := by decide +kernel

theorem rowEval19670 (x : Key → ℝ) : Integer.Sparse.eval row19670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19670, Integer.Sparse.eval_collectBalanced, rawRowCheck19670]

theorem rawRowCheck19671 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1 = rawRow19671 := by decide +kernel

theorem rowCheck19671 : row19671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19671 := by decide +kernel

theorem rowEval19671 (x : Key → ℝ) : Integer.Sparse.eval row19671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19671, Integer.Sparse.eval_collectBalanced, rawRowCheck19671]

theorem rawRowCheck19672 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1 = rawRow19672 := by decide +kernel

theorem rowCheck19672 : row19672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19672 := by decide +kernel

theorem rowEval19672 (x : Key → ℝ) : Integer.Sparse.eval row19672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19672, Integer.Sparse.eval_collectBalanced, rawRowCheck19672]

theorem rawRowCheck19673 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19673 := by decide +kernel

theorem rowCheck19673 : row19673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19673 := by decide +kernel

theorem rowEval19673 (x : Key → ℝ) : Integer.Sparse.eval row19673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19673, Integer.Sparse.eval_collectBalanced, rawRowCheck19673]

theorem rawRowCheck19674 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19674 := by decide +kernel

theorem rowCheck19674 : row19674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19674 := by decide +kernel

theorem rowEval19674 (x : Key → ℝ) : Integer.Sparse.eval row19674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19674, Integer.Sparse.eval_collectBalanced, rawRowCheck19674]

theorem rawRowCheck19675 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19675 := by decide +kernel

theorem rowCheck19675 : row19675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19675 := by decide +kernel

theorem rowEval19675 (x : Key → ℝ) : Integer.Sparse.eval row19675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19675, Integer.Sparse.eval_collectBalanced, rawRowCheck19675]

theorem rawRowCheck19676 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19676 := by decide +kernel

theorem rowCheck19676 : row19676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19676 := by decide +kernel

theorem rowEval19676 (x : Key → ℝ) : Integer.Sparse.eval row19676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19676, Integer.Sparse.eval_collectBalanced, rawRowCheck19676]

theorem rawRowCheck19677 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19677 := by decide +kernel

theorem rowCheck19677 : row19677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19677 := by decide +kernel

theorem rowEval19677 (x : Key → ℝ) : Integer.Sparse.eval row19677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19677, Integer.Sparse.eval_collectBalanced, rawRowCheck19677]

theorem rawRowCheck19678 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19678 := by decide +kernel

theorem rowCheck19678 : row19678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19678 := by decide +kernel

theorem rowEval19678 (x : Key → ℝ) : Integer.Sparse.eval row19678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19678, Integer.Sparse.eval_collectBalanced, rawRowCheck19678]

theorem rawRowCheck19679 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1 = rawRow19679 := by decide +kernel

theorem rowCheck19679 : row19679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19679 := by decide +kernel

theorem rowEval19679 (x : Key → ℝ) : Integer.Sparse.eval row19679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19679, Integer.Sparse.eval_collectBalanced, rawRowCheck19679]

theorem rawRowCheck19680 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1 = rawRow19680 := by decide +kernel

theorem rowCheck19680 : row19680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19680 := by decide +kernel

theorem rowEval19680 (x : Key → ℝ) : Integer.Sparse.eval row19680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19680, Integer.Sparse.eval_collectBalanced, rawRowCheck19680]

theorem rawRowCheck19681 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1 = rawRow19681 := by decide +kernel

theorem rowCheck19681 : row19681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19681 := by decide +kernel

theorem rowEval19681 (x : Key → ℝ) : Integer.Sparse.eval row19681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19681, Integer.Sparse.eval_collectBalanced, rawRowCheck19681]

theorem rawRowCheck19682 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1 = rawRow19682 := by decide +kernel

theorem rowCheck19682 : row19682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19682 := by decide +kernel

theorem rowEval19682 (x : Key → ℝ) : Integer.Sparse.eval row19682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19682, Integer.Sparse.eval_collectBalanced, rawRowCheck19682]

theorem rawRowCheck19683 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1 = rawRow19683 := by decide +kernel

theorem rowCheck19683 : row19683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19683 := by decide +kernel

theorem rowEval19683 (x : Key → ℝ) : Integer.Sparse.eval row19683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19683, Integer.Sparse.eval_collectBalanced, rawRowCheck19683]

theorem rawRowCheck19684 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1 = rawRow19684 := by decide +kernel

theorem rowCheck19684 : row19684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19684 := by decide +kernel

theorem rowEval19684 (x : Key → ℝ) : Integer.Sparse.eval row19684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19684, Integer.Sparse.eval_collectBalanced, rawRowCheck19684]

theorem rawRowCheck19685 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19685 := by decide +kernel

theorem rowCheck19685 : row19685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19685 := by decide +kernel

theorem rowEval19685 (x : Key → ℝ) : Integer.Sparse.eval row19685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19685, Integer.Sparse.eval_collectBalanced, rawRowCheck19685]

theorem rawRowCheck19686 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19686 := by decide +kernel

theorem rowCheck19686 : row19686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19686 := by decide +kernel

theorem rowEval19686 (x : Key → ℝ) : Integer.Sparse.eval row19686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19686, Integer.Sparse.eval_collectBalanced, rawRowCheck19686]

theorem rawRowCheck19687 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19687 := by decide +kernel

theorem rowCheck19687 : row19687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19687 := by decide +kernel

theorem rowEval19687 (x : Key → ℝ) : Integer.Sparse.eval row19687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19687, Integer.Sparse.eval_collectBalanced, rawRowCheck19687]

theorem rawRowCheck19688 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1 = rawRow19688 := by decide +kernel

theorem rowCheck19688 : row19688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19688 := by decide +kernel

theorem rowEval19688 (x : Key → ℝ) : Integer.Sparse.eval row19688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19688, Integer.Sparse.eval_collectBalanced, rawRowCheck19688]

theorem rawRowCheck19689 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1 = rawRow19689 := by decide +kernel

theorem rowCheck19689 : row19689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19689 := by decide +kernel

theorem rowEval19689 (x : Key → ℝ) : Integer.Sparse.eval row19689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19689, Integer.Sparse.eval_collectBalanced, rawRowCheck19689]

theorem rawRowCheck19690 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1 = rawRow19690 := by decide +kernel

theorem rowCheck19690 : row19690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19690 := by decide +kernel

theorem rowEval19690 (x : Key → ℝ) : Integer.Sparse.eval row19690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19690, Integer.Sparse.eval_collectBalanced, rawRowCheck19690]

theorem rawRowCheck19691 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1 = rawRow19691 := by decide +kernel

theorem rowCheck19691 : row19691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19691 := by decide +kernel

theorem rowEval19691 (x : Key → ℝ) : Integer.Sparse.eval row19691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19691, Integer.Sparse.eval_collectBalanced, rawRowCheck19691]

theorem rawRowCheck19692 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1 = rawRow19692 := by decide +kernel

theorem rowCheck19692 : row19692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19692 := by decide +kernel

theorem rowEval19692 (x : Key → ℝ) : Integer.Sparse.eval row19692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19692, Integer.Sparse.eval_collectBalanced, rawRowCheck19692]

theorem rawRowCheck19693 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1 = rawRow19693 := by decide +kernel

theorem rowCheck19693 : row19693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19693 := by decide +kernel

theorem rowEval19693 (x : Key → ℝ) : Integer.Sparse.eval row19693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19693, Integer.Sparse.eval_collectBalanced, rawRowCheck19693]

theorem rawRowCheck19694 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1 = rawRow19694 := by decide +kernel

theorem rowCheck19694 : row19694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19694 := by decide +kernel

theorem rowEval19694 (x : Key → ℝ) : Integer.Sparse.eval row19694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19694, Integer.Sparse.eval_collectBalanced, rawRowCheck19694]

theorem rawRowCheck19695 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1 = rawRow19695 := by decide +kernel

theorem rowCheck19695 : row19695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19695 := by decide +kernel

theorem rowEval19695 (x : Key → ℝ) : Integer.Sparse.eval row19695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19695, Integer.Sparse.eval_collectBalanced, rawRowCheck19695]

theorem rawRowCheck19696 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1 = rawRow19696 := by decide +kernel

theorem rowCheck19696 : row19696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19696 := by decide +kernel

theorem rowEval19696 (x : Key → ℝ) : Integer.Sparse.eval row19696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19696, Integer.Sparse.eval_collectBalanced, rawRowCheck19696]

theorem rawRowCheck19697 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1 = rawRow19697 := by decide +kernel

theorem rowCheck19697 : row19697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19697 := by decide +kernel

theorem rowEval19697 (x : Key → ℝ) : Integer.Sparse.eval row19697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19697, Integer.Sparse.eval_collectBalanced, rawRowCheck19697]

theorem rawRowCheck19698 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1 = rawRow19698 := by decide +kernel

theorem rowCheck19698 : row19698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19698 := by decide +kernel

theorem rowEval19698 (x : Key → ℝ) : Integer.Sparse.eval row19698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19698, Integer.Sparse.eval_collectBalanced, rawRowCheck19698]

theorem rawRowCheck19699 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1 = rawRow19699 := by decide +kernel

theorem rowCheck19699 : row19699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19699 := by decide +kernel

theorem rowEval19699 (x : Key → ℝ) : Integer.Sparse.eval row19699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19699, Integer.Sparse.eval_collectBalanced, rawRowCheck19699]

theorem rawRowCheck19700 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1 = rawRow19700 := by decide +kernel

theorem rowCheck19700 : row19700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19700 := by decide +kernel

theorem rowEval19700 (x : Key → ℝ) : Integer.Sparse.eval row19700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19700, Integer.Sparse.eval_collectBalanced, rawRowCheck19700]

theorem rawRowCheck19701 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1 = rawRow19701 := by decide +kernel

theorem rowCheck19701 : row19701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19701 := by decide +kernel

theorem rowEval19701 (x : Key → ℝ) : Integer.Sparse.eval row19701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19701, Integer.Sparse.eval_collectBalanced, rawRowCheck19701]

theorem rawRowCheck19702 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1 = rawRow19702 := by decide +kernel

theorem rowCheck19702 : row19702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19702 := by decide +kernel

theorem rowEval19702 (x : Key → ℝ) : Integer.Sparse.eval row19702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19702, Integer.Sparse.eval_collectBalanced, rawRowCheck19702]

theorem rawRowCheck19703 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1 = rawRow19703 := by decide +kernel

theorem rowCheck19703 : row19703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19703 := by decide +kernel

theorem rowEval19703 (x : Key → ℝ) : Integer.Sparse.eval row19703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19703, Integer.Sparse.eval_collectBalanced, rawRowCheck19703]

theorem rawRowCheck19704 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1 = rawRow19704 := by decide +kernel

theorem rowCheck19704 : row19704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19704 := by decide +kernel

theorem rowEval19704 (x : Key → ℝ) : Integer.Sparse.eval row19704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19704, Integer.Sparse.eval_collectBalanced, rawRowCheck19704]

theorem rawRowCheck19705 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1 = rawRow19705 := by decide +kernel

theorem rowCheck19705 : row19705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19705 := by decide +kernel

theorem rowEval19705 (x : Key → ℝ) : Integer.Sparse.eval row19705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19705, Integer.Sparse.eval_collectBalanced, rawRowCheck19705]

theorem rawRowCheck19706 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1 = rawRow19706 := by decide +kernel

theorem rowCheck19706 : row19706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19706 := by decide +kernel

theorem rowEval19706 (x : Key → ℝ) : Integer.Sparse.eval row19706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19706, Integer.Sparse.eval_collectBalanced, rawRowCheck19706]

theorem rawRowCheck19707 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1 = rawRow19707 := by decide +kernel

theorem rowCheck19707 : row19707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19707 := by decide +kernel

theorem rowEval19707 (x : Key → ℝ) : Integer.Sparse.eval row19707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19707, Integer.Sparse.eval_collectBalanced, rawRowCheck19707]

theorem rawRowCheck19708 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1 = rawRow19708 := by decide +kernel

theorem rowCheck19708 : row19708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19708 := by decide +kernel

theorem rowEval19708 (x : Key → ℝ) : Integer.Sparse.eval row19708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19708, Integer.Sparse.eval_collectBalanced, rawRowCheck19708]

theorem rawRowCheck19709 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1 = rawRow19709 := by decide +kernel

theorem rowCheck19709 : row19709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19709 := by decide +kernel

theorem rowEval19709 (x : Key → ℝ) : Integer.Sparse.eval row19709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19709, Integer.Sparse.eval_collectBalanced, rawRowCheck19709]

theorem rawRowCheck19710 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1 = rawRow19710 := by decide +kernel

theorem rowCheck19710 : row19710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19710 := by decide +kernel

theorem rowEval19710 (x : Key → ℝ) : Integer.Sparse.eval row19710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19710, Integer.Sparse.eval_collectBalanced, rawRowCheck19710]

theorem rawRowCheck19711 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1 = rawRow19711 := by decide +kernel

theorem rowCheck19711 : row19711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19711 := by decide +kernel

theorem rowEval19711 (x : Key → ℝ) : Integer.Sparse.eval row19711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19711, Integer.Sparse.eval_collectBalanced, rawRowCheck19711]

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

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19712 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19712 := by decide +kernel

theorem rowCheck19712 : row19712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19712 := by decide +kernel

theorem rowEval19712 (x : Key → ℝ) : Integer.Sparse.eval row19712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19712, Integer.Sparse.eval_collectBalanced, rawRowCheck19712]

theorem rawRowCheck19713 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19713 := by decide +kernel

theorem rowCheck19713 : row19713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19713 := by decide +kernel

theorem rowEval19713 (x : Key → ℝ) : Integer.Sparse.eval row19713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19713, Integer.Sparse.eval_collectBalanced, rawRowCheck19713]

theorem rawRowCheck19714 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19714 := by decide +kernel

theorem rowCheck19714 : row19714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19714 := by decide +kernel

theorem rowEval19714 (x : Key → ℝ) : Integer.Sparse.eval row19714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19714, Integer.Sparse.eval_collectBalanced, rawRowCheck19714]

theorem rawRowCheck19715 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19715 := by decide +kernel

theorem rowCheck19715 : row19715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19715 := by decide +kernel

theorem rowEval19715 (x : Key → ℝ) : Integer.Sparse.eval row19715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19715, Integer.Sparse.eval_collectBalanced, rawRowCheck19715]

theorem rawRowCheck19716 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19716 := by decide +kernel

theorem rowCheck19716 : row19716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19716 := by decide +kernel

theorem rowEval19716 (x : Key → ℝ) : Integer.Sparse.eval row19716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19716, Integer.Sparse.eval_collectBalanced, rawRowCheck19716]

theorem rawRowCheck19717 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19717 := by decide +kernel

theorem rowCheck19717 : row19717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19717 := by decide +kernel

theorem rowEval19717 (x : Key → ℝ) : Integer.Sparse.eval row19717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19717, Integer.Sparse.eval_collectBalanced, rawRowCheck19717]

theorem rawRowCheck19718 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1 = rawRow19718 := by decide +kernel

theorem rowCheck19718 : row19718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19718 := by decide +kernel

theorem rowEval19718 (x : Key → ℝ) : Integer.Sparse.eval row19718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19718, Integer.Sparse.eval_collectBalanced, rawRowCheck19718]

theorem rawRowCheck19719 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1 = rawRow19719 := by decide +kernel

theorem rowCheck19719 : row19719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19719 := by decide +kernel

theorem rowEval19719 (x : Key → ℝ) : Integer.Sparse.eval row19719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19719, Integer.Sparse.eval_collectBalanced, rawRowCheck19719]

theorem rawRowCheck19720 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1 = rawRow19720 := by decide +kernel

theorem rowCheck19720 : row19720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19720 := by decide +kernel

theorem rowEval19720 (x : Key → ℝ) : Integer.Sparse.eval row19720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19720, Integer.Sparse.eval_collectBalanced, rawRowCheck19720]

theorem rawRowCheck19721 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1 = rawRow19721 := by decide +kernel

theorem rowCheck19721 : row19721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19721 := by decide +kernel

theorem rowEval19721 (x : Key → ℝ) : Integer.Sparse.eval row19721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19721, Integer.Sparse.eval_collectBalanced, rawRowCheck19721]

theorem rawRowCheck19722 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1 = rawRow19722 := by decide +kernel

theorem rowCheck19722 : row19722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19722 := by decide +kernel

theorem rowEval19722 (x : Key → ℝ) : Integer.Sparse.eval row19722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19722, Integer.Sparse.eval_collectBalanced, rawRowCheck19722]

theorem rawRowCheck19723 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1 = rawRow19723 := by decide +kernel

theorem rowCheck19723 : row19723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19723 := by decide +kernel

theorem rowEval19723 (x : Key → ℝ) : Integer.Sparse.eval row19723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19723, Integer.Sparse.eval_collectBalanced, rawRowCheck19723]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19664 x
  · exact rowEval19665 x
  · exact rowEval19666 x
  · exact rowEval19667 x
  · exact rowEval19668 x
  · exact rowEval19669 x
  · exact rowEval19670 x
  · exact rowEval19671 x
  · exact rowEval19672 x
  · exact rowEval19673 x
  · exact rowEval19674 x
  · exact rowEval19675 x
  · exact rowEval19676 x
  · exact rowEval19677 x
  · exact rowEval19678 x
  · exact rowEval19679 x
  · exact rowEval19680 x
  · exact rowEval19681 x
  · exact rowEval19682 x
  · exact rowEval19683 x
  · exact rowEval19684 x
  · exact rowEval19685 x
  · exact rowEval19686 x
  · exact rowEval19687 x
  · exact rowEval19688 x
  · exact rowEval19689 x
  · exact rowEval19690 x
  · exact rowEval19691 x
  · exact rowEval19692 x
  · exact rowEval19693 x
  · exact rowEval19694 x
  · exact rowEval19695 x
  · exact rowEval19696 x
  · exact rowEval19697 x
  · exact rowEval19698 x
  · exact rowEval19699 x
  · exact rowEval19700 x
  · exact rowEval19701 x
  · exact rowEval19702 x
  · exact rowEval19703 x
  · exact rowEval19704 x
  · exact rowEval19705 x
  · exact rowEval19706 x
  · exact rowEval19707 x
  · exact rowEval19708 x
  · exact rowEval19709 x
  · exact rowEval19710 x
  · exact rowEval19711 x
  · exact rowEval19712 x
  · exact rowEval19713 x
  · exact rowEval19714 x
  · exact rowEval19715 x
  · exact rowEval19716 x
  · exact rowEval19717 x
  · exact rowEval19718 x
  · exact rowEval19719 x
  · exact rowEval19720 x
  · exact rowEval19721 x
  · exact rowEval19722 x
  · exact rowEval19723 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18560 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1 = rawRow18560 := by decide +kernel

theorem rowCheck18560 : row18560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18560 := by decide +kernel

theorem rowEval18560 (x : Key → ℝ) : Integer.Sparse.eval row18560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18560, Integer.Sparse.eval_collectBalanced, rawRowCheck18560]

theorem rawRowCheck18561 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1 = rawRow18561 := by decide +kernel

theorem rowCheck18561 : row18561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18561 := by decide +kernel

theorem rowEval18561 (x : Key → ℝ) : Integer.Sparse.eval row18561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18561, Integer.Sparse.eval_collectBalanced, rawRowCheck18561]

theorem rawRowCheck18562 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1 = rawRow18562 := by decide +kernel

theorem rowCheck18562 : row18562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18562 := by decide +kernel

theorem rowEval18562 (x : Key → ℝ) : Integer.Sparse.eval row18562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18562, Integer.Sparse.eval_collectBalanced, rawRowCheck18562]

theorem rawRowCheck18563 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1 = rawRow18563 := by decide +kernel

theorem rowCheck18563 : row18563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18563 := by decide +kernel

theorem rowEval18563 (x : Key → ℝ) : Integer.Sparse.eval row18563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18563, Integer.Sparse.eval_collectBalanced, rawRowCheck18563]

theorem rawRowCheck18564 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1 = rawRow18564 := by decide +kernel

theorem rowCheck18564 : row18564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18564 := by decide +kernel

theorem rowEval18564 (x : Key → ℝ) : Integer.Sparse.eval row18564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18564, Integer.Sparse.eval_collectBalanced, rawRowCheck18564]

theorem rawRowCheck18565 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1 = rawRow18565 := by decide +kernel

theorem rowCheck18565 : row18565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18565 := by decide +kernel

theorem rowEval18565 (x : Key → ℝ) : Integer.Sparse.eval row18565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18565, Integer.Sparse.eval_collectBalanced, rawRowCheck18565]

theorem rawRowCheck18566 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1 = rawRow18566 := by decide +kernel

theorem rowCheck18566 : row18566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18566 := by decide +kernel

theorem rowEval18566 (x : Key → ℝ) : Integer.Sparse.eval row18566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18566, Integer.Sparse.eval_collectBalanced, rawRowCheck18566]

theorem rawRowCheck18567 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow18567 := by decide +kernel

theorem rowCheck18567 : row18567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18567 := by decide +kernel

theorem rowEval18567 (x : Key → ℝ) : Integer.Sparse.eval row18567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18567, Integer.Sparse.eval_collectBalanced, rawRowCheck18567]

theorem rawRowCheck18568 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow18568 := by decide +kernel

theorem rowCheck18568 : row18568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18568 := by decide +kernel

theorem rowEval18568 (x : Key → ℝ) : Integer.Sparse.eval row18568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18568, Integer.Sparse.eval_collectBalanced, rawRowCheck18568]

theorem rawRowCheck18569 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow18569 := by decide +kernel

theorem rowCheck18569 : row18569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18569 := by decide +kernel

theorem rowEval18569 (x : Key → ℝ) : Integer.Sparse.eval row18569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18569, Integer.Sparse.eval_collectBalanced, rawRowCheck18569]

theorem rawRowCheck18570 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1 = rawRow18570 := by decide +kernel

theorem rowCheck18570 : row18570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18570 := by decide +kernel

theorem rowEval18570 (x : Key → ℝ) : Integer.Sparse.eval row18570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18570, Integer.Sparse.eval_collectBalanced, rawRowCheck18570]

theorem rawRowCheck18571 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1 = rawRow18571 := by decide +kernel

theorem rowCheck18571 : row18571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18571 := by decide +kernel

theorem rowEval18571 (x : Key → ℝ) : Integer.Sparse.eval row18571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18571, Integer.Sparse.eval_collectBalanced, rawRowCheck18571]

theorem rawRowCheck18572 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1 = rawRow18572 := by decide +kernel

theorem rowCheck18572 : row18572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18572 := by decide +kernel

theorem rowEval18572 (x : Key → ℝ) : Integer.Sparse.eval row18572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18572, Integer.Sparse.eval_collectBalanced, rawRowCheck18572]

theorem rawRowCheck18573 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1 = rawRow18573 := by decide +kernel

theorem rowCheck18573 : row18573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18573 := by decide +kernel

theorem rowEval18573 (x : Key → ℝ) : Integer.Sparse.eval row18573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18573, Integer.Sparse.eval_collectBalanced, rawRowCheck18573]

theorem rawRowCheck18574 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1 = rawRow18574 := by decide +kernel

theorem rowCheck18574 : row18574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18574 := by decide +kernel

theorem rowEval18574 (x : Key → ℝ) : Integer.Sparse.eval row18574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18574, Integer.Sparse.eval_collectBalanced, rawRowCheck18574]

theorem rawRowCheck18575 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1 = rawRow18575 := by decide +kernel

theorem rowCheck18575 : row18575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18575 := by decide +kernel

theorem rowEval18575 (x : Key → ℝ) : Integer.Sparse.eval row18575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18575, Integer.Sparse.eval_collectBalanced, rawRowCheck18575]

theorem rawRowCheck18576 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1 = rawRow18576 := by decide +kernel

theorem rowCheck18576 : row18576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18576 := by decide +kernel

theorem rowEval18576 (x : Key → ℝ) : Integer.Sparse.eval row18576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18576, Integer.Sparse.eval_collectBalanced, rawRowCheck18576]

theorem rawRowCheck18577 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1 = rawRow18577 := by decide +kernel

theorem rowCheck18577 : row18577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18577 := by decide +kernel

theorem rowEval18577 (x : Key → ℝ) : Integer.Sparse.eval row18577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18577, Integer.Sparse.eval_collectBalanced, rawRowCheck18577]

theorem rawRowCheck18578 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1 = rawRow18578 := by decide +kernel

theorem rowCheck18578 : row18578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18578 := by decide +kernel

theorem rowEval18578 (x : Key → ℝ) : Integer.Sparse.eval row18578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18578, Integer.Sparse.eval_collectBalanced, rawRowCheck18578]

theorem rawRowCheck18644 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18644 := by decide +kernel

theorem rowCheck18644 : row18644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18644 := by decide +kernel

theorem rowEval18644 (x : Key → ℝ) : Integer.Sparse.eval row18644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18644, Integer.Sparse.eval_collectBalanced, rawRowCheck18644]

theorem rawRowCheck18645 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18645 := by decide +kernel

theorem rowCheck18645 : row18645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18645 := by decide +kernel

theorem rowEval18645 (x : Key → ℝ) : Integer.Sparse.eval row18645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18645, Integer.Sparse.eval_collectBalanced, rawRowCheck18645]

theorem rawRowCheck18646 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18646 := by decide +kernel

theorem rowCheck18646 : row18646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18646 := by decide +kernel

theorem rowEval18646 (x : Key → ℝ) : Integer.Sparse.eval row18646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18646, Integer.Sparse.eval_collectBalanced, rawRowCheck18646]

theorem rawRowCheck18647 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18647 := by decide +kernel

theorem rowCheck18647 : row18647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18647 := by decide +kernel

theorem rowEval18647 (x : Key → ℝ) : Integer.Sparse.eval row18647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18647, Integer.Sparse.eval_collectBalanced, rawRowCheck18647]

theorem rawRowCheck18648 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18648 := by decide +kernel

theorem rowCheck18648 : row18648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18648 := by decide +kernel

theorem rowEval18648 (x : Key → ℝ) : Integer.Sparse.eval row18648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18648, Integer.Sparse.eval_collectBalanced, rawRowCheck18648]

theorem rawRowCheck18679 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18679 := by decide +kernel

theorem rowCheck18679 : row18679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18679 := by decide +kernel

theorem rowEval18679 (x : Key → ℝ) : Integer.Sparse.eval row18679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18679, Integer.Sparse.eval_collectBalanced, rawRowCheck18679]

theorem rawRowCheck18680 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18680 := by decide +kernel

theorem rowCheck18680 : row18680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18680 := by decide +kernel

theorem rowEval18680 (x : Key → ℝ) : Integer.Sparse.eval row18680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18680, Integer.Sparse.eval_collectBalanced, rawRowCheck18680]

theorem rawRowCheck18681 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18681 := by decide +kernel

theorem rowCheck18681 : row18681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18681 := by decide +kernel

theorem rowEval18681 (x : Key → ℝ) : Integer.Sparse.eval row18681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18681, Integer.Sparse.eval_collectBalanced, rawRowCheck18681]

theorem rawRowCheck18682 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18682 := by decide +kernel

theorem rowCheck18682 : row18682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18682 := by decide +kernel

theorem rowEval18682 (x : Key → ℝ) : Integer.Sparse.eval row18682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18682, Integer.Sparse.eval_collectBalanced, rawRowCheck18682]

theorem rawRowCheck18683 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18683 := by decide +kernel

theorem rowCheck18683 : row18683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18683 := by decide +kernel

theorem rowEval18683 (x : Key → ℝ) : Integer.Sparse.eval row18683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18683, Integer.Sparse.eval_collectBalanced, rawRowCheck18683]

theorem rawRowCheck18684 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18684 := by decide +kernel

theorem rowCheck18684 : row18684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18684 := by decide +kernel

theorem rowEval18684 (x : Key → ℝ) : Integer.Sparse.eval row18684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18684, Integer.Sparse.eval_collectBalanced, rawRowCheck18684]

theorem rawRowCheck18685 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18685 := by decide +kernel

theorem rowCheck18685 : row18685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18685 := by decide +kernel

theorem rowEval18685 (x : Key → ℝ) : Integer.Sparse.eval row18685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18685, Integer.Sparse.eval_collectBalanced, rawRowCheck18685]

theorem rawRowCheck18686 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form1 = rawRow18686 := by decide +kernel

theorem rowCheck18686 : row18686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18686 := by decide +kernel

theorem rowEval18686 (x : Key → ℝ) : Integer.Sparse.eval row18686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18686, Integer.Sparse.eval_collectBalanced, rawRowCheck18686]

theorem rawRowCheck18687 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form1 = rawRow18687 := by decide +kernel

theorem rowCheck18687 : row18687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18687 := by decide +kernel

theorem rowEval18687 (x : Key → ℝ) : Integer.Sparse.eval row18687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18687, Integer.Sparse.eval_collectBalanced, rawRowCheck18687]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block5.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form2.terms k).tag (GramFunctions.Block5.form2.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18519 x
  · exact rowEval18520 x
  · exact rowEval18521 x
  · exact rowEval18522 x
  · exact rowEval18523 x
  · exact rowEval18524 x
  · exact rowEval18525 x
  · exact rowEval18526 x
  · exact rowEval18527 x
  · exact rowEval18528 x
  · exact rowEval18529 x
  · exact rowEval18530 x
  · exact rowEval18531 x
  · exact rowEval18532 x
  · exact rowEval18533 x
  · exact rowEval18534 x
  · exact rowEval18535 x
  · exact rowEval18536 x
  · exact rowEval18537 x
  · exact rowEval18538 x
  · exact rowEval18539 x
  · exact rowEval18540 x
  · exact rowEval18541 x
  · exact rowEval18542 x
  · exact rowEval18543 x
  · exact rowEval18544 x
  · exact rowEval18545 x
  · exact rowEval18546 x
  · exact rowEval18547 x
  · exact rowEval18548 x
  · exact rowEval18549 x
  · exact rowEval18550 x
  · exact rowEval18551 x
  · exact rowEval18552 x
  · exact rowEval18553 x
  · exact rowEval18554 x
  · exact rowEval18555 x
  · exact rowEval18556 x
  · exact rowEval18557 x
  · exact rowEval18558 x
  · exact rowEval18559 x
  · exact rowEval18560 x
  · exact rowEval18561 x
  · exact rowEval18562 x
  · exact rowEval18563 x
  · exact rowEval18564 x
  · exact rowEval18565 x
  · exact rowEval18566 x
  · exact rowEval18567 x
  · exact rowEval18568 x
  · exact rowEval18569 x
  · exact rowEval18570 x
  · exact rowEval18571 x
  · exact rowEval18572 x
  · exact rowEval18573 x
  · exact rowEval18574 x
  · exact rowEval18575 x
  · exact rowEval18576 x
  · exact rowEval18577 x
  · exact rowEval18578 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block5.form2.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form2 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18644 x
  · exact rowEval18645 x
  · exact rowEval18646 x
  · exact rowEval18647 x
  · exact rowEval18648 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

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

theorem rawRowCheck18688 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form1 = rawRow18688 := by decide +kernel

theorem rowCheck18688 : row18688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18688 := by decide +kernel

theorem rowEval18688 (x : Key → ℝ) : Integer.Sparse.eval row18688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18688, Integer.Sparse.eval_collectBalanced, rawRowCheck18688]

theorem rawRowCheck18689 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form1 = rawRow18689 := by decide +kernel

theorem rowCheck18689 : row18689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18689 := by decide +kernel

theorem rowEval18689 (x : Key → ℝ) : Integer.Sparse.eval row18689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18689, Integer.Sparse.eval_collectBalanced, rawRowCheck18689]

theorem rawRowCheck18690 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form1 = rawRow18690 := by decide +kernel

theorem rowCheck18690 : row18690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18690 := by decide +kernel

theorem rowEval18690 (x : Key → ℝ) : Integer.Sparse.eval row18690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18690, Integer.Sparse.eval_collectBalanced, rawRowCheck18690]

theorem rawRowCheck18691 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form1 = rawRow18691 := by decide +kernel

theorem rowCheck18691 : row18691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18691 := by decide +kernel

theorem rowEval18691 (x : Key → ℝ) : Integer.Sparse.eval row18691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18691, Integer.Sparse.eval_collectBalanced, rawRowCheck18691]

theorem rawRowCheck18692 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18692 := by decide +kernel

theorem rowCheck18692 : row18692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18692 := by decide +kernel

theorem rowEval18692 (x : Key → ℝ) : Integer.Sparse.eval row18692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18692, Integer.Sparse.eval_collectBalanced, rawRowCheck18692]

theorem rawRowCheck18693 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18693 := by decide +kernel

theorem rowCheck18693 : row18693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18693 := by decide +kernel

theorem rowEval18693 (x : Key → ℝ) : Integer.Sparse.eval row18693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18693, Integer.Sparse.eval_collectBalanced, rawRowCheck18693]

theorem rawRowCheck18694 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18694 := by decide +kernel

theorem rowCheck18694 : row18694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18694 := by decide +kernel

theorem rowEval18694 (x : Key → ℝ) : Integer.Sparse.eval row18694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18694, Integer.Sparse.eval_collectBalanced, rawRowCheck18694]

theorem rawRowCheck18695 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18695 := by decide +kernel

theorem rowCheck18695 : row18695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18695 := by decide +kernel

theorem rowEval18695 (x : Key → ℝ) : Integer.Sparse.eval row18695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18695, Integer.Sparse.eval_collectBalanced, rawRowCheck18695]

theorem rawRowCheck18696 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18696 := by decide +kernel

theorem rowCheck18696 : row18696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18696 := by decide +kernel

theorem rowEval18696 (x : Key → ℝ) : Integer.Sparse.eval row18696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18696, Integer.Sparse.eval_collectBalanced, rawRowCheck18696]

theorem rawRowCheck18697 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18697 := by decide +kernel

theorem rowCheck18697 : row18697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18697 := by decide +kernel

theorem rowEval18697 (x : Key → ℝ) : Integer.Sparse.eval row18697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18697, Integer.Sparse.eval_collectBalanced, rawRowCheck18697]

theorem rawRowCheck18698 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18698 := by decide +kernel

theorem rowCheck18698 : row18698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18698 := by decide +kernel

theorem rowEval18698 (x : Key → ℝ) : Integer.Sparse.eval row18698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18698, Integer.Sparse.eval_collectBalanced, rawRowCheck18698]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18679 x
  · exact rowEval18680 x
  · exact rowEval18681 x
  · exact rowEval18682 x
  · exact rowEval18683 x
  · exact rowEval18684 x
  · exact rowEval18685 x
  · exact rowEval18686 x
  · exact rowEval18687 x
  · exact rowEval18688 x
  · exact rowEval18689 x
  · exact rowEval18690 x
  · exact rowEval18691 x
  · exact rowEval18692 x
  · exact rowEval18693 x
  · exact rowEval18694 x
  · exact rowEval18695 x
  · exact rowEval18696 x
  · exact rowEval18697 x
  · exact rowEval18698 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

end MUB6.Certificate.GramEntries.Block5

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

theorem rawRowCheck18959 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18959 := by decide +kernel

theorem rowCheck18959 : row18959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18959 := by decide +kernel

theorem rowEval18959 (x : Key → ℝ) : Integer.Sparse.eval row18959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18959, Integer.Sparse.eval_collectBalanced, rawRowCheck18959]

theorem rawRowCheck18960 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18960 := by decide +kernel

theorem rowCheck18960 : row18960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18960 := by decide +kernel

theorem rowEval18960 (x : Key → ℝ) : Integer.Sparse.eval row18960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18960, Integer.Sparse.eval_collectBalanced, rawRowCheck18960]

theorem rawRowCheck18961 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18961 := by decide +kernel

theorem rowCheck18961 : row18961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18961 := by decide +kernel

theorem rowEval18961 (x : Key → ℝ) : Integer.Sparse.eval row18961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18961, Integer.Sparse.eval_collectBalanced, rawRowCheck18961]

theorem rawRowCheck18962 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18962 := by decide +kernel

theorem rowCheck18962 : row18962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18962 := by decide +kernel

theorem rowEval18962 (x : Key → ℝ) : Integer.Sparse.eval row18962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18962, Integer.Sparse.eval_collectBalanced, rawRowCheck18962]

theorem rawRowCheck18963 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18963 := by decide +kernel

theorem rowCheck18963 : row18963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18963 := by decide +kernel

theorem rowEval18963 (x : Key → ℝ) : Integer.Sparse.eval row18963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18963, Integer.Sparse.eval_collectBalanced, rawRowCheck18963]

theorem rawRowCheck18964 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18964 := by decide +kernel

theorem rowCheck18964 : row18964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18964 := by decide +kernel

theorem rowEval18964 (x : Key → ℝ) : Integer.Sparse.eval row18964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18964, Integer.Sparse.eval_collectBalanced, rawRowCheck18964]

theorem rawRowCheck18965 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18965 := by decide +kernel

theorem rowCheck18965 : row18965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18965 := by decide +kernel

theorem rowEval18965 (x : Key → ℝ) : Integer.Sparse.eval row18965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18965, Integer.Sparse.eval_collectBalanced, rawRowCheck18965]

theorem rawRowCheck18966 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form1 = rawRow18966 := by decide +kernel

theorem rowCheck18966 : row18966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18966 := by decide +kernel

theorem rowEval18966 (x : Key → ℝ) : Integer.Sparse.eval row18966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18966, Integer.Sparse.eval_collectBalanced, rawRowCheck18966]

theorem rawRowCheck18967 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form1 = rawRow18967 := by decide +kernel

theorem rowCheck18967 : row18967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18967 := by decide +kernel

theorem rowEval18967 (x : Key → ℝ) : Integer.Sparse.eval row18967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18967, Integer.Sparse.eval_collectBalanced, rawRowCheck18967]

theorem rawRowCheck18968 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form1 = rawRow18968 := by decide +kernel

theorem rowCheck18968 : row18968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18968 := by decide +kernel

theorem rowEval18968 (x : Key → ℝ) : Integer.Sparse.eval row18968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18968, Integer.Sparse.eval_collectBalanced, rawRowCheck18968]

theorem rawRowCheck18969 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form1 = rawRow18969 := by decide +kernel

theorem rowCheck18969 : row18969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18969 := by decide +kernel

theorem rowEval18969 (x : Key → ℝ) : Integer.Sparse.eval row18969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18969, Integer.Sparse.eval_collectBalanced, rawRowCheck18969]

theorem rawRowCheck18970 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form1 = rawRow18970 := by decide +kernel

theorem rowCheck18970 : row18970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18970 := by decide +kernel

theorem rowEval18970 (x : Key → ℝ) : Integer.Sparse.eval row18970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18970, Integer.Sparse.eval_collectBalanced, rawRowCheck18970]

theorem rawRowCheck18971 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form1 = rawRow18971 := by decide +kernel

theorem rowCheck18971 : row18971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18971 := by decide +kernel

theorem rowEval18971 (x : Key → ℝ) : Integer.Sparse.eval row18971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18971, Integer.Sparse.eval_collectBalanced, rawRowCheck18971]

theorem rawRowCheck18972 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18972 := by decide +kernel

theorem rowCheck18972 : row18972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18972 := by decide +kernel

theorem rowEval18972 (x : Key → ℝ) : Integer.Sparse.eval row18972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18972, Integer.Sparse.eval_collectBalanced, rawRowCheck18972]

theorem rawRowCheck18973 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18973 := by decide +kernel

theorem rowCheck18973 : row18973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18973 := by decide +kernel

theorem rowEval18973 (x : Key → ℝ) : Integer.Sparse.eval row18973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18973, Integer.Sparse.eval_collectBalanced, rawRowCheck18973]

theorem rawRowCheck18974 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18974 := by decide +kernel

theorem rowCheck18974 : row18974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18974 := by decide +kernel

theorem rowEval18974 (x : Key → ℝ) : Integer.Sparse.eval row18974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18974, Integer.Sparse.eval_collectBalanced, rawRowCheck18974]

theorem rawRowCheck18975 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18975 := by decide +kernel

theorem rowCheck18975 : row18975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18975 := by decide +kernel

theorem rowEval18975 (x : Key → ℝ) : Integer.Sparse.eval row18975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18975, Integer.Sparse.eval_collectBalanced, rawRowCheck18975]

theorem rawRowCheck18976 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18976 := by decide +kernel

theorem rowCheck18976 : row18976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18976 := by decide +kernel

theorem rowEval18976 (x : Key → ℝ) : Integer.Sparse.eval row18976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18976, Integer.Sparse.eval_collectBalanced, rawRowCheck18976]

theorem rawRowCheck18977 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18977 := by decide +kernel

theorem rowCheck18977 : row18977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18977 := by decide +kernel

theorem rowEval18977 (x : Key → ℝ) : Integer.Sparse.eval row18977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18977, Integer.Sparse.eval_collectBalanced, rawRowCheck18977]

theorem rawRowCheck18978 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18978 := by decide +kernel

theorem rowCheck18978 : row18978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18978 := by decide +kernel

theorem rowEval18978 (x : Key → ℝ) : Integer.Sparse.eval row18978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18978, Integer.Sparse.eval_collectBalanced, rawRowCheck18978]

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

theorem rawRowCheck19099 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19099 := by decide +kernel

theorem rowCheck19099 : row19099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19099 := by decide +kernel

theorem rowEval19099 (x : Key → ℝ) : Integer.Sparse.eval row19099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19099, Integer.Sparse.eval_collectBalanced, rawRowCheck19099]

theorem rawRowCheck19100 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19100 := by decide +kernel

theorem rowCheck19100 : row19100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19100 := by decide +kernel

theorem rowEval19100 (x : Key → ℝ) : Integer.Sparse.eval row19100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19100, Integer.Sparse.eval_collectBalanced, rawRowCheck19100]

theorem rawRowCheck19101 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19101 := by decide +kernel

theorem rowCheck19101 : row19101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19101 := by decide +kernel

theorem rowEval19101 (x : Key → ℝ) : Integer.Sparse.eval row19101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19101, Integer.Sparse.eval_collectBalanced, rawRowCheck19101]

theorem rawRowCheck19102 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19102 := by decide +kernel

theorem rowCheck19102 : row19102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19102 := by decide +kernel

theorem rowEval19102 (x : Key → ℝ) : Integer.Sparse.eval row19102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19102, Integer.Sparse.eval_collectBalanced, rawRowCheck19102]

theorem rawRowCheck19103 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19103 := by decide +kernel

theorem rowCheck19103 : row19103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19103 := by decide +kernel

theorem rowEval19103 (x : Key → ℝ) : Integer.Sparse.eval row19103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19103, Integer.Sparse.eval_collectBalanced, rawRowCheck19103]

theorem rawRowCheck19104 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19104 := by decide +kernel

theorem rowCheck19104 : row19104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19104 := by decide +kernel

theorem rowEval19104 (x : Key → ℝ) : Integer.Sparse.eval row19104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19104, Integer.Sparse.eval_collectBalanced, rawRowCheck19104]

theorem rawRowCheck19105 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19105 := by decide +kernel

theorem rowCheck19105 : row19105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19105 := by decide +kernel

theorem rowEval19105 (x : Key → ℝ) : Integer.Sparse.eval row19105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19105, Integer.Sparse.eval_collectBalanced, rawRowCheck19105]

theorem rawRowCheck19106 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19106 := by decide +kernel

theorem rowCheck19106 : row19106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19106 := by decide +kernel

theorem rowEval19106 (x : Key → ℝ) : Integer.Sparse.eval row19106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19106, Integer.Sparse.eval_collectBalanced, rawRowCheck19106]

theorem rawRowCheck19107 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19107 := by decide +kernel

theorem rowCheck19107 : row19107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19107 := by decide +kernel

theorem rowEval19107 (x : Key → ℝ) : Integer.Sparse.eval row19107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19107, Integer.Sparse.eval_collectBalanced, rawRowCheck19107]

theorem rawRowCheck19108 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19108 := by decide +kernel

theorem rowCheck19108 : row19108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19108 := by decide +kernel

theorem rowEval19108 (x : Key → ℝ) : Integer.Sparse.eval row19108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19108, Integer.Sparse.eval_collectBalanced, rawRowCheck19108]

theorem rawRowCheck19109 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19109 := by decide +kernel

theorem rowCheck19109 : row19109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19109 := by decide +kernel

theorem rowEval19109 (x : Key → ℝ) : Integer.Sparse.eval row19109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19109, Integer.Sparse.eval_collectBalanced, rawRowCheck19109]

theorem rawRowCheck19110 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19110 := by decide +kernel

theorem rowCheck19110 : row19110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19110 := by decide +kernel

theorem rowEval19110 (x : Key → ℝ) : Integer.Sparse.eval row19110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19110, Integer.Sparse.eval_collectBalanced, rawRowCheck19110]

theorem rawRowCheck19111 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19111 := by decide +kernel

theorem rowCheck19111 : row19111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19111 := by decide +kernel

theorem rowEval19111 (x : Key → ℝ) : Integer.Sparse.eval row19111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19111, Integer.Sparse.eval_collectBalanced, rawRowCheck19111]

theorem rawRowCheck19112 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19112 := by decide +kernel

theorem rowCheck19112 : row19112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19112 := by decide +kernel

theorem rowEval19112 (x : Key → ℝ) : Integer.Sparse.eval row19112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19112, Integer.Sparse.eval_collectBalanced, rawRowCheck19112]

theorem rawRowCheck19113 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form1 = rawRow19113 := by decide +kernel

theorem rowCheck19113 : row19113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19113 := by decide +kernel

theorem rowEval19113 (x : Key → ℝ) : Integer.Sparse.eval row19113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19113, Integer.Sparse.eval_collectBalanced, rawRowCheck19113]

theorem rawRowCheck19114 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form1 = rawRow19114 := by decide +kernel

theorem rowCheck19114 : row19114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19114 := by decide +kernel

theorem rowEval19114 (x : Key → ℝ) : Integer.Sparse.eval row19114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19114, Integer.Sparse.eval_collectBalanced, rawRowCheck19114]

theorem rawRowCheck19115 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form1 = rawRow19115 := by decide +kernel

theorem rowCheck19115 : row19115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19115 := by decide +kernel

theorem rowEval19115 (x : Key → ℝ) : Integer.Sparse.eval row19115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19115, Integer.Sparse.eval_collectBalanced, rawRowCheck19115]

theorem rawRowCheck19116 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form1 = rawRow19116 := by decide +kernel

theorem rowCheck19116 : row19116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19116 := by decide +kernel

theorem rowEval19116 (x : Key → ℝ) : Integer.Sparse.eval row19116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19116, Integer.Sparse.eval_collectBalanced, rawRowCheck19116]

theorem rawRowCheck19117 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form1 = rawRow19117 := by decide +kernel

theorem rowCheck19117 : row19117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19117 := by decide +kernel

theorem rowEval19117 (x : Key → ℝ) : Integer.Sparse.eval row19117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19117, Integer.Sparse.eval_collectBalanced, rawRowCheck19117]

theorem rawRowCheck19118 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form1 = rawRow19118 := by decide +kernel

theorem rowCheck19118 : row19118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19118 := by decide +kernel

theorem rowEval19118 (x : Key → ℝ) : Integer.Sparse.eval row19118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19118, Integer.Sparse.eval_collectBalanced, rawRowCheck19118]

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

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18959 x
  · exact rowEval18960 x
  · exact rowEval18961 x
  · exact rowEval18962 x
  · exact rowEval18963 x
  · exact rowEval18964 x
  · exact rowEval18965 x
  · exact rowEval18966 x
  · exact rowEval18967 x
  · exact rowEval18968 x
  · exact rowEval18969 x
  · exact rowEval18970 x
  · exact rowEval18971 x
  · exact rowEval18972 x
  · exact rowEval18973 x
  · exact rowEval18974 x
  · exact rowEval18975 x
  · exact rowEval18976 x
  · exact rowEval18977 x
  · exact rowEval18978 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

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

theorem rawRowCheck19244 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19244 := by decide +kernel

theorem rowCheck19244 : row19244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19244 := by decide +kernel

theorem rowEval19244 (x : Key → ℝ) : Integer.Sparse.eval row19244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19244, Integer.Sparse.eval_collectBalanced, rawRowCheck19244]

theorem rawRowCheck19245 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19245 := by decide +kernel

theorem rowCheck19245 : row19245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19245 := by decide +kernel

theorem rowEval19245 (x : Key → ℝ) : Integer.Sparse.eval row19245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19245, Integer.Sparse.eval_collectBalanced, rawRowCheck19245]

theorem rawRowCheck19246 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19246 := by decide +kernel

theorem rowCheck19246 : row19246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19246 := by decide +kernel

theorem rowEval19246 (x : Key → ℝ) : Integer.Sparse.eval row19246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19246, Integer.Sparse.eval_collectBalanced, rawRowCheck19246]

theorem rawRowCheck19247 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19247 := by decide +kernel

theorem rowCheck19247 : row19247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19247 := by decide +kernel

theorem rowEval19247 (x : Key → ℝ) : Integer.Sparse.eval row19247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19247, Integer.Sparse.eval_collectBalanced, rawRowCheck19247]

theorem rawRowCheck19248 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19248 := by decide +kernel

theorem rowCheck19248 : row19248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19248 := by decide +kernel

theorem rowEval19248 (x : Key → ℝ) : Integer.Sparse.eval row19248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19248, Integer.Sparse.eval_collectBalanced, rawRowCheck19248]

theorem rawRowCheck19294 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19294 := by decide +kernel

theorem rowCheck19294 : row19294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19294 := by decide +kernel

theorem rowEval19294 (x : Key → ℝ) : Integer.Sparse.eval row19294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19294, Integer.Sparse.eval_collectBalanced, rawRowCheck19294]

theorem rawRowCheck19295 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19295 := by decide +kernel

theorem rowCheck19295 : row19295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19295 := by decide +kernel

theorem rowEval19295 (x : Key → ℝ) : Integer.Sparse.eval row19295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19295, Integer.Sparse.eval_collectBalanced, rawRowCheck19295]

theorem rawRowCheck19296 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19296 := by decide +kernel

theorem rowCheck19296 : row19296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19296 := by decide +kernel

theorem rowEval19296 (x : Key → ℝ) : Integer.Sparse.eval row19296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19296, Integer.Sparse.eval_collectBalanced, rawRowCheck19296]

theorem rawRowCheck19297 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form1 = rawRow19297 := by decide +kernel

theorem rowCheck19297 : row19297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19297 := by decide +kernel

theorem rowEval19297 (x : Key → ℝ) : Integer.Sparse.eval row19297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19297, Integer.Sparse.eval_collectBalanced, rawRowCheck19297]

theorem rawRowCheck19298 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form1 = rawRow19298 := by decide +kernel

theorem rowCheck19298 : row19298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19298 := by decide +kernel

theorem rowEval19298 (x : Key → ℝ) : Integer.Sparse.eval row19298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19298, Integer.Sparse.eval_collectBalanced, rawRowCheck19298]

theorem rawRowCheck19299 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form1 = rawRow19299 := by decide +kernel

theorem rowCheck19299 : row19299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19299 := by decide +kernel

theorem rowEval19299 (x : Key → ℝ) : Integer.Sparse.eval row19299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19299, Integer.Sparse.eval_collectBalanced, rawRowCheck19299]

theorem rawRowCheck19300 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form1 = rawRow19300 := by decide +kernel

theorem rowCheck19300 : row19300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19300 := by decide +kernel

theorem rowEval19300 (x : Key → ℝ) : Integer.Sparse.eval row19300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19300, Integer.Sparse.eval_collectBalanced, rawRowCheck19300]

theorem rawRowCheck19301 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form1 = rawRow19301 := by decide +kernel

theorem rowCheck19301 : row19301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19301 := by decide +kernel

theorem rowEval19301 (x : Key → ℝ) : Integer.Sparse.eval row19301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19301, Integer.Sparse.eval_collectBalanced, rawRowCheck19301]

theorem rawRowCheck19302 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form1 = rawRow19302 := by decide +kernel

theorem rowCheck19302 : row19302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19302 := by decide +kernel

theorem rowEval19302 (x : Key → ℝ) : Integer.Sparse.eval row19302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19302, Integer.Sparse.eval_collectBalanced, rawRowCheck19302]

theorem rawRowCheck19303 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form1 = rawRow19303 := by decide +kernel

theorem rowCheck19303 : row19303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19303 := by decide +kernel

theorem rowEval19303 (x : Key → ℝ) : Integer.Sparse.eval row19303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19303, Integer.Sparse.eval_collectBalanced, rawRowCheck19303]

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

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19099 x
  · exact rowEval19100 x
  · exact rowEval19101 x
  · exact rowEval19102 x
  · exact rowEval19103 x
  · exact rowEval19104 x
  · exact rowEval19105 x
  · exact rowEval19106 x
  · exact rowEval19107 x
  · exact rowEval19108 x
  · exact rowEval19109 x
  · exact rowEval19110 x
  · exact rowEval19111 x
  · exact rowEval19112 x
  · exact rowEval19113 x
  · exact rowEval19114 x
  · exact rowEval19115 x
  · exact rowEval19116 x
  · exact rowEval19117 x
  · exact rowEval19118 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

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

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19244 x
  · exact rowEval19245 x
  · exact rowEval19246 x
  · exact rowEval19247 x
  · exact rowEval19248 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

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

theorem entryCheck9_1 : entry9_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_1 k)) := by decide +kernel

theorem rowsSound9_1 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19294 x
  · exact rowEval19295 x
  · exact rowEval19296 x
  · exact rowEval19297 x
  · exact rowEval19298 x
  · exact rowEval19299 x
  · exact rowEval19300 x
  · exact rowEval19301 x
  · exact rowEval19302 x
  · exact rowEval19303 x

theorem entryEval9_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_1 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck9_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_1]

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

theorem entryEvalRow1_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 1).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval1_0 B hB
  · exact entryEval1_1 B hB
  · exact (entryEval2_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e_oai
