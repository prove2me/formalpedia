-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:17:30.678147+00:00
-- url     : https://prove2.me/submissions/dfd20751-86ab-40b4-9cba-23c2a8100944

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
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

theorem rawRowCheck12339 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form1 = rawRow12339 := by decide +kernel

theorem rowCheck12339 : row12339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12339 := by decide +kernel

theorem rowEval12339 (x : Key → ℝ) : Integer.Sparse.eval row12339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12339, Integer.Sparse.eval_collectBalanced, rawRowCheck12339]

theorem rawRowCheck12340 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form1 = rawRow12340 := by decide +kernel

theorem rowCheck12340 : row12340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12340 := by decide +kernel

theorem rowEval12340 (x : Key → ℝ) : Integer.Sparse.eval row12340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12340, Integer.Sparse.eval_collectBalanced, rawRowCheck12340]

theorem rawRowCheck12341 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form1 = rawRow12341 := by decide +kernel

theorem rowCheck12341 : row12341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12341 := by decide +kernel

theorem rowEval12341 (x : Key → ℝ) : Integer.Sparse.eval row12341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12341, Integer.Sparse.eval_collectBalanced, rawRowCheck12341]

theorem rawRowCheck12342 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form1 = rawRow12342 := by decide +kernel

theorem rowCheck12342 : row12342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12342 := by decide +kernel

theorem rowEval12342 (x : Key → ℝ) : Integer.Sparse.eval row12342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12342, Integer.Sparse.eval_collectBalanced, rawRowCheck12342]

theorem rawRowCheck12343 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form1 = rawRow12343 := by decide +kernel

theorem rowCheck12343 : row12343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12343 := by decide +kernel

theorem rowEval12343 (x : Key → ℝ) : Integer.Sparse.eval row12343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12343, Integer.Sparse.eval_collectBalanced, rawRowCheck12343]

theorem rawRowCheck12344 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form1 = rawRow12344 := by decide +kernel

theorem rowCheck12344 : row12344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12344 := by decide +kernel

theorem rowEval12344 (x : Key → ℝ) : Integer.Sparse.eval row12344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12344, Integer.Sparse.eval_collectBalanced, rawRowCheck12344]

theorem rawRowCheck12345 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form1 = rawRow12345 := by decide +kernel

theorem rowCheck12345 : row12345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12345 := by decide +kernel

theorem rowEval12345 (x : Key → ℝ) : Integer.Sparse.eval row12345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12345, Integer.Sparse.eval_collectBalanced, rawRowCheck12345]

theorem rawRowCheck12346 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form1 = rawRow12346 := by decide +kernel

theorem rowCheck12346 : row12346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12346 := by decide +kernel

theorem rowEval12346 (x : Key → ℝ) : Integer.Sparse.eval row12346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12346, Integer.Sparse.eval_collectBalanced, rawRowCheck12346]

theorem rawRowCheck12347 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form2 = rawRow12347 := by decide +kernel

theorem rowCheck12347 : row12347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12347 := by decide +kernel

theorem rowEval12347 (x : Key → ℝ) : Integer.Sparse.eval row12347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12347, Integer.Sparse.eval_collectBalanced, rawRowCheck12347]

theorem rawRowCheck12348 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form2 = rawRow12348 := by decide +kernel

theorem rowCheck12348 : row12348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12348 := by decide +kernel

theorem rowEval12348 (x : Key → ℝ) : Integer.Sparse.eval row12348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12348, Integer.Sparse.eval_collectBalanced, rawRowCheck12348]

theorem rawRowCheck12349 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form2 = rawRow12349 := by decide +kernel

theorem rowCheck12349 : row12349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12349 := by decide +kernel

theorem rowEval12349 (x : Key → ℝ) : Integer.Sparse.eval row12349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12349, Integer.Sparse.eval_collectBalanced, rawRowCheck12349]

theorem rawRowCheck12350 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form2 = rawRow12350 := by decide +kernel

theorem rowCheck12350 : row12350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12350 := by decide +kernel

theorem rowEval12350 (x : Key → ℝ) : Integer.Sparse.eval row12350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12350, Integer.Sparse.eval_collectBalanced, rawRowCheck12350]

theorem rawRowCheck12351 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form2 = rawRow12351 := by decide +kernel

theorem rowCheck12351 : row12351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12351 := by decide +kernel

theorem rowEval12351 (x : Key → ℝ) : Integer.Sparse.eval row12351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12351, Integer.Sparse.eval_collectBalanced, rawRowCheck12351]

theorem rawRowCheck12352 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form2 = rawRow12352 := by decide +kernel

theorem rowCheck12352 : row12352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12352 := by decide +kernel

theorem rowEval12352 (x : Key → ℝ) : Integer.Sparse.eval row12352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12352, Integer.Sparse.eval_collectBalanced, rawRowCheck12352]

theorem rawRowCheck12353 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form2 = rawRow12353 := by decide +kernel

theorem rowCheck12353 : row12353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12353 := by decide +kernel

theorem rowEval12353 (x : Key → ℝ) : Integer.Sparse.eval row12353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12353, Integer.Sparse.eval_collectBalanced, rawRowCheck12353]

theorem rawRowCheck12354 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form2 = rawRow12354 := by decide +kernel

theorem rowCheck12354 : row12354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12354 := by decide +kernel

theorem rowEval12354 (x : Key → ℝ) : Integer.Sparse.eval row12354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12354, Integer.Sparse.eval_collectBalanced, rawRowCheck12354]

theorem rawRowCheck12355 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form3 = rawRow12355 := by decide +kernel

theorem rowCheck12355 : row12355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12355 := by decide +kernel

theorem rowEval12355 (x : Key → ℝ) : Integer.Sparse.eval row12355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12355, Integer.Sparse.eval_collectBalanced, rawRowCheck12355]

theorem rawRowCheck12356 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form3 = rawRow12356 := by decide +kernel

theorem rowCheck12356 : row12356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12356 := by decide +kernel

theorem rowEval12356 (x : Key → ℝ) : Integer.Sparse.eval row12356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12356, Integer.Sparse.eval_collectBalanced, rawRowCheck12356]

theorem rawRowCheck12357 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form3 = rawRow12357 := by decide +kernel

theorem rowCheck12357 : row12357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12357 := by decide +kernel

theorem rowEval12357 (x : Key → ℝ) : Integer.Sparse.eval row12357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12357, Integer.Sparse.eval_collectBalanced, rawRowCheck12357]

theorem rawRowCheck12358 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form3 = rawRow12358 := by decide +kernel

theorem rowCheck12358 : row12358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12358 := by decide +kernel

theorem rowEval12358 (x : Key → ℝ) : Integer.Sparse.eval row12358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12358, Integer.Sparse.eval_collectBalanced, rawRowCheck12358]

theorem rawRowCheck12359 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form3 = rawRow12359 := by decide +kernel

theorem rowCheck12359 : row12359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12359 := by decide +kernel

theorem rowEval12359 (x : Key → ℝ) : Integer.Sparse.eval row12359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12359, Integer.Sparse.eval_collectBalanced, rawRowCheck12359]

theorem rawRowCheck12360 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form3 = rawRow12360 := by decide +kernel

theorem rowCheck12360 : row12360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12360 := by decide +kernel

theorem rowEval12360 (x : Key → ℝ) : Integer.Sparse.eval row12360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12360, Integer.Sparse.eval_collectBalanced, rawRowCheck12360]

theorem rawRowCheck12361 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form3 = rawRow12361 := by decide +kernel

theorem rowCheck12361 : row12361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12361 := by decide +kernel

theorem rowEval12361 (x : Key → ℝ) : Integer.Sparse.eval row12361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12361, Integer.Sparse.eval_collectBalanced, rawRowCheck12361]

theorem rawRowCheck12362 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form3 = rawRow12362 := by decide +kernel

theorem rowCheck12362 : row12362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12362 := by decide +kernel

theorem rowEval12362 (x : Key → ℝ) : Integer.Sparse.eval row12362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12362, Integer.Sparse.eval_collectBalanced, rawRowCheck12362]

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

theorem rawRowCheck12371 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form5 = rawRow12371 := by decide +kernel

theorem rowCheck12371 : row12371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12371 := by decide +kernel

theorem rowEval12371 (x : Key → ℝ) : Integer.Sparse.eval row12371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12371, Integer.Sparse.eval_collectBalanced, rawRowCheck12371]

theorem rawRowCheck12372 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form5 = rawRow12372 := by decide +kernel

theorem rowCheck12372 : row12372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12372 := by decide +kernel

theorem rowEval12372 (x : Key → ℝ) : Integer.Sparse.eval row12372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12372, Integer.Sparse.eval_collectBalanced, rawRowCheck12372]

theorem rawRowCheck12373 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form5 = rawRow12373 := by decide +kernel

theorem rowCheck12373 : row12373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12373 := by decide +kernel

theorem rowEval12373 (x : Key → ℝ) : Integer.Sparse.eval row12373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12373, Integer.Sparse.eval_collectBalanced, rawRowCheck12373]

theorem rawRowCheck12374 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form5 = rawRow12374 := by decide +kernel

theorem rowCheck12374 : row12374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12374 := by decide +kernel

theorem rowEval12374 (x : Key → ℝ) : Integer.Sparse.eval row12374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12374, Integer.Sparse.eval_collectBalanced, rawRowCheck12374]

theorem rawRowCheck12375 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form5 = rawRow12375 := by decide +kernel

theorem rowCheck12375 : row12375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12375 := by decide +kernel

theorem rowEval12375 (x : Key → ℝ) : Integer.Sparse.eval row12375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12375, Integer.Sparse.eval_collectBalanced, rawRowCheck12375]

theorem rawRowCheck12376 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form5 = rawRow12376 := by decide +kernel

theorem rowCheck12376 : row12376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12376 := by decide +kernel

theorem rowEval12376 (x : Key → ℝ) : Integer.Sparse.eval row12376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12376, Integer.Sparse.eval_collectBalanced, rawRowCheck12376]

theorem rawRowCheck12377 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form5 = rawRow12377 := by decide +kernel

theorem rowCheck12377 : row12377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12377 := by decide +kernel

theorem rowEval12377 (x : Key → ℝ) : Integer.Sparse.eval row12377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12377, Integer.Sparse.eval_collectBalanced, rawRowCheck12377]

theorem rawRowCheck12378 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form5 = rawRow12378 := by decide +kernel

theorem rowCheck12378 : row12378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12378 := by decide +kernel

theorem rowEval12378 (x : Key → ℝ) : Integer.Sparse.eval row12378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12378, Integer.Sparse.eval_collectBalanced, rawRowCheck12378]

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

theorem rawRowCheck12387 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form7 = rawRow12387 := by decide +kernel

theorem rowCheck12387 : row12387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12387 := by decide +kernel

theorem rowEval12387 (x : Key → ℝ) : Integer.Sparse.eval row12387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12387, Integer.Sparse.eval_collectBalanced, rawRowCheck12387]

theorem rawRowCheck12388 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form7 = rawRow12388 := by decide +kernel

theorem rowCheck12388 : row12388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12388 := by decide +kernel

theorem rowEval12388 (x : Key → ℝ) : Integer.Sparse.eval row12388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12388, Integer.Sparse.eval_collectBalanced, rawRowCheck12388]

theorem rawRowCheck12389 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form7 = rawRow12389 := by decide +kernel

theorem rowCheck12389 : row12389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12389 := by decide +kernel

theorem rowEval12389 (x : Key → ℝ) : Integer.Sparse.eval row12389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12389, Integer.Sparse.eval_collectBalanced, rawRowCheck12389]

theorem rawRowCheck12390 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form7 = rawRow12390 := by decide +kernel

theorem rowCheck12390 : row12390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12390 := by decide +kernel

theorem rowEval12390 (x : Key → ℝ) : Integer.Sparse.eval row12390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12390, Integer.Sparse.eval_collectBalanced, rawRowCheck12390]

theorem rawRowCheck12391 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form7 = rawRow12391 := by decide +kernel

theorem rowCheck12391 : row12391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12391 := by decide +kernel

theorem rowEval12391 (x : Key → ℝ) : Integer.Sparse.eval row12391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12391, Integer.Sparse.eval_collectBalanced, rawRowCheck12391]

theorem rawRowCheck12392 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form7 = rawRow12392 := by decide +kernel

theorem rowCheck12392 : row12392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12392 := by decide +kernel

theorem rowEval12392 (x : Key → ℝ) : Integer.Sparse.eval row12392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12392, Integer.Sparse.eval_collectBalanced, rawRowCheck12392]

theorem rawRowCheck12393 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form7 = rawRow12393 := by decide +kernel

theorem rowCheck12393 : row12393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12393 := by decide +kernel

theorem rowEval12393 (x : Key → ℝ) : Integer.Sparse.eval row12393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12393, Integer.Sparse.eval_collectBalanced, rawRowCheck12393]

theorem rawRowCheck12394 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form7 = rawRow12394 := by decide +kernel

theorem rowCheck12394 : row12394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12394 := by decide +kernel

theorem rowEval12394 (x : Key → ℝ) : Integer.Sparse.eval row12394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12394, Integer.Sparse.eval_collectBalanced, rawRowCheck12394]

theorem rawRowCheck12395 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form8 = rawRow12395 := by decide +kernel

theorem rowCheck12395 : row12395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12395 := by decide +kernel

theorem rowEval12395 (x : Key → ℝ) : Integer.Sparse.eval row12395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12395, Integer.Sparse.eval_collectBalanced, rawRowCheck12395]

theorem rawRowCheck12396 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form8 = rawRow12396 := by decide +kernel

theorem rowCheck12396 : row12396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12396 := by decide +kernel

theorem rowEval12396 (x : Key → ℝ) : Integer.Sparse.eval row12396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12396, Integer.Sparse.eval_collectBalanced, rawRowCheck12396]

theorem rawRowCheck12397 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form8 = rawRow12397 := by decide +kernel

theorem rowCheck12397 : row12397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12397 := by decide +kernel

theorem rowEval12397 (x : Key → ℝ) : Integer.Sparse.eval row12397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12397, Integer.Sparse.eval_collectBalanced, rawRowCheck12397]

theorem rawRowCheck12398 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form8 = rawRow12398 := by decide +kernel

theorem rowCheck12398 : row12398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12398 := by decide +kernel

theorem rowEval12398 (x : Key → ℝ) : Integer.Sparse.eval row12398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12398, Integer.Sparse.eval_collectBalanced, rawRowCheck12398]

theorem rawRowCheck12399 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form8 = rawRow12399 := by decide +kernel

theorem rowCheck12399 : row12399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12399 := by decide +kernel

theorem rowEval12399 (x : Key → ℝ) : Integer.Sparse.eval row12399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12399, Integer.Sparse.eval_collectBalanced, rawRowCheck12399]

theorem rawRowCheck12400 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form8 = rawRow12400 := by decide +kernel

theorem rowCheck12400 : row12400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12400 := by decide +kernel

theorem rowEval12400 (x : Key → ℝ) : Integer.Sparse.eval row12400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12400, Integer.Sparse.eval_collectBalanced, rawRowCheck12400]

theorem rawRowCheck12401 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form8 = rawRow12401 := by decide +kernel

theorem rowCheck12401 : row12401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12401 := by decide +kernel

theorem rowEval12401 (x : Key → ℝ) : Integer.Sparse.eval row12401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12401, Integer.Sparse.eval_collectBalanced, rawRowCheck12401]

theorem rawRowCheck12402 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form8 = rawRow12402 := by decide +kernel

theorem rowCheck12402 : row12402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12402 := by decide +kernel

theorem rowEval12402 (x : Key → ℝ) : Integer.Sparse.eval row12402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12402, Integer.Sparse.eval_collectBalanced, rawRowCheck12402]

theorem rawRowCheck12403 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form9 = rawRow12403 := by decide +kernel

theorem rowCheck12403 : row12403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12403 := by decide +kernel

theorem rowEval12403 (x : Key → ℝ) : Integer.Sparse.eval row12403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12403, Integer.Sparse.eval_collectBalanced, rawRowCheck12403]

theorem rawRowCheck12404 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form9 = rawRow12404 := by decide +kernel

theorem rowCheck12404 : row12404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12404 := by decide +kernel

theorem rowEval12404 (x : Key → ℝ) : Integer.Sparse.eval row12404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12404, Integer.Sparse.eval_collectBalanced, rawRowCheck12404]

theorem rawRowCheck12405 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form9 = rawRow12405 := by decide +kernel

theorem rowCheck12405 : row12405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12405 := by decide +kernel

theorem rowEval12405 (x : Key → ℝ) : Integer.Sparse.eval row12405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12405, Integer.Sparse.eval_collectBalanced, rawRowCheck12405]

theorem rawRowCheck12406 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form9 = rawRow12406 := by decide +kernel

theorem rowCheck12406 : row12406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12406 := by decide +kernel

theorem rowEval12406 (x : Key → ℝ) : Integer.Sparse.eval row12406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12406, Integer.Sparse.eval_collectBalanced, rawRowCheck12406]

theorem rawRowCheck12407 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form9 = rawRow12407 := by decide +kernel

theorem rowCheck12407 : row12407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12407 := by decide +kernel

theorem rowEval12407 (x : Key → ℝ) : Integer.Sparse.eval row12407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12407, Integer.Sparse.eval_collectBalanced, rawRowCheck12407]

theorem rawRowCheck12408 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form9 = rawRow12408 := by decide +kernel

theorem rowCheck12408 : row12408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12408 := by decide +kernel

theorem rowEval12408 (x : Key → ℝ) : Integer.Sparse.eval row12408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12408, Integer.Sparse.eval_collectBalanced, rawRowCheck12408]

theorem rawRowCheck12409 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form9 = rawRow12409 := by decide +kernel

theorem rowCheck12409 : row12409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12409 := by decide +kernel

theorem rowEval12409 (x : Key → ℝ) : Integer.Sparse.eval row12409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12409, Integer.Sparse.eval_collectBalanced, rawRowCheck12409]

theorem rawRowCheck12410 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form9 = rawRow12410 := by decide +kernel

theorem rowCheck12410 : row12410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12410 := by decide +kernel

theorem rowEval12410 (x : Key → ℝ) : Integer.Sparse.eval row12410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12410, Integer.Sparse.eval_collectBalanced, rawRowCheck12410]

theorem rawRowCheck12411 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form10 = rawRow12411 := by decide +kernel

theorem rowCheck12411 : row12411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12411 := by decide +kernel

theorem rowEval12411 (x : Key → ℝ) : Integer.Sparse.eval row12411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12411, Integer.Sparse.eval_collectBalanced, rawRowCheck12411]

theorem rawRowCheck12412 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form10 = rawRow12412 := by decide +kernel

theorem rowCheck12412 : row12412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12412 := by decide +kernel

theorem rowEval12412 (x : Key → ℝ) : Integer.Sparse.eval row12412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12412, Integer.Sparse.eval_collectBalanced, rawRowCheck12412]

theorem rawRowCheck12413 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form10 = rawRow12413 := by decide +kernel

theorem rowCheck12413 : row12413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12413 := by decide +kernel

theorem rowEval12413 (x : Key → ℝ) : Integer.Sparse.eval row12413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12413, Integer.Sparse.eval_collectBalanced, rawRowCheck12413]

theorem rawRowCheck12414 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form10 = rawRow12414 := by decide +kernel

theorem rowCheck12414 : row12414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12414 := by decide +kernel

theorem rowEval12414 (x : Key → ℝ) : Integer.Sparse.eval row12414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12414, Integer.Sparse.eval_collectBalanced, rawRowCheck12414]

theorem rawRowCheck12415 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form10 = rawRow12415 := by decide +kernel

theorem rowCheck12415 : row12415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12415 := by decide +kernel

theorem rowEval12415 (x : Key → ℝ) : Integer.Sparse.eval row12415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12415, Integer.Sparse.eval_collectBalanced, rawRowCheck12415]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck12416 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form10 = rawRow12416 := by decide +kernel

theorem rowCheck12416 : row12416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12416 := by decide +kernel

theorem rowEval12416 (x : Key → ℝ) : Integer.Sparse.eval row12416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12416, Integer.Sparse.eval_collectBalanced, rawRowCheck12416]

theorem rawRowCheck12417 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form10 = rawRow12417 := by decide +kernel

theorem rowCheck12417 : row12417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12417 := by decide +kernel

theorem rowEval12417 (x : Key → ℝ) : Integer.Sparse.eval row12417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12417, Integer.Sparse.eval_collectBalanced, rawRowCheck12417]

theorem rawRowCheck12418 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form10 = rawRow12418 := by decide +kernel

theorem rowCheck12418 : row12418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12418 := by decide +kernel

theorem rowEval12418 (x : Key → ℝ) : Integer.Sparse.eval row12418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12418, Integer.Sparse.eval_collectBalanced, rawRowCheck12418]

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

theorem rawRowCheck12427 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form12 = rawRow12427 := by decide +kernel

theorem rowCheck12427 : row12427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12427 := by decide +kernel

theorem rowEval12427 (x : Key → ℝ) : Integer.Sparse.eval row12427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12427, Integer.Sparse.eval_collectBalanced, rawRowCheck12427]

theorem rawRowCheck12428 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form12 = rawRow12428 := by decide +kernel

theorem rowCheck12428 : row12428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12428 := by decide +kernel

theorem rowEval12428 (x : Key → ℝ) : Integer.Sparse.eval row12428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12428, Integer.Sparse.eval_collectBalanced, rawRowCheck12428]

theorem rawRowCheck12429 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form12 = rawRow12429 := by decide +kernel

theorem rowCheck12429 : row12429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12429 := by decide +kernel

theorem rowEval12429 (x : Key → ℝ) : Integer.Sparse.eval row12429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12429, Integer.Sparse.eval_collectBalanced, rawRowCheck12429]

theorem rawRowCheck12430 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form12 = rawRow12430 := by decide +kernel

theorem rowCheck12430 : row12430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12430 := by decide +kernel

theorem rowEval12430 (x : Key → ℝ) : Integer.Sparse.eval row12430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12430, Integer.Sparse.eval_collectBalanced, rawRowCheck12430]

theorem rawRowCheck12431 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form12 = rawRow12431 := by decide +kernel

theorem rowCheck12431 : row12431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12431 := by decide +kernel

theorem rowEval12431 (x : Key → ℝ) : Integer.Sparse.eval row12431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12431, Integer.Sparse.eval_collectBalanced, rawRowCheck12431]

theorem rawRowCheck12432 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form12 = rawRow12432 := by decide +kernel

theorem rowCheck12432 : row12432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12432 := by decide +kernel

theorem rowEval12432 (x : Key → ℝ) : Integer.Sparse.eval row12432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12432, Integer.Sparse.eval_collectBalanced, rawRowCheck12432]

theorem rawRowCheck12433 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form12 = rawRow12433 := by decide +kernel

theorem rowCheck12433 : row12433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12433 := by decide +kernel

theorem rowEval12433 (x : Key → ℝ) : Integer.Sparse.eval row12433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12433, Integer.Sparse.eval_collectBalanced, rawRowCheck12433]

theorem rawRowCheck12434 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form12 = rawRow12434 := by decide +kernel

theorem rowCheck12434 : row12434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12434 := by decide +kernel

theorem rowEval12434 (x : Key → ℝ) : Integer.Sparse.eval row12434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12434, Integer.Sparse.eval_collectBalanced, rawRowCheck12434]

theorem rawRowCheck12435 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form13 = rawRow12435 := by decide +kernel

theorem rowCheck12435 : row12435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12435 := by decide +kernel

theorem rowEval12435 (x : Key → ℝ) : Integer.Sparse.eval row12435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12435, Integer.Sparse.eval_collectBalanced, rawRowCheck12435]

theorem rawRowCheck12436 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form13 = rawRow12436 := by decide +kernel

theorem rowCheck12436 : row12436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12436 := by decide +kernel

theorem rowEval12436 (x : Key → ℝ) : Integer.Sparse.eval row12436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12436, Integer.Sparse.eval_collectBalanced, rawRowCheck12436]

theorem rawRowCheck12437 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form13 = rawRow12437 := by decide +kernel

theorem rowCheck12437 : row12437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12437 := by decide +kernel

theorem rowEval12437 (x : Key → ℝ) : Integer.Sparse.eval row12437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12437, Integer.Sparse.eval_collectBalanced, rawRowCheck12437]

theorem rawRowCheck12438 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form13 = rawRow12438 := by decide +kernel

theorem rowCheck12438 : row12438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12438 := by decide +kernel

theorem rowEval12438 (x : Key → ℝ) : Integer.Sparse.eval row12438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12438, Integer.Sparse.eval_collectBalanced, rawRowCheck12438]

theorem rawRowCheck12439 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form13 = rawRow12439 := by decide +kernel

theorem rowCheck12439 : row12439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12439 := by decide +kernel

theorem rowEval12439 (x : Key → ℝ) : Integer.Sparse.eval row12439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12439, Integer.Sparse.eval_collectBalanced, rawRowCheck12439]

theorem rawRowCheck12440 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form13 = rawRow12440 := by decide +kernel

theorem rowCheck12440 : row12440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12440 := by decide +kernel

theorem rowEval12440 (x : Key → ℝ) : Integer.Sparse.eval row12440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12440, Integer.Sparse.eval_collectBalanced, rawRowCheck12440]

theorem rawRowCheck12441 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form13 = rawRow12441 := by decide +kernel

theorem rowCheck12441 : row12441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12441 := by decide +kernel

theorem rowEval12441 (x : Key → ℝ) : Integer.Sparse.eval row12441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12441, Integer.Sparse.eval_collectBalanced, rawRowCheck12441]

theorem rawRowCheck12442 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form13 = rawRow12442 := by decide +kernel

theorem rowCheck12442 : row12442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12442 := by decide +kernel

theorem rowEval12442 (x : Key → ℝ) : Integer.Sparse.eval row12442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12442, Integer.Sparse.eval_collectBalanced, rawRowCheck12442]

theorem rawRowCheck12443 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form14 = rawRow12443 := by decide +kernel

theorem rowCheck12443 : row12443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12443 := by decide +kernel

theorem rowEval12443 (x : Key → ℝ) : Integer.Sparse.eval row12443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12443, Integer.Sparse.eval_collectBalanced, rawRowCheck12443]

theorem rawRowCheck12444 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form14 = rawRow12444 := by decide +kernel

theorem rowCheck12444 : row12444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12444 := by decide +kernel

theorem rowEval12444 (x : Key → ℝ) : Integer.Sparse.eval row12444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12444, Integer.Sparse.eval_collectBalanced, rawRowCheck12444]

theorem rawRowCheck12445 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form14 = rawRow12445 := by decide +kernel

theorem rowCheck12445 : row12445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12445 := by decide +kernel

theorem rowEval12445 (x : Key → ℝ) : Integer.Sparse.eval row12445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12445, Integer.Sparse.eval_collectBalanced, rawRowCheck12445]

theorem rawRowCheck12446 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form14 = rawRow12446 := by decide +kernel

theorem rowCheck12446 : row12446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12446 := by decide +kernel

theorem rowEval12446 (x : Key → ℝ) : Integer.Sparse.eval row12446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12446, Integer.Sparse.eval_collectBalanced, rawRowCheck12446]

theorem rawRowCheck12447 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form14 = rawRow12447 := by decide +kernel

theorem rowCheck12447 : row12447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12447 := by decide +kernel

theorem rowEval12447 (x : Key → ℝ) : Integer.Sparse.eval row12447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12447, Integer.Sparse.eval_collectBalanced, rawRowCheck12447]

theorem rawRowCheck12448 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form14 = rawRow12448 := by decide +kernel

theorem rowCheck12448 : row12448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12448 := by decide +kernel

theorem rowEval12448 (x : Key → ℝ) : Integer.Sparse.eval row12448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12448, Integer.Sparse.eval_collectBalanced, rawRowCheck12448]

theorem rawRowCheck12449 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form14 = rawRow12449 := by decide +kernel

theorem rowCheck12449 : row12449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12449 := by decide +kernel

theorem rowEval12449 (x : Key → ℝ) : Integer.Sparse.eval row12449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12449, Integer.Sparse.eval_collectBalanced, rawRowCheck12449]

theorem rawRowCheck12450 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form14 = rawRow12450 := by decide +kernel

theorem rowCheck12450 : row12450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12450 := by decide +kernel

theorem rowEval12450 (x : Key → ℝ) : Integer.Sparse.eval row12450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12450, Integer.Sparse.eval_collectBalanced, rawRowCheck12450]

theorem rawRowCheck12451 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form15 = rawRow12451 := by decide +kernel

theorem rowCheck12451 : row12451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12451 := by decide +kernel

theorem rowEval12451 (x : Key → ℝ) : Integer.Sparse.eval row12451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12451, Integer.Sparse.eval_collectBalanced, rawRowCheck12451]

theorem rawRowCheck12452 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form15 = rawRow12452 := by decide +kernel

theorem rowCheck12452 : row12452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12452 := by decide +kernel

theorem rowEval12452 (x : Key → ℝ) : Integer.Sparse.eval row12452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12452, Integer.Sparse.eval_collectBalanced, rawRowCheck12452]

theorem rawRowCheck12453 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form15 = rawRow12453 := by decide +kernel

theorem rowCheck12453 : row12453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12453 := by decide +kernel

theorem rowEval12453 (x : Key → ℝ) : Integer.Sparse.eval row12453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12453, Integer.Sparse.eval_collectBalanced, rawRowCheck12453]

theorem rawRowCheck12454 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form15 = rawRow12454 := by decide +kernel

theorem rowCheck12454 : row12454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12454 := by decide +kernel

theorem rowEval12454 (x : Key → ℝ) : Integer.Sparse.eval row12454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12454, Integer.Sparse.eval_collectBalanced, rawRowCheck12454]

theorem rawRowCheck12455 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form15 = rawRow12455 := by decide +kernel

theorem rowCheck12455 : row12455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12455 := by decide +kernel

theorem rowEval12455 (x : Key → ℝ) : Integer.Sparse.eval row12455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12455, Integer.Sparse.eval_collectBalanced, rawRowCheck12455]

theorem rawRowCheck12456 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form15 = rawRow12456 := by decide +kernel

theorem rowCheck12456 : row12456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12456 := by decide +kernel

theorem rowEval12456 (x : Key → ℝ) : Integer.Sparse.eval row12456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12456, Integer.Sparse.eval_collectBalanced, rawRowCheck12456]

theorem rawRowCheck12457 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form15 = rawRow12457 := by decide +kernel

theorem rowCheck12457 : row12457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12457 := by decide +kernel

theorem rowEval12457 (x : Key → ℝ) : Integer.Sparse.eval row12457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12457, Integer.Sparse.eval_collectBalanced, rawRowCheck12457]

theorem rawRowCheck12458 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form15 = rawRow12458 := by decide +kernel

theorem rowCheck12458 : row12458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12458 := by decide +kernel

theorem rowEval12458 (x : Key → ℝ) : Integer.Sparse.eval row12458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12458, Integer.Sparse.eval_collectBalanced, rawRowCheck12458]

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

theorem rawRowCheck12467 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form17 = rawRow12467 := by decide +kernel

theorem rowCheck12467 : row12467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12467 := by decide +kernel

theorem rowEval12467 (x : Key → ℝ) : Integer.Sparse.eval row12467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12467, Integer.Sparse.eval_collectBalanced, rawRowCheck12467]

theorem rawRowCheck12468 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form17 = rawRow12468 := by decide +kernel

theorem rowCheck12468 : row12468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12468 := by decide +kernel

theorem rowEval12468 (x : Key → ℝ) : Integer.Sparse.eval row12468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12468, Integer.Sparse.eval_collectBalanced, rawRowCheck12468]

theorem rawRowCheck12469 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form17 = rawRow12469 := by decide +kernel

theorem rowCheck12469 : row12469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12469 := by decide +kernel

theorem rowEval12469 (x : Key → ℝ) : Integer.Sparse.eval row12469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12469, Integer.Sparse.eval_collectBalanced, rawRowCheck12469]

theorem rawRowCheck12470 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form17 = rawRow12470 := by decide +kernel

theorem rowCheck12470 : row12470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12470 := by decide +kernel

theorem rowEval12470 (x : Key → ℝ) : Integer.Sparse.eval row12470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12470, Integer.Sparse.eval_collectBalanced, rawRowCheck12470]

theorem rawRowCheck12471 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form17 = rawRow12471 := by decide +kernel

theorem rowCheck12471 : row12471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12471 := by decide +kernel

theorem rowEval12471 (x : Key → ℝ) : Integer.Sparse.eval row12471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12471, Integer.Sparse.eval_collectBalanced, rawRowCheck12471]

theorem rawRowCheck12472 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form17 = rawRow12472 := by decide +kernel

theorem rowCheck12472 : row12472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12472 := by decide +kernel

theorem rowEval12472 (x : Key → ℝ) : Integer.Sparse.eval row12472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12472, Integer.Sparse.eval_collectBalanced, rawRowCheck12472]

theorem rawRowCheck12473 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form17 = rawRow12473 := by decide +kernel

theorem rowCheck12473 : row12473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12473 := by decide +kernel

theorem rowEval12473 (x : Key → ℝ) : Integer.Sparse.eval row12473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12473, Integer.Sparse.eval_collectBalanced, rawRowCheck12473]

theorem rawRowCheck12474 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form17 = rawRow12474 := by decide +kernel

theorem rowCheck12474 : row12474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12474 := by decide +kernel

theorem rowEval12474 (x : Key → ℝ) : Integer.Sparse.eval row12474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12474, Integer.Sparse.eval_collectBalanced, rawRowCheck12474]

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

theorem rawRowCheck12483 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form19 = rawRow12483 := by decide +kernel

theorem rowCheck12483 : row12483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12483 := by decide +kernel

theorem rowEval12483 (x : Key → ℝ) : Integer.Sparse.eval row12483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12483, Integer.Sparse.eval_collectBalanced, rawRowCheck12483]

theorem rawRowCheck12484 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form19 = rawRow12484 := by decide +kernel

theorem rowCheck12484 : row12484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12484 := by decide +kernel

theorem rowEval12484 (x : Key → ℝ) : Integer.Sparse.eval row12484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12484, Integer.Sparse.eval_collectBalanced, rawRowCheck12484]

theorem rawRowCheck12485 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form19 = rawRow12485 := by decide +kernel

theorem rowCheck12485 : row12485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12485 := by decide +kernel

theorem rowEval12485 (x : Key → ℝ) : Integer.Sparse.eval row12485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12485, Integer.Sparse.eval_collectBalanced, rawRowCheck12485]

theorem rawRowCheck12486 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form19 = rawRow12486 := by decide +kernel

theorem rowCheck12486 : row12486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12486 := by decide +kernel

theorem rowEval12486 (x : Key → ℝ) : Integer.Sparse.eval row12486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12486, Integer.Sparse.eval_collectBalanced, rawRowCheck12486]

theorem rawRowCheck12487 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form19 = rawRow12487 := by decide +kernel

theorem rowCheck12487 : row12487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12487 := by decide +kernel

theorem rowEval12487 (x : Key → ℝ) : Integer.Sparse.eval row12487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12487, Integer.Sparse.eval_collectBalanced, rawRowCheck12487]

theorem rawRowCheck12488 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form19 = rawRow12488 := by decide +kernel

theorem rowCheck12488 : row12488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12488 := by decide +kernel

theorem rowEval12488 (x : Key → ℝ) : Integer.Sparse.eval row12488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12488, Integer.Sparse.eval_collectBalanced, rawRowCheck12488]

theorem rawRowCheck12489 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form19 = rawRow12489 := by decide +kernel

theorem rowCheck12489 : row12489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12489 := by decide +kernel

theorem rowEval12489 (x : Key → ℝ) : Integer.Sparse.eval row12489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12489, Integer.Sparse.eval_collectBalanced, rawRowCheck12489]

theorem rawRowCheck12490 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form19 = rawRow12490 := by decide +kernel

theorem rowCheck12490 : row12490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12490 := by decide +kernel

theorem rowEval12490 (x : Key → ℝ) : Integer.Sparse.eval row12490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12490, Integer.Sparse.eval_collectBalanced, rawRowCheck12490]

theorem rawRowCheck12491 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form20 = rawRow12491 := by decide +kernel

theorem rowCheck12491 : row12491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12491 := by decide +kernel

theorem rowEval12491 (x : Key → ℝ) : Integer.Sparse.eval row12491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12491, Integer.Sparse.eval_collectBalanced, rawRowCheck12491]

theorem rawRowCheck12492 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form20 = rawRow12492 := by decide +kernel

theorem rowCheck12492 : row12492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12492 := by decide +kernel

theorem rowEval12492 (x : Key → ℝ) : Integer.Sparse.eval row12492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12492, Integer.Sparse.eval_collectBalanced, rawRowCheck12492]

theorem rawRowCheck12493 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form20 = rawRow12493 := by decide +kernel

theorem rowCheck12493 : row12493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12493 := by decide +kernel

theorem rowEval12493 (x : Key → ℝ) : Integer.Sparse.eval row12493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12493, Integer.Sparse.eval_collectBalanced, rawRowCheck12493]

theorem rawRowCheck12494 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form20 = rawRow12494 := by decide +kernel

theorem rowCheck12494 : row12494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12494 := by decide +kernel

theorem rowEval12494 (x : Key → ℝ) : Integer.Sparse.eval row12494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12494, Integer.Sparse.eval_collectBalanced, rawRowCheck12494]

theorem rawRowCheck12495 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form20 = rawRow12495 := by decide +kernel

theorem rowCheck12495 : row12495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12495 := by decide +kernel

theorem rowEval12495 (x : Key → ℝ) : Integer.Sparse.eval row12495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12495, Integer.Sparse.eval_collectBalanced, rawRowCheck12495]

theorem rawRowCheck12496 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form20 = rawRow12496 := by decide +kernel

theorem rowCheck12496 : row12496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12496 := by decide +kernel

theorem rowEval12496 (x : Key → ℝ) : Integer.Sparse.eval row12496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12496, Integer.Sparse.eval_collectBalanced, rawRowCheck12496]

theorem rawRowCheck12497 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form20 = rawRow12497 := by decide +kernel

theorem rowCheck12497 : row12497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12497 := by decide +kernel

theorem rowEval12497 (x : Key → ℝ) : Integer.Sparse.eval row12497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12497, Integer.Sparse.eval_collectBalanced, rawRowCheck12497]

theorem rawRowCheck12498 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form20 = rawRow12498 := by decide +kernel

theorem rowCheck12498 : row12498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12498 := by decide +kernel

theorem rowEval12498 (x : Key → ℝ) : Integer.Sparse.eval row12498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12498, Integer.Sparse.eval_collectBalanced, rawRowCheck12498]

theorem rawRowCheck12499 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form21 = rawRow12499 := by decide +kernel

theorem rowCheck12499 : row12499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12499 := by decide +kernel

theorem rowEval12499 (x : Key → ℝ) : Integer.Sparse.eval row12499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12499, Integer.Sparse.eval_collectBalanced, rawRowCheck12499]

theorem rawRowCheck12500 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form21 = rawRow12500 := by decide +kernel

theorem rowCheck12500 : row12500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12500 := by decide +kernel

theorem rowEval12500 (x : Key → ℝ) : Integer.Sparse.eval row12500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12500, Integer.Sparse.eval_collectBalanced, rawRowCheck12500]

theorem rawRowCheck12501 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form21 = rawRow12501 := by decide +kernel

theorem rowCheck12501 : row12501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12501 := by decide +kernel

theorem rowEval12501 (x : Key → ℝ) : Integer.Sparse.eval row12501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12501, Integer.Sparse.eval_collectBalanced, rawRowCheck12501]

theorem rawRowCheck12502 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form21 = rawRow12502 := by decide +kernel

theorem rowCheck12502 : row12502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12502 := by decide +kernel

theorem rowEval12502 (x : Key → ℝ) : Integer.Sparse.eval row12502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12502, Integer.Sparse.eval_collectBalanced, rawRowCheck12502]

theorem rawRowCheck12503 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form21 = rawRow12503 := by decide +kernel

theorem rowCheck12503 : row12503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12503 := by decide +kernel

theorem rowEval12503 (x : Key → ℝ) : Integer.Sparse.eval row12503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12503, Integer.Sparse.eval_collectBalanced, rawRowCheck12503]

theorem rawRowCheck12504 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form21 = rawRow12504 := by decide +kernel

theorem rowCheck12504 : row12504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12504 := by decide +kernel

theorem rowEval12504 (x : Key → ℝ) : Integer.Sparse.eval row12504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12504, Integer.Sparse.eval_collectBalanced, rawRowCheck12504]

theorem rawRowCheck12505 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form21 = rawRow12505 := by decide +kernel

theorem rowCheck12505 : row12505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12505 := by decide +kernel

theorem rowEval12505 (x : Key → ℝ) : Integer.Sparse.eval row12505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12505, Integer.Sparse.eval_collectBalanced, rawRowCheck12505]

theorem rawRowCheck12506 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form21 = rawRow12506 := by decide +kernel

theorem rowCheck12506 : row12506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12506 := by decide +kernel

theorem rowEval12506 (x : Key → ℝ) : Integer.Sparse.eval row12506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12506, Integer.Sparse.eval_collectBalanced, rawRowCheck12506]

theorem rawRowCheck12507 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form22 = rawRow12507 := by decide +kernel

theorem rowCheck12507 : row12507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12507 := by decide +kernel

theorem rowEval12507 (x : Key → ℝ) : Integer.Sparse.eval row12507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12507, Integer.Sparse.eval_collectBalanced, rawRowCheck12507]

theorem rawRowCheck12508 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form22 = rawRow12508 := by decide +kernel

theorem rowCheck12508 : row12508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12508 := by decide +kernel

theorem rowEval12508 (x : Key → ℝ) : Integer.Sparse.eval row12508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12508, Integer.Sparse.eval_collectBalanced, rawRowCheck12508]

theorem rawRowCheck12509 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form22 = rawRow12509 := by decide +kernel

theorem rowCheck12509 : row12509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12509 := by decide +kernel

theorem rowEval12509 (x : Key → ℝ) : Integer.Sparse.eval row12509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12509, Integer.Sparse.eval_collectBalanced, rawRowCheck12509]

theorem rawRowCheck12510 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form22 = rawRow12510 := by decide +kernel

theorem rowCheck12510 : row12510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12510 := by decide +kernel

theorem rowEval12510 (x : Key → ℝ) : Integer.Sparse.eval row12510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12510, Integer.Sparse.eval_collectBalanced, rawRowCheck12510]

theorem rawRowCheck12511 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form22 = rawRow12511 := by decide +kernel

theorem rowCheck12511 : row12511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12511 := by decide +kernel

theorem rowEval12511 (x : Key → ℝ) : Integer.Sparse.eval row12511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12511, Integer.Sparse.eval_collectBalanced, rawRowCheck12511]

theorem rawRowCheck12512 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form22 = rawRow12512 := by decide +kernel

theorem rowCheck12512 : row12512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12512 := by decide +kernel

theorem rowEval12512 (x : Key → ℝ) : Integer.Sparse.eval row12512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12512, Integer.Sparse.eval_collectBalanced, rawRowCheck12512]

theorem rawRowCheck12513 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form22 = rawRow12513 := by decide +kernel

theorem rowCheck12513 : row12513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12513 := by decide +kernel

theorem rowEval12513 (x : Key → ℝ) : Integer.Sparse.eval row12513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12513, Integer.Sparse.eval_collectBalanced, rawRowCheck12513]

theorem rawRowCheck12514 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form22 = rawRow12514 := by decide +kernel

theorem rowCheck12514 : row12514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12514 := by decide +kernel

theorem rowEval12514 (x : Key → ℝ) : Integer.Sparse.eval row12514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12514, Integer.Sparse.eval_collectBalanced, rawRowCheck12514]

theorem rawRowCheck12515 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form23 = rawRow12515 := by decide +kernel

theorem rowCheck12515 : row12515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12515 := by decide +kernel

theorem rowEval12515 (x : Key → ℝ) : Integer.Sparse.eval row12515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12515, Integer.Sparse.eval_collectBalanced, rawRowCheck12515]

theorem rawRowCheck12516 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form23 = rawRow12516 := by decide +kernel

theorem rowCheck12516 : row12516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12516 := by decide +kernel

theorem rowEval12516 (x : Key → ℝ) : Integer.Sparse.eval row12516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12516, Integer.Sparse.eval_collectBalanced, rawRowCheck12516]

theorem rawRowCheck12517 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form23 = rawRow12517 := by decide +kernel

theorem rowCheck12517 : row12517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12517 := by decide +kernel

theorem rowEval12517 (x : Key → ℝ) : Integer.Sparse.eval row12517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12517, Integer.Sparse.eval_collectBalanced, rawRowCheck12517]

theorem rawRowCheck12518 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form23 = rawRow12518 := by decide +kernel

theorem rowCheck12518 : row12518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12518 := by decide +kernel

theorem rowEval12518 (x : Key → ℝ) : Integer.Sparse.eval row12518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12518, Integer.Sparse.eval_collectBalanced, rawRowCheck12518]

theorem rawRowCheck12519 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form23 = rawRow12519 := by decide +kernel

theorem rowCheck12519 : row12519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12519 := by decide +kernel

theorem rowEval12519 (x : Key → ℝ) : Integer.Sparse.eval row12519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12519, Integer.Sparse.eval_collectBalanced, rawRowCheck12519]

theorem rawRowCheck12520 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form23 = rawRow12520 := by decide +kernel

theorem rowCheck12520 : row12520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12520 := by decide +kernel

theorem rowEval12520 (x : Key → ℝ) : Integer.Sparse.eval row12520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12520, Integer.Sparse.eval_collectBalanced, rawRowCheck12520]

theorem rawRowCheck12521 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form23 = rawRow12521 := by decide +kernel

theorem rowCheck12521 : row12521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12521 := by decide +kernel

theorem rowEval12521 (x : Key → ℝ) : Integer.Sparse.eval row12521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12521, Integer.Sparse.eval_collectBalanced, rawRowCheck12521]

theorem rawRowCheck12522 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form23 = rawRow12522 := by decide +kernel

theorem rowCheck12522 : row12522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12522 := by decide +kernel

theorem rowEval12522 (x : Key → ℝ) : Integer.Sparse.eval row12522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12522, Integer.Sparse.eval_collectBalanced, rawRowCheck12522]

theorem rawRowCheck12523 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form24 = rawRow12523 := by decide +kernel

theorem rowCheck12523 : row12523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12523 := by decide +kernel

theorem rowEval12523 (x : Key → ℝ) : Integer.Sparse.eval row12523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12523, Integer.Sparse.eval_collectBalanced, rawRowCheck12523]

theorem rawRowCheck12524 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form24 = rawRow12524 := by decide +kernel

theorem rowCheck12524 : row12524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12524 := by decide +kernel

theorem rowEval12524 (x : Key → ℝ) : Integer.Sparse.eval row12524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12524, Integer.Sparse.eval_collectBalanced, rawRowCheck12524]

theorem rawRowCheck12525 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form24 = rawRow12525 := by decide +kernel

theorem rowCheck12525 : row12525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12525 := by decide +kernel

theorem rowEval12525 (x : Key → ℝ) : Integer.Sparse.eval row12525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12525, Integer.Sparse.eval_collectBalanced, rawRowCheck12525]

theorem rawRowCheck12526 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form24 = rawRow12526 := by decide +kernel

theorem rowCheck12526 : row12526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12526 := by decide +kernel

theorem rowEval12526 (x : Key → ℝ) : Integer.Sparse.eval row12526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12526, Integer.Sparse.eval_collectBalanced, rawRowCheck12526]

theorem rawRowCheck12527 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form24 = rawRow12527 := by decide +kernel

theorem rowCheck12527 : row12527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12527 := by decide +kernel

theorem rowEval12527 (x : Key → ℝ) : Integer.Sparse.eval row12527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12527, Integer.Sparse.eval_collectBalanced, rawRowCheck12527]

theorem rawRowCheck12528 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form24 = rawRow12528 := by decide +kernel

theorem rowCheck12528 : row12528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12528 := by decide +kernel

theorem rowEval12528 (x : Key → ℝ) : Integer.Sparse.eval row12528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12528, Integer.Sparse.eval_collectBalanced, rawRowCheck12528]

theorem rawRowCheck12529 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form24 = rawRow12529 := by decide +kernel

theorem rowCheck12529 : row12529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12529 := by decide +kernel

theorem rowEval12529 (x : Key → ℝ) : Integer.Sparse.eval row12529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12529, Integer.Sparse.eval_collectBalanced, rawRowCheck12529]

theorem rawRowCheck12530 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form24 = rawRow12530 := by decide +kernel

theorem rowCheck12530 : row12530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12530 := by decide +kernel

theorem rowEval12530 (x : Key → ℝ) : Integer.Sparse.eval row12530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12530, Integer.Sparse.eval_collectBalanced, rawRowCheck12530]

theorem rawRowCheck12531 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form25 = rawRow12531 := by decide +kernel

theorem rowCheck12531 : row12531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12531 := by decide +kernel

theorem rowEval12531 (x : Key → ℝ) : Integer.Sparse.eval row12531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12531, Integer.Sparse.eval_collectBalanced, rawRowCheck12531]

theorem rawRowCheck12532 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form25 = rawRow12532 := by decide +kernel

theorem rowCheck12532 : row12532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12532 := by decide +kernel

theorem rowEval12532 (x : Key → ℝ) : Integer.Sparse.eval row12532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12532, Integer.Sparse.eval_collectBalanced, rawRowCheck12532]

theorem rawRowCheck12533 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form25 = rawRow12533 := by decide +kernel

theorem rowCheck12533 : row12533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12533 := by decide +kernel

theorem rowEval12533 (x : Key → ℝ) : Integer.Sparse.eval row12533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12533, Integer.Sparse.eval_collectBalanced, rawRowCheck12533]

theorem rawRowCheck12534 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form25 = rawRow12534 := by decide +kernel

theorem rowCheck12534 : row12534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12534 := by decide +kernel

theorem rowEval12534 (x : Key → ℝ) : Integer.Sparse.eval row12534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12534, Integer.Sparse.eval_collectBalanced, rawRowCheck12534]

theorem rawRowCheck12535 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form25 = rawRow12535 := by decide +kernel

theorem rowCheck12535 : row12535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12535 := by decide +kernel

theorem rowEval12535 (x : Key → ℝ) : Integer.Sparse.eval row12535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck12535, Integer.Sparse.eval_collectBalanced, rawRowCheck12535]

theorem rawRowCheck12536 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form25 = rawRow12536 := by decide +kernel

theorem rowCheck12536 : row12536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12536 := by decide +kernel

theorem rowEval12536 (x : Key → ℝ) : Integer.Sparse.eval row12536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12536, Integer.Sparse.eval_collectBalanced, rawRowCheck12536]

theorem rawRowCheck12537 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form25 = rawRow12537 := by decide +kernel

theorem rowCheck12537 : row12537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12537 := by decide +kernel

theorem rowEval12537 (x : Key → ℝ) : Integer.Sparse.eval row12537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12537, Integer.Sparse.eval_collectBalanced, rawRowCheck12537]

theorem rawRowCheck12538 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form25 = rawRow12538 := by decide +kernel

theorem rowCheck12538 : row12538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12538 := by decide +kernel

theorem rowEval12538 (x : Key → ℝ) : Integer.Sparse.eval row12538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12538, Integer.Sparse.eval_collectBalanced, rawRowCheck12538]

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

theorem entryCheck25_1 : entry25_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_1 k)) := by decide +kernel

theorem rowsSound25_1 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12339 x
  · exact rowEval12340 x
  · exact rowEval12341 x
  · exact rowEval12342 x
  · exact rowEval12343 x
  · exact rowEval12344 x
  · exact rowEval12345 x
  · exact rowEval12346 x

theorem entryEval25_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_1 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck25_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_1]

theorem entryCheck25_2 : entry25_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_2 k)) := by decide +kernel

theorem rowsSound25_2 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12347 x
  · exact rowEval12348 x
  · exact rowEval12349 x
  · exact rowEval12350 x
  · exact rowEval12351 x
  · exact rowEval12352 x
  · exact rowEval12353 x
  · exact rowEval12354 x

theorem entryEval25_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_2 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck25_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_2]

theorem entryCheck25_3 : entry25_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_3 k)) := by decide +kernel

theorem rowsSound25_3 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12355 x
  · exact rowEval12356 x
  · exact rowEval12357 x
  · exact rowEval12358 x
  · exact rowEval12359 x
  · exact rowEval12360 x
  · exact rowEval12361 x
  · exact rowEval12362 x

theorem entryEval25_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_3 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck25_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_3]

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

theorem entryCheck25_5 : entry25_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_5 k)) := by decide +kernel

theorem rowsSound25_5 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval12371 x
  · exact rowEval12372 x
  · exact rowEval12373 x
  · exact rowEval12374 x
  · exact rowEval12375 x
  · exact rowEval12376 x
  · exact rowEval12377 x
  · exact rowEval12378 x

theorem entryEval25_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_5 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck25_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_5]

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

theorem entryCheck25_7 : entry25_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_7 k)) := by decide +kernel

theorem rowsSound25_7 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval12387 x
  · exact rowEval12388 x
  · exact rowEval12389 x
  · exact rowEval12390 x
  · exact rowEval12391 x
  · exact rowEval12392 x
  · exact rowEval12393 x
  · exact rowEval12394 x

theorem entryEval25_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_7 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck25_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_7]

theorem entryCheck25_8 : entry25_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_8 k)) := by decide +kernel

theorem rowsSound25_8 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval12395 x
  · exact rowEval12396 x
  · exact rowEval12397 x
  · exact rowEval12398 x
  · exact rowEval12399 x
  · exact rowEval12400 x
  · exact rowEval12401 x
  · exact rowEval12402 x

theorem entryEval25_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_8 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck25_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_8]

theorem entryCheck25_9 : entry25_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_9 k)) := by decide +kernel

theorem rowsSound25_9 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval12403 x
  · exact rowEval12404 x
  · exact rowEval12405 x
  · exact rowEval12406 x
  · exact rowEval12407 x
  · exact rowEval12408 x
  · exact rowEval12409 x
  · exact rowEval12410 x

theorem entryEval25_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_9 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck25_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_9]

theorem entryCheck25_10 : entry25_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_10 k)) := by decide +kernel

theorem rowsSound25_10 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval12411 x
  · exact rowEval12412 x
  · exact rowEval12413 x
  · exact rowEval12414 x
  · exact rowEval12415 x
  · exact rowEval12416 x
  · exact rowEval12417 x
  · exact rowEval12418 x

theorem entryEval25_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_10 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck25_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_10]

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

theorem entryCheck25_12 : entry25_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_12 k)) := by decide +kernel

theorem rowsSound25_12 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval12427 x
  · exact rowEval12428 x
  · exact rowEval12429 x
  · exact rowEval12430 x
  · exact rowEval12431 x
  · exact rowEval12432 x
  · exact rowEval12433 x
  · exact rowEval12434 x

theorem entryEval25_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_12 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck25_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_12]

theorem entryCheck25_13 : entry25_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_13 k)) := by decide +kernel

theorem rowsSound25_13 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12435 x
  · exact rowEval12436 x
  · exact rowEval12437 x
  · exact rowEval12438 x
  · exact rowEval12439 x
  · exact rowEval12440 x
  · exact rowEval12441 x
  · exact rowEval12442 x

theorem entryEval25_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_13 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck25_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_13]

theorem entryCheck25_14 : entry25_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_14 k)) := by decide +kernel

theorem rowsSound25_14 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12443 x
  · exact rowEval12444 x
  · exact rowEval12445 x
  · exact rowEval12446 x
  · exact rowEval12447 x
  · exact rowEval12448 x
  · exact rowEval12449 x
  · exact rowEval12450 x

theorem entryEval25_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_14 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck25_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_14]

theorem entryCheck25_15 : entry25_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_15 k)) := by decide +kernel

theorem rowsSound25_15 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12451 x
  · exact rowEval12452 x
  · exact rowEval12453 x
  · exact rowEval12454 x
  · exact rowEval12455 x
  · exact rowEval12456 x
  · exact rowEval12457 x
  · exact rowEval12458 x

theorem entryEval25_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_15 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck25_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_15]

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

theorem entryCheck25_17 : entry25_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_17 k)) := by decide +kernel

theorem rowsSound25_17 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12467 x
  · exact rowEval12468 x
  · exact rowEval12469 x
  · exact rowEval12470 x
  · exact rowEval12471 x
  · exact rowEval12472 x
  · exact rowEval12473 x
  · exact rowEval12474 x

theorem entryEval25_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_17 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck25_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_17]

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

theorem entryCheck25_19 : entry25_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_19 k)) := by decide +kernel

theorem rowsSound25_19 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12483 x
  · exact rowEval12484 x
  · exact rowEval12485 x
  · exact rowEval12486 x
  · exact rowEval12487 x
  · exact rowEval12488 x
  · exact rowEval12489 x
  · exact rowEval12490 x

theorem entryEval25_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_19 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck25_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_19]

theorem entryCheck25_20 : entry25_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_20 k)) := by decide +kernel

theorem rowsSound25_20 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval12491 x
  · exact rowEval12492 x
  · exact rowEval12493 x
  · exact rowEval12494 x
  · exact rowEval12495 x
  · exact rowEval12496 x
  · exact rowEval12497 x
  · exact rowEval12498 x

theorem entryEval25_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_20 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck25_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_20]

theorem entryCheck25_21 : entry25_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_21 k)) := by decide +kernel

theorem rowsSound25_21 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval12499 x
  · exact rowEval12500 x
  · exact rowEval12501 x
  · exact rowEval12502 x
  · exact rowEval12503 x
  · exact rowEval12504 x
  · exact rowEval12505 x
  · exact rowEval12506 x

theorem entryEval25_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_21 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck25_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_21]

theorem entryCheck25_22 : entry25_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_22 k)) := by decide +kernel

theorem rowsSound25_22 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval12507 x
  · exact rowEval12508 x
  · exact rowEval12509 x
  · exact rowEval12510 x
  · exact rowEval12511 x
  · exact rowEval12512 x
  · exact rowEval12513 x
  · exact rowEval12514 x

theorem entryEval25_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_22 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck25_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_22]

theorem entryCheck25_23 : entry25_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_23 k)) := by decide +kernel

theorem rowsSound25_23 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval12515 x
  · exact rowEval12516 x
  · exact rowEval12517 x
  · exact rowEval12518 x
  · exact rowEval12519 x
  · exact rowEval12520 x
  · exact rowEval12521 x
  · exact rowEval12522 x

theorem entryEval25_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_23 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck25_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_23]

theorem entryCheck25_24 : entry25_24 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_24 k)) := by decide +kernel

theorem rowsSound25_24 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_24 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form24) x := by
  fin_cases k
  · exact rowEval12523 x
  · exact rowEval12524 x
  · exact rowEval12525 x
  · exact rowEval12526 x
  · exact rowEval12527 x
  · exact rowEval12528 x
  · exact rowEval12529 x
  · exact rowEval12530 x

theorem entryEval25_24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_24 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form24 B := by
  rw [entryCheck25_24, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form24 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_24]

theorem entryCheck25_25 : entry25_25 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_25 k)) := by decide +kernel

theorem rowsSound25_25 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_25 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form25) x := by
  fin_cases k
  · exact rowEval12531 x
  · exact rowEval12532 x
  · exact rowEval12533 x
  · exact rowEval12534 x
  · exact rowEval12535 x
  · exact rowEval12536 x
  · exact rowEval12537 x
  · exact rowEval12538 x

theorem entryEval25_25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_25 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form25 B := by
  rw [entryCheck25_25, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form25 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_25]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13139 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form25 = rawRow13139 := by decide +kernel

theorem rowCheck13139 : row13139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13139 := by decide +kernel

theorem rowEval13139 (x : Key → ℝ) : Integer.Sparse.eval row13139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13139, Integer.Sparse.eval_collectBalanced, rawRowCheck13139]

theorem rawRowCheck13140 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form25 = rawRow13140 := by decide +kernel

theorem rowCheck13140 : row13140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13140 := by decide +kernel

theorem rowEval13140 (x : Key → ℝ) : Integer.Sparse.eval row13140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13140, Integer.Sparse.eval_collectBalanced, rawRowCheck13140]

theorem rawRowCheck13141 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form25 = rawRow13141 := by decide +kernel

theorem rowCheck13141 : row13141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13141 := by decide +kernel

theorem rowEval13141 (x : Key → ℝ) : Integer.Sparse.eval row13141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13141, Integer.Sparse.eval_collectBalanced, rawRowCheck13141]

theorem rawRowCheck13142 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form25 = rawRow13142 := by decide +kernel

theorem rowCheck13142 : row13142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13142 := by decide +kernel

theorem rowEval13142 (x : Key → ℝ) : Integer.Sparse.eval row13142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13142, Integer.Sparse.eval_collectBalanced, rawRowCheck13142]

theorem rawRowCheck13143 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form25 = rawRow13143 := by decide +kernel

theorem rowCheck13143 : row13143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13143 := by decide +kernel

theorem rowEval13143 (x : Key → ℝ) : Integer.Sparse.eval row13143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13143, Integer.Sparse.eval_collectBalanced, rawRowCheck13143]

theorem rawRowCheck13144 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form25 = rawRow13144 := by decide +kernel

theorem rowCheck13144 : row13144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13144 := by decide +kernel

theorem rowEval13144 (x : Key → ℝ) : Integer.Sparse.eval row13144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13144, Integer.Sparse.eval_collectBalanced, rawRowCheck13144]

theorem rawRowCheck13145 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form25 = rawRow13145 := by decide +kernel

theorem rowCheck13145 : row13145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13145 := by decide +kernel

theorem rowEval13145 (x : Key → ℝ) : Integer.Sparse.eval row13145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13145, Integer.Sparse.eval_collectBalanced, rawRowCheck13145]

theorem rawRowCheck13146 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form25 = rawRow13146 := by decide +kernel

theorem rowCheck13146 : row13146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13146 := by decide +kernel

theorem rowEval13146 (x : Key → ℝ) : Integer.Sparse.eval row13146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13146, Integer.Sparse.eval_collectBalanced, rawRowCheck13146]

theorem rawRowCheck13147 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form25 = rawRow13147 := by decide +kernel

theorem rowCheck13147 : row13147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13147 := by decide +kernel

theorem rowEval13147 (x : Key → ℝ) : Integer.Sparse.eval row13147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13147, Integer.Sparse.eval_collectBalanced, rawRowCheck13147]

theorem rawRowCheck13148 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form25 = rawRow13148 := by decide +kernel

theorem rowCheck13148 : row13148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13148 := by decide +kernel

theorem rowEval13148 (x : Key → ℝ) : Integer.Sparse.eval row13148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13148, Integer.Sparse.eval_collectBalanced, rawRowCheck13148]

theorem rawRowCheck13149 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form25 = rawRow13149 := by decide +kernel

theorem rowCheck13149 : row13149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13149 := by decide +kernel

theorem rowEval13149 (x : Key → ℝ) : Integer.Sparse.eval row13149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13149, Integer.Sparse.eval_collectBalanced, rawRowCheck13149]

theorem rawRowCheck13150 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form25 = rawRow13150 := by decide +kernel

theorem rowCheck13150 : row13150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13150 := by decide +kernel

theorem rowEval13150 (x : Key → ℝ) : Integer.Sparse.eval row13150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13150, Integer.Sparse.eval_collectBalanced, rawRowCheck13150]

theorem rawRowCheck13151 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form25 = rawRow13151 := by decide +kernel

theorem rowCheck13151 : row13151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13151 := by decide +kernel

theorem rowEval13151 (x : Key → ℝ) : Integer.Sparse.eval row13151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13151, Integer.Sparse.eval_collectBalanced, rawRowCheck13151]

theorem rawRowCheck13152 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form25 = rawRow13152 := by decide +kernel

theorem rowCheck13152 : row13152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13152 := by decide +kernel

theorem rowEval13152 (x : Key → ℝ) : Integer.Sparse.eval row13152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13152, Integer.Sparse.eval_collectBalanced, rawRowCheck13152]

theorem rawRowCheck13153 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form25 = rawRow13153 := by decide +kernel

theorem rowCheck13153 : row13153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13153 := by decide +kernel

theorem rowEval13153 (x : Key → ℝ) : Integer.Sparse.eval row13153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13153, Integer.Sparse.eval_collectBalanced, rawRowCheck13153]

theorem rawRowCheck13154 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form25 = rawRow13154 := by decide +kernel

theorem rowCheck13154 : row13154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13154 := by decide +kernel

theorem rowEval13154 (x : Key → ℝ) : Integer.Sparse.eval row13154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13154, Integer.Sparse.eval_collectBalanced, rawRowCheck13154]

theorem rawRowCheck13155 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form25 = rawRow13155 := by decide +kernel

theorem rowCheck13155 : row13155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13155 := by decide +kernel

theorem rowEval13155 (x : Key → ℝ) : Integer.Sparse.eval row13155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13155, Integer.Sparse.eval_collectBalanced, rawRowCheck13155]

theorem rawRowCheck13156 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form25 = rawRow13156 := by decide +kernel

theorem rowCheck13156 : row13156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13156 := by decide +kernel

theorem rowEval13156 (x : Key → ℝ) : Integer.Sparse.eval row13156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13156, Integer.Sparse.eval_collectBalanced, rawRowCheck13156]

theorem rawRowCheck13157 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form25 = rawRow13157 := by decide +kernel

theorem rowCheck13157 : row13157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13157 := by decide +kernel

theorem rowEval13157 (x : Key → ℝ) : Integer.Sparse.eval row13157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13157, Integer.Sparse.eval_collectBalanced, rawRowCheck13157]

theorem rawRowCheck13158 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form25 = rawRow13158 := by decide +kernel

theorem rowCheck13158 : row13158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13158 := by decide +kernel

theorem rowEval13158 (x : Key → ℝ) : Integer.Sparse.eval row13158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13158, Integer.Sparse.eval_collectBalanced, rawRowCheck13158]

theorem rawRowCheck13159 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form25 = rawRow13159 := by decide +kernel

theorem rowCheck13159 : row13159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13159 := by decide +kernel

theorem rowEval13159 (x : Key → ℝ) : Integer.Sparse.eval row13159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13159, Integer.Sparse.eval_collectBalanced, rawRowCheck13159]

theorem rawRowCheck13160 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form25 = rawRow13160 := by decide +kernel

theorem rowCheck13160 : row13160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13160 := by decide +kernel

theorem rowEval13160 (x : Key → ℝ) : Integer.Sparse.eval row13160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13160, Integer.Sparse.eval_collectBalanced, rawRowCheck13160]

theorem rawRowCheck13161 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form25 = rawRow13161 := by decide +kernel

theorem rowCheck13161 : row13161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13161 := by decide +kernel

theorem rowEval13161 (x : Key → ℝ) : Integer.Sparse.eval row13161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13161, Integer.Sparse.eval_collectBalanced, rawRowCheck13161]

theorem rawRowCheck13162 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form25 = rawRow13162 := by decide +kernel

theorem rowCheck13162 : row13162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13162 := by decide +kernel

theorem rowEval13162 (x : Key → ℝ) : Integer.Sparse.eval row13162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13162, Integer.Sparse.eval_collectBalanced, rawRowCheck13162]

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

theorem entryCheck26_25 : entry26_25 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_25 k)) := by decide +kernel

theorem rowsSound26_25 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_25 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form25) x := by
  fin_cases k
  · exact rowEval13139 x
  · exact rowEval13140 x
  · exact rowEval13141 x
  · exact rowEval13142 x
  · exact rowEval13143 x
  · exact rowEval13144 x
  · exact rowEval13145 x
  · exact rowEval13146 x
  · exact rowEval13147 x
  · exact rowEval13148 x
  · exact rowEval13149 x
  · exact rowEval13150 x
  · exact rowEval13151 x
  · exact rowEval13152 x
  · exact rowEval13153 x
  · exact rowEval13154 x
  · exact rowEval13155 x
  · exact rowEval13156 x
  · exact rowEval13157 x
  · exact rowEval13158 x
  · exact rowEval13159 x
  · exact rowEval13160 x
  · exact rowEval13161 x
  · exact rowEval13162 x

theorem entryEval26_25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_25 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form25 B := by
  rw [entryCheck26_25, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form25 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_25]

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

theorem entryEvalRow25_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 25 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 25).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval25_0 B hB
  · exact entryEval25_1 B hB
  · exact entryEval25_2 B hB
  · exact entryEval25_3 B hB
  · exact entryEval25_4 B hB
  · exact entryEval25_5 B hB
  · exact entryEval25_6 B hB
  · exact entryEval25_7 B hB
  · exact entryEval25_8 B hB
  · exact entryEval25_9 B hB
  · exact entryEval25_10 B hB
  · exact entryEval25_11 B hB
  · exact entryEval25_12 B hB
  · exact entryEval25_13 B hB
  · exact entryEval25_14 B hB
  · exact entryEval25_15 B hB
  · exact entryEval25_16 B hB
  · exact entryEval25_17 B hB
  · exact entryEval25_18 B hB
  · exact entryEval25_19 B hB
  · exact entryEval25_20 B hB
  · exact entryEval25_21 B hB
  · exact entryEval25_22 B hB
  · exact entryEval25_23 B hB
  · exact entryEval25_24 B hB
  · exact entryEval25_25 B hB
  · exact (entryEval26_25 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e_oai
