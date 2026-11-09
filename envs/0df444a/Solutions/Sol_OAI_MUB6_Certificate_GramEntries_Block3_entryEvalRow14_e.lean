-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:12:49.509789+00:00
-- url     : https://prove2.me/submissions/875ec551-65d0-4286-a45e-ebe08f03672d

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

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

theorem rawRowCheck7398 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7398 := by decide +kernel

theorem rowCheck7398 : row7398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7398 := by decide +kernel

theorem rowEval7398 (x : Key → ℝ) : Integer.Sparse.eval row7398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7398, Integer.Sparse.eval_collectBalanced, rawRowCheck7398]

theorem rawRowCheck7399 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7399 := by decide +kernel

theorem rowCheck7399 : row7399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7399 := by decide +kernel

theorem rowEval7399 (x : Key → ℝ) : Integer.Sparse.eval row7399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7399, Integer.Sparse.eval_collectBalanced, rawRowCheck7399]

theorem rawRowCheck7400 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7400 := by decide +kernel

theorem rowCheck7400 : row7400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7400 := by decide +kernel

theorem rowEval7400 (x : Key → ℝ) : Integer.Sparse.eval row7400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7400, Integer.Sparse.eval_collectBalanced, rawRowCheck7400]

theorem rawRowCheck7401 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7401 := by decide +kernel

theorem rowCheck7401 : row7401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7401 := by decide +kernel

theorem rowEval7401 (x : Key → ℝ) : Integer.Sparse.eval row7401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7401, Integer.Sparse.eval_collectBalanced, rawRowCheck7401]

theorem rawRowCheck7414 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7414 := by decide +kernel

theorem rowCheck7414 : row7414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7414 := by decide +kernel

theorem rowEval7414 (x : Key → ℝ) : Integer.Sparse.eval row7414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7414, Integer.Sparse.eval_collectBalanced, rawRowCheck7414]

theorem rawRowCheck7415 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7415 := by decide +kernel

theorem rowCheck7415 : row7415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7415 := by decide +kernel

theorem rowEval7415 (x : Key → ℝ) : Integer.Sparse.eval row7415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7415, Integer.Sparse.eval_collectBalanced, rawRowCheck7415]

theorem rawRowCheck7416 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7416 := by decide +kernel

theorem rowCheck7416 : row7416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7416 := by decide +kernel

theorem rowEval7416 (x : Key → ℝ) : Integer.Sparse.eval row7416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7416, Integer.Sparse.eval_collectBalanced, rawRowCheck7416]

theorem rawRowCheck7417 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7417 := by decide +kernel

theorem rowCheck7417 : row7417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7417 := by decide +kernel

theorem rowEval7417 (x : Key → ℝ) : Integer.Sparse.eval row7417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7417, Integer.Sparse.eval_collectBalanced, rawRowCheck7417]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck9069 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow9069 := by decide +kernel

theorem rowCheck9069 : row9069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9069 := by decide +kernel

theorem rowEval9069 (x : Key → ℝ) : Integer.Sparse.eval row9069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9069, Integer.Sparse.eval_collectBalanced, rawRowCheck9069]

theorem rawRowCheck9070 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9070 := by decide +kernel

theorem rowCheck9070 : row9070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9070 := by decide +kernel

theorem rowEval9070 (x : Key → ℝ) : Integer.Sparse.eval row9070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9070, Integer.Sparse.eval_collectBalanced, rawRowCheck9070]

theorem rawRowCheck9071 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9071 := by decide +kernel

theorem rowCheck9071 : row9071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9071 := by decide +kernel

theorem rowEval9071 (x : Key → ℝ) : Integer.Sparse.eval row9071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9071, Integer.Sparse.eval_collectBalanced, rawRowCheck9071]

theorem rawRowCheck9072 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9072 := by decide +kernel

theorem rowCheck9072 : row9072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9072 := by decide +kernel

theorem rowEval9072 (x : Key → ℝ) : Integer.Sparse.eval row9072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9072, Integer.Sparse.eval_collectBalanced, rawRowCheck9072]

theorem rawRowCheck9073 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow9073 := by decide +kernel

theorem rowCheck9073 : row9073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9073 := by decide +kernel

theorem rowEval9073 (x : Key → ℝ) : Integer.Sparse.eval row9073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9073, Integer.Sparse.eval_collectBalanced, rawRowCheck9073]

theorem rawRowCheck9074 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow9074 := by decide +kernel

theorem rowCheck9074 : row9074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9074 := by decide +kernel

theorem rowEval9074 (x : Key → ℝ) : Integer.Sparse.eval row9074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9074, Integer.Sparse.eval_collectBalanced, rawRowCheck9074]

theorem rawRowCheck9075 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow9075 := by decide +kernel

theorem rowCheck9075 : row9075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9075 := by decide +kernel

theorem rowEval9075 (x : Key → ℝ) : Integer.Sparse.eval row9075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9075, Integer.Sparse.eval_collectBalanced, rawRowCheck9075]

theorem rawRowCheck9076 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow9076 := by decide +kernel

theorem rowCheck9076 : row9076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9076 := by decide +kernel

theorem rowEval9076 (x : Key → ℝ) : Integer.Sparse.eval row9076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9076, Integer.Sparse.eval_collectBalanced, rawRowCheck9076]

theorem rawRowCheck9077 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow9077 := by decide +kernel

theorem rowCheck9077 : row9077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9077 := by decide +kernel

theorem rowEval9077 (x : Key → ℝ) : Integer.Sparse.eval row9077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9077, Integer.Sparse.eval_collectBalanced, rawRowCheck9077]

theorem rawRowCheck9078 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow9078 := by decide +kernel

theorem rowCheck9078 : row9078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9078 := by decide +kernel

theorem rowEval9078 (x : Key → ℝ) : Integer.Sparse.eval row9078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9078, Integer.Sparse.eval_collectBalanced, rawRowCheck9078]

theorem rawRowCheck9079 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow9079 := by decide +kernel

theorem rowCheck9079 : row9079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9079 := by decide +kernel

theorem rowEval9079 (x : Key → ℝ) : Integer.Sparse.eval row9079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9079, Integer.Sparse.eval_collectBalanced, rawRowCheck9079]

theorem rawRowCheck9080 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9080 := by decide +kernel

theorem rowCheck9080 : row9080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9080 := by decide +kernel

theorem rowEval9080 (x : Key → ℝ) : Integer.Sparse.eval row9080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9080, Integer.Sparse.eval_collectBalanced, rawRowCheck9080]

theorem rawRowCheck9081 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9081 := by decide +kernel

theorem rowCheck9081 : row9081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9081 := by decide +kernel

theorem rowEval9081 (x : Key → ℝ) : Integer.Sparse.eval row9081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9081, Integer.Sparse.eval_collectBalanced, rawRowCheck9081]

theorem rawRowCheck9082 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow9082 := by decide +kernel

theorem rowCheck9082 : row9082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9082 := by decide +kernel

theorem rowEval9082 (x : Key → ℝ) : Integer.Sparse.eval row9082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9082, Integer.Sparse.eval_collectBalanced, rawRowCheck9082]

theorem rawRowCheck9083 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow9083 := by decide +kernel

theorem rowCheck9083 : row9083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9083 := by decide +kernel

theorem rowEval9083 (x : Key → ℝ) : Integer.Sparse.eval row9083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9083, Integer.Sparse.eval_collectBalanced, rawRowCheck9083]

theorem rawRowCheck9084 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow9084 := by decide +kernel

theorem rowCheck9084 : row9084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9084 := by decide +kernel

theorem rowEval9084 (x : Key → ℝ) : Integer.Sparse.eval row9084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9084, Integer.Sparse.eval_collectBalanced, rawRowCheck9084]

theorem rawRowCheck9085 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow9085 := by decide +kernel

theorem rowCheck9085 : row9085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9085 := by decide +kernel

theorem rowEval9085 (x : Key → ℝ) : Integer.Sparse.eval row9085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9085, Integer.Sparse.eval_collectBalanced, rawRowCheck9085]

theorem rawRowCheck9086 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow9086 := by decide +kernel

theorem rowCheck9086 : row9086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9086 := by decide +kernel

theorem rowEval9086 (x : Key → ℝ) : Integer.Sparse.eval row9086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9086, Integer.Sparse.eval_collectBalanced, rawRowCheck9086]

theorem rawRowCheck9087 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow9087 := by decide +kernel

theorem rowCheck9087 : row9087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9087 := by decide +kernel

theorem rowEval9087 (x : Key → ℝ) : Integer.Sparse.eval row9087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9087, Integer.Sparse.eval_collectBalanced, rawRowCheck9087]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck9088 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9088 := by decide +kernel

theorem rowCheck9088 : row9088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9088 := by decide +kernel

theorem rowEval9088 (x : Key → ℝ) : Integer.Sparse.eval row9088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9088, Integer.Sparse.eval_collectBalanced, rawRowCheck9088]

theorem rawRowCheck9089 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow9089 := by decide +kernel

theorem rowCheck9089 : row9089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9089 := by decide +kernel

theorem rowEval9089 (x : Key → ℝ) : Integer.Sparse.eval row9089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9089, Integer.Sparse.eval_collectBalanced, rawRowCheck9089]

theorem rawRowCheck9090 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow9090 := by decide +kernel

theorem rowCheck9090 : row9090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9090 := by decide +kernel

theorem rowEval9090 (x : Key → ℝ) : Integer.Sparse.eval row9090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9090, Integer.Sparse.eval_collectBalanced, rawRowCheck9090]

theorem rawRowCheck9091 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow9091 := by decide +kernel

theorem rowCheck9091 : row9091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9091 := by decide +kernel

theorem rowEval9091 (x : Key → ℝ) : Integer.Sparse.eval row9091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9091, Integer.Sparse.eval_collectBalanced, rawRowCheck9091]

theorem rawRowCheck9092 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow9092 := by decide +kernel

theorem rowCheck9092 : row9092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9092 := by decide +kernel

theorem rowEval9092 (x : Key → ℝ) : Integer.Sparse.eval row9092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9092, Integer.Sparse.eval_collectBalanced, rawRowCheck9092]

theorem rawRowCheck9093 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form5 = rawRow9093 := by decide +kernel

theorem rowCheck9093 : row9093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9093 := by decide +kernel

theorem rowEval9093 (x : Key → ℝ) : Integer.Sparse.eval row9093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9093, Integer.Sparse.eval_collectBalanced, rawRowCheck9093]

theorem rawRowCheck9094 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form5 = rawRow9094 := by decide +kernel

theorem rowCheck9094 : row9094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9094 := by decide +kernel

theorem rowEval9094 (x : Key → ℝ) : Integer.Sparse.eval row9094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9094, Integer.Sparse.eval_collectBalanced, rawRowCheck9094]

theorem rawRowCheck9095 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form5 = rawRow9095 := by decide +kernel

theorem rowCheck9095 : row9095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9095 := by decide +kernel

theorem rowEval9095 (x : Key → ℝ) : Integer.Sparse.eval row9095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9095, Integer.Sparse.eval_collectBalanced, rawRowCheck9095]

theorem rawRowCheck9096 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow9096 := by decide +kernel

theorem rowCheck9096 : row9096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9096 := by decide +kernel

theorem rowEval9096 (x : Key → ℝ) : Integer.Sparse.eval row9096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9096, Integer.Sparse.eval_collectBalanced, rawRowCheck9096]

theorem rawRowCheck9097 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form5 = rawRow9097 := by decide +kernel

theorem rowCheck9097 : row9097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9097 := by decide +kernel

theorem rowEval9097 (x : Key → ℝ) : Integer.Sparse.eval row9097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9097, Integer.Sparse.eval_collectBalanced, rawRowCheck9097]

theorem rawRowCheck9098 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form5 = rawRow9098 := by decide +kernel

theorem rowCheck9098 : row9098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9098 := by decide +kernel

theorem rowEval9098 (x : Key → ℝ) : Integer.Sparse.eval row9098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9098, Integer.Sparse.eval_collectBalanced, rawRowCheck9098]

theorem rawRowCheck9099 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form5 = rawRow9099 := by decide +kernel

theorem rowCheck9099 : row9099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9099 := by decide +kernel

theorem rowEval9099 (x : Key → ℝ) : Integer.Sparse.eval row9099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9099, Integer.Sparse.eval_collectBalanced, rawRowCheck9099]

theorem rawRowCheck9100 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form5 = rawRow9100 := by decide +kernel

theorem rowCheck9100 : row9100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9100 := by decide +kernel

theorem rowEval9100 (x : Key → ℝ) : Integer.Sparse.eval row9100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck9100, Integer.Sparse.eval_collectBalanced, rawRowCheck9100]

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

theorem rawRowCheck9109 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow9109 := by decide +kernel

theorem rowCheck9109 : row9109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9109 := by decide +kernel

theorem rowEval9109 (x : Key → ℝ) : Integer.Sparse.eval row9109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9109, Integer.Sparse.eval_collectBalanced, rawRowCheck9109]

theorem rawRowCheck9110 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow9110 := by decide +kernel

theorem rowCheck9110 : row9110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9110 := by decide +kernel

theorem rowEval9110 (x : Key → ℝ) : Integer.Sparse.eval row9110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9110, Integer.Sparse.eval_collectBalanced, rawRowCheck9110]

theorem rawRowCheck9111 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow9111 := by decide +kernel

theorem rowCheck9111 : row9111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9111 := by decide +kernel

theorem rowEval9111 (x : Key → ℝ) : Integer.Sparse.eval row9111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9111, Integer.Sparse.eval_collectBalanced, rawRowCheck9111]

theorem rawRowCheck9112 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9112 := by decide +kernel

theorem rowCheck9112 : row9112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9112 := by decide +kernel

theorem rowEval9112 (x : Key → ℝ) : Integer.Sparse.eval row9112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9112, Integer.Sparse.eval_collectBalanced, rawRowCheck9112]

theorem rawRowCheck9113 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7 = rawRow9113 := by decide +kernel

theorem rowCheck9113 : row9113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9113 := by decide +kernel

theorem rowEval9113 (x : Key → ℝ) : Integer.Sparse.eval row9113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9113, Integer.Sparse.eval_collectBalanced, rawRowCheck9113]

theorem rawRowCheck9114 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7 = rawRow9114 := by decide +kernel

theorem rowCheck9114 : row9114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9114 := by decide +kernel

theorem rowEval9114 (x : Key → ℝ) : Integer.Sparse.eval row9114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9114, Integer.Sparse.eval_collectBalanced, rawRowCheck9114]

theorem rawRowCheck9115 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7 = rawRow9115 := by decide +kernel

theorem rowCheck9115 : row9115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9115 := by decide +kernel

theorem rowEval9115 (x : Key → ℝ) : Integer.Sparse.eval row9115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9115, Integer.Sparse.eval_collectBalanced, rawRowCheck9115]

theorem rawRowCheck9116 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7 = rawRow9116 := by decide +kernel

theorem rowCheck9116 : row9116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9116 := by decide +kernel

theorem rowEval9116 (x : Key → ℝ) : Integer.Sparse.eval row9116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9116, Integer.Sparse.eval_collectBalanced, rawRowCheck9116]

theorem rawRowCheck9117 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form8 = rawRow9117 := by decide +kernel

theorem rowCheck9117 : row9117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9117 := by decide +kernel

theorem rowEval9117 (x : Key → ℝ) : Integer.Sparse.eval row9117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9117, Integer.Sparse.eval_collectBalanced, rawRowCheck9117]

theorem rawRowCheck9118 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form8 = rawRow9118 := by decide +kernel

theorem rowCheck9118 : row9118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9118 := by decide +kernel

theorem rowEval9118 (x : Key → ℝ) : Integer.Sparse.eval row9118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9118, Integer.Sparse.eval_collectBalanced, rawRowCheck9118]

theorem rawRowCheck9119 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form8 = rawRow9119 := by decide +kernel

theorem rowCheck9119 : row9119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9119 := by decide +kernel

theorem rowEval9119 (x : Key → ℝ) : Integer.Sparse.eval row9119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9119, Integer.Sparse.eval_collectBalanced, rawRowCheck9119]

theorem rawRowCheck9120 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow9120 := by decide +kernel

theorem rowCheck9120 : row9120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9120 := by decide +kernel

theorem rowEval9120 (x : Key → ℝ) : Integer.Sparse.eval row9120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9120, Integer.Sparse.eval_collectBalanced, rawRowCheck9120]

theorem rawRowCheck9121 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form8 = rawRow9121 := by decide +kernel

theorem rowCheck9121 : row9121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9121 := by decide +kernel

theorem rowEval9121 (x : Key → ℝ) : Integer.Sparse.eval row9121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9121, Integer.Sparse.eval_collectBalanced, rawRowCheck9121]

theorem rawRowCheck9122 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form8 = rawRow9122 := by decide +kernel

theorem rowCheck9122 : row9122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9122 := by decide +kernel

theorem rowEval9122 (x : Key → ℝ) : Integer.Sparse.eval row9122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9122, Integer.Sparse.eval_collectBalanced, rawRowCheck9122]

theorem rawRowCheck9123 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form8 = rawRow9123 := by decide +kernel

theorem rowCheck9123 : row9123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9123 := by decide +kernel

theorem rowEval9123 (x : Key → ℝ) : Integer.Sparse.eval row9123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9123, Integer.Sparse.eval_collectBalanced, rawRowCheck9123]

theorem rawRowCheck9124 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form8 = rawRow9124 := by decide +kernel

theorem rowCheck9124 : row9124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9124 := by decide +kernel

theorem rowEval9124 (x : Key → ℝ) : Integer.Sparse.eval row9124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck9124, Integer.Sparse.eval_collectBalanced, rawRowCheck9124]

theorem rawRowCheck9125 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form9 = rawRow9125 := by decide +kernel

theorem rowCheck9125 : row9125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9125 := by decide +kernel

theorem rowEval9125 (x : Key → ℝ) : Integer.Sparse.eval row9125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9125, Integer.Sparse.eval_collectBalanced, rawRowCheck9125]

theorem rawRowCheck9126 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form9 = rawRow9126 := by decide +kernel

theorem rowCheck9126 : row9126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9126 := by decide +kernel

theorem rowEval9126 (x : Key → ℝ) : Integer.Sparse.eval row9126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9126, Integer.Sparse.eval_collectBalanced, rawRowCheck9126]

theorem rawRowCheck9127 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form9 = rawRow9127 := by decide +kernel

theorem rowCheck9127 : row9127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9127 := by decide +kernel

theorem rowEval9127 (x : Key → ℝ) : Integer.Sparse.eval row9127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9127, Integer.Sparse.eval_collectBalanced, rawRowCheck9127]

theorem rawRowCheck9128 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow9128 := by decide +kernel

theorem rowCheck9128 : row9128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9128 := by decide +kernel

theorem rowEval9128 (x : Key → ℝ) : Integer.Sparse.eval row9128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9128, Integer.Sparse.eval_collectBalanced, rawRowCheck9128]

theorem rawRowCheck9129 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form9 = rawRow9129 := by decide +kernel

theorem rowCheck9129 : row9129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9129 := by decide +kernel

theorem rowEval9129 (x : Key → ℝ) : Integer.Sparse.eval row9129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9129, Integer.Sparse.eval_collectBalanced, rawRowCheck9129]

theorem rawRowCheck9130 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form9 = rawRow9130 := by decide +kernel

theorem rowCheck9130 : row9130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9130 := by decide +kernel

theorem rowEval9130 (x : Key → ℝ) : Integer.Sparse.eval row9130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9130, Integer.Sparse.eval_collectBalanced, rawRowCheck9130]

theorem rawRowCheck9131 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form9 = rawRow9131 := by decide +kernel

theorem rowCheck9131 : row9131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9131 := by decide +kernel

theorem rowEval9131 (x : Key → ℝ) : Integer.Sparse.eval row9131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9131, Integer.Sparse.eval_collectBalanced, rawRowCheck9131]

theorem rawRowCheck9132 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9 = rawRow9132 := by decide +kernel

theorem rowCheck9132 : row9132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9132 := by decide +kernel

theorem rowEval9132 (x : Key → ℝ) : Integer.Sparse.eval row9132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck9132, Integer.Sparse.eval_collectBalanced, rawRowCheck9132]

theorem rawRowCheck9133 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow9133 := by decide +kernel

theorem rowCheck9133 : row9133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9133 := by decide +kernel

theorem rowEval9133 (x : Key → ℝ) : Integer.Sparse.eval row9133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9133, Integer.Sparse.eval_collectBalanced, rawRowCheck9133]

theorem rawRowCheck9134 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow9134 := by decide +kernel

theorem rowCheck9134 : row9134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9134 := by decide +kernel

theorem rowEval9134 (x : Key → ℝ) : Integer.Sparse.eval row9134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9134, Integer.Sparse.eval_collectBalanced, rawRowCheck9134]

theorem rawRowCheck9135 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow9135 := by decide +kernel

theorem rowCheck9135 : row9135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9135 := by decide +kernel

theorem rowEval9135 (x : Key → ℝ) : Integer.Sparse.eval row9135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9135, Integer.Sparse.eval_collectBalanced, rawRowCheck9135]

theorem rawRowCheck9136 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9136 := by decide +kernel

theorem rowCheck9136 : row9136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9136 := by decide +kernel

theorem rowEval9136 (x : Key → ℝ) : Integer.Sparse.eval row9136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9136, Integer.Sparse.eval_collectBalanced, rawRowCheck9136]

theorem rawRowCheck9137 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9137 := by decide +kernel

theorem rowCheck9137 : row9137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9137 := by decide +kernel

theorem rowEval9137 (x : Key → ℝ) : Integer.Sparse.eval row9137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9137, Integer.Sparse.eval_collectBalanced, rawRowCheck9137]

theorem rawRowCheck9138 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow9138 := by decide +kernel

theorem rowCheck9138 : row9138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9138 := by decide +kernel

theorem rowEval9138 (x : Key → ℝ) : Integer.Sparse.eval row9138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9138, Integer.Sparse.eval_collectBalanced, rawRowCheck9138]

theorem rawRowCheck9139 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow9139 := by decide +kernel

theorem rowCheck9139 : row9139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9139 := by decide +kernel

theorem rowEval9139 (x : Key → ℝ) : Integer.Sparse.eval row9139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9139, Integer.Sparse.eval_collectBalanced, rawRowCheck9139]

theorem rawRowCheck9140 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow9140 := by decide +kernel

theorem rowCheck9140 : row9140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9140 := by decide +kernel

theorem rowEval9140 (x : Key → ℝ) : Integer.Sparse.eval row9140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9140, Integer.Sparse.eval_collectBalanced, rawRowCheck9140]

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

theorem rawRowCheck9149 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow9149 := by decide +kernel

theorem rowCheck9149 : row9149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9149 := by decide +kernel

theorem rowEval9149 (x : Key → ℝ) : Integer.Sparse.eval row9149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9149, Integer.Sparse.eval_collectBalanced, rawRowCheck9149]

theorem rawRowCheck9150 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow9150 := by decide +kernel

theorem rowCheck9150 : row9150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9150 := by decide +kernel

theorem rowEval9150 (x : Key → ℝ) : Integer.Sparse.eval row9150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9150, Integer.Sparse.eval_collectBalanced, rawRowCheck9150]

theorem rawRowCheck9151 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow9151 := by decide +kernel

theorem rowCheck9151 : row9151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9151 := by decide +kernel

theorem rowEval9151 (x : Key → ℝ) : Integer.Sparse.eval row9151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9151, Integer.Sparse.eval_collectBalanced, rawRowCheck9151]

theorem rawRowCheck9152 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9152 := by decide +kernel

theorem rowCheck9152 : row9152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9152 := by decide +kernel

theorem rowEval9152 (x : Key → ℝ) : Integer.Sparse.eval row9152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9152, Integer.Sparse.eval_collectBalanced, rawRowCheck9152]

theorem rawRowCheck9153 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9153 := by decide +kernel

theorem rowCheck9153 : row9153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9153 := by decide +kernel

theorem rowEval9153 (x : Key → ℝ) : Integer.Sparse.eval row9153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9153, Integer.Sparse.eval_collectBalanced, rawRowCheck9153]

theorem rawRowCheck9154 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form12 = rawRow9154 := by decide +kernel

theorem rowCheck9154 : row9154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9154 := by decide +kernel

theorem rowEval9154 (x : Key → ℝ) : Integer.Sparse.eval row9154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9154, Integer.Sparse.eval_collectBalanced, rawRowCheck9154]

theorem rawRowCheck9155 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form12 = rawRow9155 := by decide +kernel

theorem rowCheck9155 : row9155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9155 := by decide +kernel

theorem rowEval9155 (x : Key → ℝ) : Integer.Sparse.eval row9155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9155, Integer.Sparse.eval_collectBalanced, rawRowCheck9155]

theorem rawRowCheck9156 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form12 = rawRow9156 := by decide +kernel

theorem rowCheck9156 : row9156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9156 := by decide +kernel

theorem rowEval9156 (x : Key → ℝ) : Integer.Sparse.eval row9156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9156, Integer.Sparse.eval_collectBalanced, rawRowCheck9156]

theorem rawRowCheck9157 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form13 = rawRow9157 := by decide +kernel

theorem rowCheck9157 : row9157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9157 := by decide +kernel

theorem rowEval9157 (x : Key → ℝ) : Integer.Sparse.eval row9157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9157, Integer.Sparse.eval_collectBalanced, rawRowCheck9157]

theorem rawRowCheck9158 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form13 = rawRow9158 := by decide +kernel

theorem rowCheck9158 : row9158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9158 := by decide +kernel

theorem rowEval9158 (x : Key → ℝ) : Integer.Sparse.eval row9158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9158, Integer.Sparse.eval_collectBalanced, rawRowCheck9158]

theorem rawRowCheck9159 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form13 = rawRow9159 := by decide +kernel

theorem rowCheck9159 : row9159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9159 := by decide +kernel

theorem rowEval9159 (x : Key → ℝ) : Integer.Sparse.eval row9159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9159, Integer.Sparse.eval_collectBalanced, rawRowCheck9159]

theorem rawRowCheck9160 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9160 := by decide +kernel

theorem rowCheck9160 : row9160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9160 := by decide +kernel

theorem rowEval9160 (x : Key → ℝ) : Integer.Sparse.eval row9160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9160, Integer.Sparse.eval_collectBalanced, rawRowCheck9160]

theorem rawRowCheck9161 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9161 := by decide +kernel

theorem rowCheck9161 : row9161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9161 := by decide +kernel

theorem rowEval9161 (x : Key → ℝ) : Integer.Sparse.eval row9161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9161, Integer.Sparse.eval_collectBalanced, rawRowCheck9161]

theorem rawRowCheck9162 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form13 = rawRow9162 := by decide +kernel

theorem rowCheck9162 : row9162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9162 := by decide +kernel

theorem rowEval9162 (x : Key → ℝ) : Integer.Sparse.eval row9162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9162, Integer.Sparse.eval_collectBalanced, rawRowCheck9162]

theorem rawRowCheck9163 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form13 = rawRow9163 := by decide +kernel

theorem rowCheck9163 : row9163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9163 := by decide +kernel

theorem rowEval9163 (x : Key → ℝ) : Integer.Sparse.eval row9163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9163, Integer.Sparse.eval_collectBalanced, rawRowCheck9163]

theorem rawRowCheck9164 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form13 = rawRow9164 := by decide +kernel

theorem rowCheck9164 : row9164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9164 := by decide +kernel

theorem rowEval9164 (x : Key → ℝ) : Integer.Sparse.eval row9164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9164, Integer.Sparse.eval_collectBalanced, rawRowCheck9164]

theorem rawRowCheck9165 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form14 = rawRow9165 := by decide +kernel

theorem rowCheck9165 : row9165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9165 := by decide +kernel

theorem rowEval9165 (x : Key → ℝ) : Integer.Sparse.eval row9165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9165, Integer.Sparse.eval_collectBalanced, rawRowCheck9165]

theorem rawRowCheck9166 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form14 = rawRow9166 := by decide +kernel

theorem rowCheck9166 : row9166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9166 := by decide +kernel

theorem rowEval9166 (x : Key → ℝ) : Integer.Sparse.eval row9166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9166, Integer.Sparse.eval_collectBalanced, rawRowCheck9166]

theorem rawRowCheck9167 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form14 = rawRow9167 := by decide +kernel

theorem rowCheck9167 : row9167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9167 := by decide +kernel

theorem rowEval9167 (x : Key → ℝ) : Integer.Sparse.eval row9167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9167, Integer.Sparse.eval_collectBalanced, rawRowCheck9167]

theorem rawRowCheck9168 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9168 := by decide +kernel

theorem rowCheck9168 : row9168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9168 := by decide +kernel

theorem rowEval9168 (x : Key → ℝ) : Integer.Sparse.eval row9168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9168, Integer.Sparse.eval_collectBalanced, rawRowCheck9168]

theorem rawRowCheck9169 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9169 := by decide +kernel

theorem rowCheck9169 : row9169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9169 := by decide +kernel

theorem rowEval9169 (x : Key → ℝ) : Integer.Sparse.eval row9169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9169, Integer.Sparse.eval_collectBalanced, rawRowCheck9169]

theorem rawRowCheck9170 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form14 = rawRow9170 := by decide +kernel

theorem rowCheck9170 : row9170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9170 := by decide +kernel

theorem rowEval9170 (x : Key → ℝ) : Integer.Sparse.eval row9170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9170, Integer.Sparse.eval_collectBalanced, rawRowCheck9170]

theorem rawRowCheck9171 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form14 = rawRow9171 := by decide +kernel

theorem rowCheck9171 : row9171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9171 := by decide +kernel

theorem rowEval9171 (x : Key → ℝ) : Integer.Sparse.eval row9171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9171, Integer.Sparse.eval_collectBalanced, rawRowCheck9171]

theorem rawRowCheck9172 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form14 = rawRow9172 := by decide +kernel

theorem rowCheck9172 : row9172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9172 := by decide +kernel

theorem rowEval9172 (x : Key → ℝ) : Integer.Sparse.eval row9172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9172, Integer.Sparse.eval_collectBalanced, rawRowCheck9172]

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

theorem entryCheck14_1 : entry14_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_1 k)) := by decide +kernel

theorem rowsSound14_1 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7398 x
  · exact rowEval7399 x
  · exact rowEval7400 x
  · exact rowEval7401 x
  · exact rowEval9069 x
  · exact rowEval9070 x
  · exact rowEval9071 x
  · exact rowEval9072 x

theorem entryEval14_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_1 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck14_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_1]

theorem entryCheck14_2 : entry14_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_2 k)) := by decide +kernel

theorem rowsSound14_2 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7414 x
  · exact rowEval7415 x
  · exact rowEval7416 x
  · exact rowEval7417 x
  · exact rowEval9073 x
  · exact rowEval9074 x
  · exact rowEval9075 x
  · exact rowEval9076 x

theorem entryEval14_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_2 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck14_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_2]

theorem entryCheck14_3 : entry14_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_3 k)) := by decide +kernel

theorem rowsSound14_3 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval9077 x
  · exact rowEval9078 x
  · exact rowEval9079 x
  · exact rowEval9080 x
  · exact rowEval9081 x
  · exact rowEval9082 x
  · exact rowEval9083 x
  · exact rowEval9084 x

theorem entryEval14_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_3 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck14_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_3]

theorem entryCheck14_4 : entry14_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_4 k)) := by decide +kernel

theorem rowsSound14_4 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval9085 x
  · exact rowEval9086 x
  · exact rowEval9087 x
  · exact rowEval9088 x
  · exact rowEval9089 x
  · exact rowEval9090 x
  · exact rowEval9091 x
  · exact rowEval9092 x

theorem entryEval14_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_4 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck14_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_4]

theorem entryCheck14_5 : entry14_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_5 k)) := by decide +kernel

theorem rowsSound14_5 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval9093 x
  · exact rowEval9094 x
  · exact rowEval9095 x
  · exact rowEval9096 x
  · exact rowEval9097 x
  · exact rowEval9098 x
  · exact rowEval9099 x
  · exact rowEval9100 x

theorem entryEval14_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_5 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck14_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_5]

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

theorem entryCheck14_7 : entry14_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_7 k)) := by decide +kernel

theorem rowsSound14_7 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval9109 x
  · exact rowEval9110 x
  · exact rowEval9111 x
  · exact rowEval9112 x
  · exact rowEval9113 x
  · exact rowEval9114 x
  · exact rowEval9115 x
  · exact rowEval9116 x

theorem entryEval14_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_7 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck14_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_7]

theorem entryCheck14_8 : entry14_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_8 k)) := by decide +kernel

theorem rowsSound14_8 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval9117 x
  · exact rowEval9118 x
  · exact rowEval9119 x
  · exact rowEval9120 x
  · exact rowEval9121 x
  · exact rowEval9122 x
  · exact rowEval9123 x
  · exact rowEval9124 x

theorem entryEval14_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_8 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck14_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_8]

theorem entryCheck14_9 : entry14_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_9 k)) := by decide +kernel

theorem rowsSound14_9 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval9125 x
  · exact rowEval9126 x
  · exact rowEval9127 x
  · exact rowEval9128 x
  · exact rowEval9129 x
  · exact rowEval9130 x
  · exact rowEval9131 x
  · exact rowEval9132 x

theorem entryEval14_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_9 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck14_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_9]

theorem entryCheck14_10 : entry14_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_10 k)) := by decide +kernel

theorem rowsSound14_10 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9133 x
  · exact rowEval9134 x
  · exact rowEval9135 x
  · exact rowEval9136 x
  · exact rowEval9137 x
  · exact rowEval9138 x
  · exact rowEval9139 x
  · exact rowEval9140 x

theorem entryEval14_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_10 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck14_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_10]

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

theorem entryCheck14_12 : entry14_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_12 k)) := by decide +kernel

theorem rowsSound14_12 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9149 x
  · exact rowEval9150 x
  · exact rowEval9151 x
  · exact rowEval9152 x
  · exact rowEval9153 x
  · exact rowEval9154 x
  · exact rowEval9155 x
  · exact rowEval9156 x

theorem entryEval14_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_12 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck14_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_12]

theorem entryCheck14_13 : entry14_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_13 k)) := by decide +kernel

theorem rowsSound14_13 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9157 x
  · exact rowEval9158 x
  · exact rowEval9159 x
  · exact rowEval9160 x
  · exact rowEval9161 x
  · exact rowEval9162 x
  · exact rowEval9163 x
  · exact rowEval9164 x

theorem entryEval14_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_13 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck14_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_13]

theorem entryCheck14_14 : entry14_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_14 k)) := by decide +kernel

theorem rowsSound14_14 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9165 x
  · exact rowEval9166 x
  · exact rowEval9167 x
  · exact rowEval9168 x
  · exact rowEval9169 x
  · exact rowEval9170 x
  · exact rowEval9171 x
  · exact rowEval9172 x

theorem entryEval14_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_14 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck14_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_14]

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

theorem rawRowCheck9349 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form14 = rawRow9349 := by decide +kernel

theorem rowCheck9349 : row9349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9349 := by decide +kernel

theorem rowEval9349 (x : Key → ℝ) : Integer.Sparse.eval row9349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9349, Integer.Sparse.eval_collectBalanced, rawRowCheck9349]

theorem rawRowCheck9350 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form14 = rawRow9350 := by decide +kernel

theorem rowCheck9350 : row9350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9350 := by decide +kernel

theorem rowEval9350 (x : Key → ℝ) : Integer.Sparse.eval row9350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9350, Integer.Sparse.eval_collectBalanced, rawRowCheck9350]

theorem rawRowCheck9351 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form14 = rawRow9351 := by decide +kernel

theorem rowCheck9351 : row9351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9351 := by decide +kernel

theorem rowEval9351 (x : Key → ℝ) : Integer.Sparse.eval row9351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9351, Integer.Sparse.eval_collectBalanced, rawRowCheck9351]

theorem rawRowCheck9352 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9352 := by decide +kernel

theorem rowCheck9352 : row9352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9352 := by decide +kernel

theorem rowEval9352 (x : Key → ℝ) : Integer.Sparse.eval row9352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9352, Integer.Sparse.eval_collectBalanced, rawRowCheck9352]

theorem rawRowCheck9353 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form14 = rawRow9353 := by decide +kernel

theorem rowCheck9353 : row9353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9353 := by decide +kernel

theorem rowEval9353 (x : Key → ℝ) : Integer.Sparse.eval row9353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9353, Integer.Sparse.eval_collectBalanced, rawRowCheck9353]

theorem rawRowCheck9354 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form14 = rawRow9354 := by decide +kernel

theorem rowCheck9354 : row9354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9354 := by decide +kernel

theorem rowEval9354 (x : Key → ℝ) : Integer.Sparse.eval row9354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9354, Integer.Sparse.eval_collectBalanced, rawRowCheck9354]

theorem rawRowCheck9355 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form14 = rawRow9355 := by decide +kernel

theorem rowCheck9355 : row9355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9355 := by decide +kernel

theorem rowEval9355 (x : Key → ℝ) : Integer.Sparse.eval row9355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9355, Integer.Sparse.eval_collectBalanced, rawRowCheck9355]

theorem rawRowCheck9356 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form14 = rawRow9356 := by decide +kernel

theorem rowCheck9356 : row9356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9356 := by decide +kernel

theorem rowEval9356 (x : Key → ℝ) : Integer.Sparse.eval row9356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9356, Integer.Sparse.eval_collectBalanced, rawRowCheck9356]

theorem rawRowCheck9357 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form14 = rawRow9357 := by decide +kernel

theorem rowCheck9357 : row9357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9357 := by decide +kernel

theorem rowEval9357 (x : Key → ℝ) : Integer.Sparse.eval row9357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9357, Integer.Sparse.eval_collectBalanced, rawRowCheck9357]

theorem rawRowCheck9358 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form14 = rawRow9358 := by decide +kernel

theorem rowCheck9358 : row9358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9358 := by decide +kernel

theorem rowEval9358 (x : Key → ℝ) : Integer.Sparse.eval row9358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9358, Integer.Sparse.eval_collectBalanced, rawRowCheck9358]

theorem rawRowCheck9359 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form14 = rawRow9359 := by decide +kernel

theorem rowCheck9359 : row9359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9359 := by decide +kernel

theorem rowEval9359 (x : Key → ℝ) : Integer.Sparse.eval row9359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9359, Integer.Sparse.eval_collectBalanced, rawRowCheck9359]

theorem rawRowCheck9360 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form14 = rawRow9360 := by decide +kernel

theorem rowCheck9360 : row9360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9360 := by decide +kernel

theorem rowEval9360 (x : Key → ℝ) : Integer.Sparse.eval row9360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9360, Integer.Sparse.eval_collectBalanced, rawRowCheck9360]

theorem rawRowCheck9361 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form14 = rawRow9361 := by decide +kernel

theorem rowCheck9361 : row9361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9361 := by decide +kernel

theorem rowEval9361 (x : Key → ℝ) : Integer.Sparse.eval row9361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9361, Integer.Sparse.eval_collectBalanced, rawRowCheck9361]

theorem rawRowCheck9362 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form14 = rawRow9362 := by decide +kernel

theorem rowCheck9362 : row9362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9362 := by decide +kernel

theorem rowEval9362 (x : Key → ℝ) : Integer.Sparse.eval row9362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9362, Integer.Sparse.eval_collectBalanced, rawRowCheck9362]

theorem rawRowCheck9363 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form14 = rawRow9363 := by decide +kernel

theorem rowCheck9363 : row9363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9363 := by decide +kernel

theorem rowEval9363 (x : Key → ℝ) : Integer.Sparse.eval row9363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9363, Integer.Sparse.eval_collectBalanced, rawRowCheck9363]

theorem rawRowCheck9364 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form14 = rawRow9364 := by decide +kernel

theorem rowCheck9364 : row9364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9364 := by decide +kernel

theorem rowEval9364 (x : Key → ℝ) : Integer.Sparse.eval row9364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck9364, Integer.Sparse.eval_collectBalanced, rawRowCheck9364]

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

theorem entryCheck15_14 : entry15_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_14 k)) := by decide +kernel

theorem rowsSound15_14 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9349 x
  · exact rowEval9350 x
  · exact rowEval9351 x
  · exact rowEval9352 x
  · exact rowEval9353 x
  · exact rowEval9354 x
  · exact rowEval9355 x
  · exact rowEval9356 x
  · exact rowEval9357 x
  · exact rowEval9358 x
  · exact rowEval9359 x
  · exact rowEval9360 x
  · exact rowEval9361 x
  · exact rowEval9362 x
  · exact rowEval9363 x
  · exact rowEval9364 x

theorem entryEval15_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_14 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck15_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_14]

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

theorem rawRowCheck9837 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form14 = rawRow9837 := by decide +kernel

theorem rowCheck9837 : row9837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9837 := by decide +kernel

theorem rowEval9837 (x : Key → ℝ) : Integer.Sparse.eval row9837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9837, Integer.Sparse.eval_collectBalanced, rawRowCheck9837]

theorem rawRowCheck9838 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form14 = rawRow9838 := by decide +kernel

theorem rowCheck9838 : row9838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9838 := by decide +kernel

theorem rowEval9838 (x : Key → ℝ) : Integer.Sparse.eval row9838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9838, Integer.Sparse.eval_collectBalanced, rawRowCheck9838]

theorem rawRowCheck9839 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form14 = rawRow9839 := by decide +kernel

theorem rowCheck9839 : row9839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9839 := by decide +kernel

theorem rowEval9839 (x : Key → ℝ) : Integer.Sparse.eval row9839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9839, Integer.Sparse.eval_collectBalanced, rawRowCheck9839]

theorem rawRowCheck9840 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form14 = rawRow9840 := by decide +kernel

theorem rowCheck9840 : row9840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9840 := by decide +kernel

theorem rowEval9840 (x : Key → ℝ) : Integer.Sparse.eval row9840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9840, Integer.Sparse.eval_collectBalanced, rawRowCheck9840]

theorem rawRowCheck9841 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form14 = rawRow9841 := by decide +kernel

theorem rowCheck9841 : row9841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9841 := by decide +kernel

theorem rowEval9841 (x : Key → ℝ) : Integer.Sparse.eval row9841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9841, Integer.Sparse.eval_collectBalanced, rawRowCheck9841]

theorem rawRowCheck9842 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form14 = rawRow9842 := by decide +kernel

theorem rowCheck9842 : row9842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9842 := by decide +kernel

theorem rowEval9842 (x : Key → ℝ) : Integer.Sparse.eval row9842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9842, Integer.Sparse.eval_collectBalanced, rawRowCheck9842]

theorem rawRowCheck9843 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow9843 := by decide +kernel

theorem rowCheck9843 : row9843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9843 := by decide +kernel

theorem rowEval9843 (x : Key → ℝ) : Integer.Sparse.eval row9843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9843, Integer.Sparse.eval_collectBalanced, rawRowCheck9843]

theorem rawRowCheck9844 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow9844 := by decide +kernel

theorem rowCheck9844 : row9844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9844 := by decide +kernel

theorem rowEval9844 (x : Key → ℝ) : Integer.Sparse.eval row9844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9844, Integer.Sparse.eval_collectBalanced, rawRowCheck9844]

theorem rawRowCheck9845 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow9845 := by decide +kernel

theorem rowCheck9845 : row9845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9845 := by decide +kernel

theorem rowEval9845 (x : Key → ℝ) : Integer.Sparse.eval row9845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9845, Integer.Sparse.eval_collectBalanced, rawRowCheck9845]

theorem rawRowCheck9846 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow9846 := by decide +kernel

theorem rowCheck9846 : row9846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9846 := by decide +kernel

theorem rowEval9846 (x : Key → ℝ) : Integer.Sparse.eval row9846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9846, Integer.Sparse.eval_collectBalanced, rawRowCheck9846]

theorem rawRowCheck9847 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow9847 := by decide +kernel

theorem rowCheck9847 : row9847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9847 := by decide +kernel

theorem rowEval9847 (x : Key → ℝ) : Integer.Sparse.eval row9847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9847, Integer.Sparse.eval_collectBalanced, rawRowCheck9847]

theorem rawRowCheck9848 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow9848 := by decide +kernel

theorem rowCheck9848 : row9848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9848 := by decide +kernel

theorem rowEval9848 (x : Key → ℝ) : Integer.Sparse.eval row9848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9848, Integer.Sparse.eval_collectBalanced, rawRowCheck9848]

theorem rawRowCheck9849 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form14 = rawRow9849 := by decide +kernel

theorem rowCheck9849 : row9849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9849 := by decide +kernel

theorem rowEval9849 (x : Key → ℝ) : Integer.Sparse.eval row9849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9849, Integer.Sparse.eval_collectBalanced, rawRowCheck9849]

theorem rawRowCheck9850 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form14 = rawRow9850 := by decide +kernel

theorem rowCheck9850 : row9850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9850 := by decide +kernel

theorem rowEval9850 (x : Key → ℝ) : Integer.Sparse.eval row9850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9850, Integer.Sparse.eval_collectBalanced, rawRowCheck9850]

theorem rawRowCheck9851 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form14 = rawRow9851 := by decide +kernel

theorem rowCheck9851 : row9851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9851 := by decide +kernel

theorem rowEval9851 (x : Key → ℝ) : Integer.Sparse.eval row9851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9851, Integer.Sparse.eval_collectBalanced, rawRowCheck9851]

theorem rawRowCheck9852 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form14 = rawRow9852 := by decide +kernel

theorem rowCheck9852 : row9852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9852 := by decide +kernel

theorem rowEval9852 (x : Key → ℝ) : Integer.Sparse.eval row9852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9852, Integer.Sparse.eval_collectBalanced, rawRowCheck9852]

theorem rawRowCheck9853 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form14 = rawRow9853 := by decide +kernel

theorem rowCheck9853 : row9853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9853 := by decide +kernel

theorem rowEval9853 (x : Key → ℝ) : Integer.Sparse.eval row9853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9853, Integer.Sparse.eval_collectBalanced, rawRowCheck9853]

theorem rawRowCheck9854 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form14 = rawRow9854 := by decide +kernel

theorem rowCheck9854 : row9854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9854 := by decide +kernel

theorem rowEval9854 (x : Key → ℝ) : Integer.Sparse.eval row9854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9854, Integer.Sparse.eval_collectBalanced, rawRowCheck9854]

theorem rawRowCheck9855 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form14 = rawRow9855 := by decide +kernel

theorem rowCheck9855 : row9855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9855 := by decide +kernel

theorem rowEval9855 (x : Key → ℝ) : Integer.Sparse.eval row9855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9855, Integer.Sparse.eval_collectBalanced, rawRowCheck9855]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck9856 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form14 = rawRow9856 := by decide +kernel

theorem rowCheck9856 : row9856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9856 := by decide +kernel

theorem rowEval9856 (x : Key → ℝ) : Integer.Sparse.eval row9856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9856, Integer.Sparse.eval_collectBalanced, rawRowCheck9856]

theorem rawRowCheck9857 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form14 = rawRow9857 := by decide +kernel

theorem rowCheck9857 : row9857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9857 := by decide +kernel

theorem rowEval9857 (x : Key → ℝ) : Integer.Sparse.eval row9857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9857, Integer.Sparse.eval_collectBalanced, rawRowCheck9857]

theorem rawRowCheck9858 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form14 = rawRow9858 := by decide +kernel

theorem rowCheck9858 : row9858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9858 := by decide +kernel

theorem rowEval9858 (x : Key → ℝ) : Integer.Sparse.eval row9858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9858, Integer.Sparse.eval_collectBalanced, rawRowCheck9858]

theorem rawRowCheck9859 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form14 = rawRow9859 := by decide +kernel

theorem rowCheck9859 : row9859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9859 := by decide +kernel

theorem rowEval9859 (x : Key → ℝ) : Integer.Sparse.eval row9859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9859, Integer.Sparse.eval_collectBalanced, rawRowCheck9859]

theorem rawRowCheck9860 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form14 = rawRow9860 := by decide +kernel

theorem rowCheck9860 : row9860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9860 := by decide +kernel

theorem rowEval9860 (x : Key → ℝ) : Integer.Sparse.eval row9860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9860, Integer.Sparse.eval_collectBalanced, rawRowCheck9860]

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

theorem entryCheck17_14 : entry17_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_14 k)) := by decide +kernel

theorem rowsSound17_14 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9837 x
  · exact rowEval9838 x
  · exact rowEval9839 x
  · exact rowEval9840 x
  · exact rowEval9841 x
  · exact rowEval9842 x
  · exact rowEval9843 x
  · exact rowEval9844 x
  · exact rowEval9845 x
  · exact rowEval9846 x
  · exact rowEval9847 x
  · exact rowEval9848 x
  · exact rowEval9849 x
  · exact rowEval9850 x
  · exact rowEval9851 x
  · exact rowEval9852 x
  · exact rowEval9853 x
  · exact rowEval9854 x
  · exact rowEval9855 x
  · exact rowEval9856 x
  · exact rowEval9857 x
  · exact rowEval9858 x
  · exact rowEval9859 x
  · exact rowEval9860 x

theorem entryEval17_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_14 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck17_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_14]

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

theorem rawRowCheck10529 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form14 = rawRow10529 := by decide +kernel

theorem rowCheck10529 : row10529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10529 := by decide +kernel

theorem rowEval10529 (x : Key → ℝ) : Integer.Sparse.eval row10529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10529, Integer.Sparse.eval_collectBalanced, rawRowCheck10529]

theorem rawRowCheck10530 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form14 = rawRow10530 := by decide +kernel

theorem rowCheck10530 : row10530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10530 := by decide +kernel

theorem rowEval10530 (x : Key → ℝ) : Integer.Sparse.eval row10530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10530, Integer.Sparse.eval_collectBalanced, rawRowCheck10530]

theorem rawRowCheck10531 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form14 = rawRow10531 := by decide +kernel

theorem rowCheck10531 : row10531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10531 := by decide +kernel

theorem rowEval10531 (x : Key → ℝ) : Integer.Sparse.eval row10531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10531, Integer.Sparse.eval_collectBalanced, rawRowCheck10531]

theorem rawRowCheck10532 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form14 = rawRow10532 := by decide +kernel

theorem rowCheck10532 : row10532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10532 := by decide +kernel

theorem rowEval10532 (x : Key → ℝ) : Integer.Sparse.eval row10532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10532, Integer.Sparse.eval_collectBalanced, rawRowCheck10532]

theorem rawRowCheck10533 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form14 = rawRow10533 := by decide +kernel

theorem rowCheck10533 : row10533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10533 := by decide +kernel

theorem rowEval10533 (x : Key → ℝ) : Integer.Sparse.eval row10533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10533, Integer.Sparse.eval_collectBalanced, rawRowCheck10533]

theorem rawRowCheck10534 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form14 = rawRow10534 := by decide +kernel

theorem rowCheck10534 : row10534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10534 := by decide +kernel

theorem rowEval10534 (x : Key → ℝ) : Integer.Sparse.eval row10534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10534, Integer.Sparse.eval_collectBalanced, rawRowCheck10534]

theorem rawRowCheck10535 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form14 = rawRow10535 := by decide +kernel

theorem rowCheck10535 : row10535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10535 := by decide +kernel

theorem rowEval10535 (x : Key → ℝ) : Integer.Sparse.eval row10535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10535, Integer.Sparse.eval_collectBalanced, rawRowCheck10535]

theorem rawRowCheck10536 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form14 = rawRow10536 := by decide +kernel

theorem rowCheck10536 : row10536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10536 := by decide +kernel

theorem rowEval10536 (x : Key → ℝ) : Integer.Sparse.eval row10536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10536, Integer.Sparse.eval_collectBalanced, rawRowCheck10536]

theorem rawRowCheck10537 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form14 = rawRow10537 := by decide +kernel

theorem rowCheck10537 : row10537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10537 := by decide +kernel

theorem rowEval10537 (x : Key → ℝ) : Integer.Sparse.eval row10537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10537, Integer.Sparse.eval_collectBalanced, rawRowCheck10537]

theorem rawRowCheck10538 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form14 = rawRow10538 := by decide +kernel

theorem rowCheck10538 : row10538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10538 := by decide +kernel

theorem rowEval10538 (x : Key → ℝ) : Integer.Sparse.eval row10538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10538, Integer.Sparse.eval_collectBalanced, rawRowCheck10538]

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

theorem entryCheck19_14 : entry19_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_14 k)) := by decide +kernel

theorem rowsSound19_14 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval10529 x
  · exact rowEval10530 x
  · exact rowEval10531 x
  · exact rowEval10532 x
  · exact rowEval10533 x
  · exact rowEval10534 x
  · exact rowEval10535 x
  · exact rowEval10536 x
  · exact rowEval10537 x
  · exact rowEval10538 x

theorem entryEval19_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_14 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck19_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_14]

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

theorem rawRowCheck10659 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form14 = rawRow10659 := by decide +kernel

theorem rowCheck10659 : row10659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10659 := by decide +kernel

theorem rowEval10659 (x : Key → ℝ) : Integer.Sparse.eval row10659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form14) x := by
  rw [rowCheck10659, Integer.Sparse.eval_collectBalanced, rawRowCheck10659]

theorem rawRowCheck10660 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form14 = rawRow10660 := by decide +kernel

theorem rowCheck10660 : row10660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10660 := by decide +kernel

theorem rowEval10660 (x : Key → ℝ) : Integer.Sparse.eval row10660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10660, Integer.Sparse.eval_collectBalanced, rawRowCheck10660]

theorem rawRowCheck10661 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form14 = rawRow10661 := by decide +kernel

theorem rowCheck10661 : row10661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10661 := by decide +kernel

theorem rowEval10661 (x : Key → ℝ) : Integer.Sparse.eval row10661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10661, Integer.Sparse.eval_collectBalanced, rawRowCheck10661]

theorem rawRowCheck10662 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow10662 := by decide +kernel

theorem rowCheck10662 : row10662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10662 := by decide +kernel

theorem rowEval10662 (x : Key → ℝ) : Integer.Sparse.eval row10662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10662, Integer.Sparse.eval_collectBalanced, rawRowCheck10662]

theorem rawRowCheck10663 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form14 = rawRow10663 := by decide +kernel

theorem rowCheck10663 : row10663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10663 := by decide +kernel

theorem rowEval10663 (x : Key → ℝ) : Integer.Sparse.eval row10663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10663, Integer.Sparse.eval_collectBalanced, rawRowCheck10663]

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

theorem entryCheck20_14 : entry20_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_14 k)) := by decide +kernel

theorem rowsSound20_14 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval10659 x
  · exact rowEval10660 x
  · exact rowEval10661 x
  · exact rowEval10662 x
  · exact rowEval10663 x

theorem entryEval20_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_14 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck20_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_14]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11198 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form14 = rawRow11198 := by decide +kernel

theorem rowCheck11198 : row11198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11198 := by decide +kernel

theorem rowEval11198 (x : Key → ℝ) : Integer.Sparse.eval row11198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11198, Integer.Sparse.eval_collectBalanced, rawRowCheck11198]

theorem rawRowCheck11199 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form14 = rawRow11199 := by decide +kernel

theorem rowCheck11199 : row11199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11199 := by decide +kernel

theorem rowEval11199 (x : Key → ℝ) : Integer.Sparse.eval row11199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11199, Integer.Sparse.eval_collectBalanced, rawRowCheck11199]

theorem rawRowCheck11200 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form14 = rawRow11200 := by decide +kernel

theorem rowCheck11200 : row11200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11200 := by decide +kernel

theorem rowEval11200 (x : Key → ℝ) : Integer.Sparse.eval row11200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11200, Integer.Sparse.eval_collectBalanced, rawRowCheck11200]

theorem rawRowCheck11201 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form14 = rawRow11201 := by decide +kernel

theorem rowCheck11201 : row11201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11201 := by decide +kernel

theorem rowEval11201 (x : Key → ℝ) : Integer.Sparse.eval row11201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11201, Integer.Sparse.eval_collectBalanced, rawRowCheck11201]

theorem rawRowCheck11202 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form14 = rawRow11202 := by decide +kernel

theorem rowCheck11202 : row11202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11202 := by decide +kernel

theorem rowEval11202 (x : Key → ℝ) : Integer.Sparse.eval row11202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11202, Integer.Sparse.eval_collectBalanced, rawRowCheck11202]

theorem rawRowCheck11203 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form14 = rawRow11203 := by decide +kernel

theorem rowCheck11203 : row11203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11203 := by decide +kernel

theorem rowEval11203 (x : Key → ℝ) : Integer.Sparse.eval row11203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11203, Integer.Sparse.eval_collectBalanced, rawRowCheck11203]

theorem rawRowCheck11204 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow11204 := by decide +kernel

theorem rowCheck11204 : row11204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11204 := by decide +kernel

theorem rowEval11204 (x : Key → ℝ) : Integer.Sparse.eval row11204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11204, Integer.Sparse.eval_collectBalanced, rawRowCheck11204]

theorem rawRowCheck11205 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow11205 := by decide +kernel

theorem rowCheck11205 : row11205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11205 := by decide +kernel

theorem rowEval11205 (x : Key → ℝ) : Integer.Sparse.eval row11205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11205, Integer.Sparse.eval_collectBalanced, rawRowCheck11205]

theorem rawRowCheck11206 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow11206 := by decide +kernel

theorem rowCheck11206 : row11206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11206 := by decide +kernel

theorem rowEval11206 (x : Key → ℝ) : Integer.Sparse.eval row11206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11206, Integer.Sparse.eval_collectBalanced, rawRowCheck11206]

theorem rawRowCheck11207 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow11207 := by decide +kernel

theorem rowCheck11207 : row11207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11207 := by decide +kernel

theorem rowEval11207 (x : Key → ℝ) : Integer.Sparse.eval row11207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11207, Integer.Sparse.eval_collectBalanced, rawRowCheck11207]

theorem rawRowCheck11208 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow11208 := by decide +kernel

theorem rowCheck11208 : row11208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11208 := by decide +kernel

theorem rowEval11208 (x : Key → ℝ) : Integer.Sparse.eval row11208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11208, Integer.Sparse.eval_collectBalanced, rawRowCheck11208]

theorem rawRowCheck11209 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow11209 := by decide +kernel

theorem rowCheck11209 : row11209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11209 := by decide +kernel

theorem rowEval11209 (x : Key → ℝ) : Integer.Sparse.eval row11209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11209, Integer.Sparse.eval_collectBalanced, rawRowCheck11209]

theorem rawRowCheck11210 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form14 = rawRow11210 := by decide +kernel

theorem rowCheck11210 : row11210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11210 := by decide +kernel

theorem rowEval11210 (x : Key → ℝ) : Integer.Sparse.eval row11210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11210, Integer.Sparse.eval_collectBalanced, rawRowCheck11210]

theorem rawRowCheck11211 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form14 = rawRow11211 := by decide +kernel

theorem rowCheck11211 : row11211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11211 := by decide +kernel

theorem rowEval11211 (x : Key → ℝ) : Integer.Sparse.eval row11211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11211, Integer.Sparse.eval_collectBalanced, rawRowCheck11211]

theorem rawRowCheck11212 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form14 = rawRow11212 := by decide +kernel

theorem rowCheck11212 : row11212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11212 := by decide +kernel

theorem rowEval11212 (x : Key → ℝ) : Integer.Sparse.eval row11212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11212, Integer.Sparse.eval_collectBalanced, rawRowCheck11212]

theorem rawRowCheck11213 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form14 = rawRow11213 := by decide +kernel

theorem rowCheck11213 : row11213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11213 := by decide +kernel

theorem rowEval11213 (x : Key → ℝ) : Integer.Sparse.eval row11213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11213, Integer.Sparse.eval_collectBalanced, rawRowCheck11213]

theorem rawRowCheck11214 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form14 = rawRow11214 := by decide +kernel

theorem rowCheck11214 : row11214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11214 := by decide +kernel

theorem rowEval11214 (x : Key → ℝ) : Integer.Sparse.eval row11214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11214, Integer.Sparse.eval_collectBalanced, rawRowCheck11214]

theorem rawRowCheck11215 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form14 = rawRow11215 := by decide +kernel

theorem rowCheck11215 : row11215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11215 := by decide +kernel

theorem rowEval11215 (x : Key → ℝ) : Integer.Sparse.eval row11215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11215, Integer.Sparse.eval_collectBalanced, rawRowCheck11215]

theorem rawRowCheck11216 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form14 = rawRow11216 := by decide +kernel

theorem rowCheck11216 : row11216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11216 := by decide +kernel

theorem rowEval11216 (x : Key → ℝ) : Integer.Sparse.eval row11216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11216, Integer.Sparse.eval_collectBalanced, rawRowCheck11216]

theorem rawRowCheck11217 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form14 = rawRow11217 := by decide +kernel

theorem rowCheck11217 : row11217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11217 := by decide +kernel

theorem rowEval11217 (x : Key → ℝ) : Integer.Sparse.eval row11217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11217, Integer.Sparse.eval_collectBalanced, rawRowCheck11217]

theorem rawRowCheck11218 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form14 = rawRow11218 := by decide +kernel

theorem rowCheck11218 : row11218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11218 := by decide +kernel

theorem rowEval11218 (x : Key → ℝ) : Integer.Sparse.eval row11218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11218, Integer.Sparse.eval_collectBalanced, rawRowCheck11218]

theorem rawRowCheck11219 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form14 = rawRow11219 := by decide +kernel

theorem rowCheck11219 : row11219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11219 := by decide +kernel

theorem rowEval11219 (x : Key → ℝ) : Integer.Sparse.eval row11219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11219, Integer.Sparse.eval_collectBalanced, rawRowCheck11219]

theorem rawRowCheck11220 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form14 = rawRow11220 := by decide +kernel

theorem rowCheck11220 : row11220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11220 := by decide +kernel

theorem rowEval11220 (x : Key → ℝ) : Integer.Sparse.eval row11220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11220, Integer.Sparse.eval_collectBalanced, rawRowCheck11220]

theorem rawRowCheck11221 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form14 = rawRow11221 := by decide +kernel

theorem rowCheck11221 : row11221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11221 := by decide +kernel

theorem rowEval11221 (x : Key → ℝ) : Integer.Sparse.eval row11221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11221, Integer.Sparse.eval_collectBalanced, rawRowCheck11221]

theorem rawRowCheck11222 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form14 = rawRow11222 := by decide +kernel

theorem rowCheck11222 : row11222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11222 := by decide +kernel

theorem rowEval11222 (x : Key → ℝ) : Integer.Sparse.eval row11222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11222, Integer.Sparse.eval_collectBalanced, rawRowCheck11222]

theorem rawRowCheck11223 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form14 = rawRow11223 := by decide +kernel

theorem rowCheck11223 : row11223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11223 := by decide +kernel

theorem rowEval11223 (x : Key → ℝ) : Integer.Sparse.eval row11223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11223, Integer.Sparse.eval_collectBalanced, rawRowCheck11223]

theorem rawRowCheck11224 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form14 = rawRow11224 := by decide +kernel

theorem rowCheck11224 : row11224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11224 := by decide +kernel

theorem rowEval11224 (x : Key → ℝ) : Integer.Sparse.eval row11224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11224, Integer.Sparse.eval_collectBalanced, rawRowCheck11224]

theorem rawRowCheck11225 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow11225 := by decide +kernel

theorem rowCheck11225 : row11225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11225 := by decide +kernel

theorem rowEval11225 (x : Key → ℝ) : Integer.Sparse.eval row11225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11225, Integer.Sparse.eval_collectBalanced, rawRowCheck11225]

theorem rawRowCheck11226 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow11226 := by decide +kernel

theorem rowCheck11226 : row11226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11226 := by decide +kernel

theorem rowEval11226 (x : Key → ℝ) : Integer.Sparse.eval row11226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11226, Integer.Sparse.eval_collectBalanced, rawRowCheck11226]

theorem rawRowCheck11227 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow11227 := by decide +kernel

theorem rowCheck11227 : row11227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11227 := by decide +kernel

theorem rowEval11227 (x : Key → ℝ) : Integer.Sparse.eval row11227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11227, Integer.Sparse.eval_collectBalanced, rawRowCheck11227]

theorem rawRowCheck11228 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form14 = rawRow11228 := by decide +kernel

theorem rowCheck11228 : row11228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11228 := by decide +kernel

theorem rowEval11228 (x : Key → ℝ) : Integer.Sparse.eval row11228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11228, Integer.Sparse.eval_collectBalanced, rawRowCheck11228]

theorem rawRowCheck11229 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form14 = rawRow11229 := by decide +kernel

theorem rowCheck11229 : row11229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11229 := by decide +kernel

theorem rowEval11229 (x : Key → ℝ) : Integer.Sparse.eval row11229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11229, Integer.Sparse.eval_collectBalanced, rawRowCheck11229]

theorem rawRowCheck11230 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form14 = rawRow11230 := by decide +kernel

theorem rowCheck11230 : row11230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11230 := by decide +kernel

theorem rowEval11230 (x : Key → ℝ) : Integer.Sparse.eval row11230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11230, Integer.Sparse.eval_collectBalanced, rawRowCheck11230]

theorem rawRowCheck11231 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form14 = rawRow11231 := by decide +kernel

theorem rowCheck11231 : row11231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11231 := by decide +kernel

theorem rowEval11231 (x : Key → ℝ) : Integer.Sparse.eval row11231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11231, Integer.Sparse.eval_collectBalanced, rawRowCheck11231]

theorem rawRowCheck11232 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form14 = rawRow11232 := by decide +kernel

theorem rowCheck11232 : row11232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11232 := by decide +kernel

theorem rowEval11232 (x : Key → ℝ) : Integer.Sparse.eval row11232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11232, Integer.Sparse.eval_collectBalanced, rawRowCheck11232]

theorem rawRowCheck11233 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form14 = rawRow11233 := by decide +kernel

theorem rowCheck11233 : row11233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11233 := by decide +kernel

theorem rowEval11233 (x : Key → ℝ) : Integer.Sparse.eval row11233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11233, Integer.Sparse.eval_collectBalanced, rawRowCheck11233]

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

theorem entryCheck21_14 : entry21_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_14 k)) := by decide +kernel

theorem rowsSound21_14 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval11198 x
  · exact rowEval11199 x
  · exact rowEval11200 x
  · exact rowEval11201 x
  · exact rowEval11202 x
  · exact rowEval11203 x
  · exact rowEval11204 x
  · exact rowEval11205 x
  · exact rowEval11206 x
  · exact rowEval11207 x
  · exact rowEval11208 x
  · exact rowEval11209 x
  · exact rowEval11210 x
  · exact rowEval11211 x
  · exact rowEval11212 x
  · exact rowEval11213 x
  · exact rowEval11214 x
  · exact rowEval11215 x
  · exact rowEval11216 x
  · exact rowEval11217 x
  · exact rowEval11218 x
  · exact rowEval11219 x
  · exact rowEval11220 x
  · exact rowEval11221 x
  · exact rowEval11222 x
  · exact rowEval11223 x
  · exact rowEval11224 x
  · exact rowEval11225 x
  · exact rowEval11226 x
  · exact rowEval11227 x
  · exact rowEval11228 x
  · exact rowEval11229 x
  · exact rowEval11230 x
  · exact rowEval11231 x
  · exact rowEval11232 x
  · exact rowEval11233 x

theorem entryEval21_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_14 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck21_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_14]

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

theorem rawRowCheck11654 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form14 = rawRow11654 := by decide +kernel

theorem rowCheck11654 : row11654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11654 := by decide +kernel

theorem rowEval11654 (x : Key → ℝ) : Integer.Sparse.eval row11654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11654, Integer.Sparse.eval_collectBalanced, rawRowCheck11654]

theorem rawRowCheck11655 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form14 = rawRow11655 := by decide +kernel

theorem rowCheck11655 : row11655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11655 := by decide +kernel

theorem rowEval11655 (x : Key → ℝ) : Integer.Sparse.eval row11655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11655, Integer.Sparse.eval_collectBalanced, rawRowCheck11655]

theorem rawRowCheck11656 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form14 = rawRow11656 := by decide +kernel

theorem rowCheck11656 : row11656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11656 := by decide +kernel

theorem rowEval11656 (x : Key → ℝ) : Integer.Sparse.eval row11656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11656, Integer.Sparse.eval_collectBalanced, rawRowCheck11656]

theorem rawRowCheck11657 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form14 = rawRow11657 := by decide +kernel

theorem rowCheck11657 : row11657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11657 := by decide +kernel

theorem rowEval11657 (x : Key → ℝ) : Integer.Sparse.eval row11657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11657, Integer.Sparse.eval_collectBalanced, rawRowCheck11657]

theorem rawRowCheck11658 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form14 = rawRow11658 := by decide +kernel

theorem rowCheck11658 : row11658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11658 := by decide +kernel

theorem rowEval11658 (x : Key → ℝ) : Integer.Sparse.eval row11658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11658, Integer.Sparse.eval_collectBalanced, rawRowCheck11658]

theorem rawRowCheck11659 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form14 = rawRow11659 := by decide +kernel

theorem rowCheck11659 : row11659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11659 := by decide +kernel

theorem rowEval11659 (x : Key → ℝ) : Integer.Sparse.eval row11659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11659, Integer.Sparse.eval_collectBalanced, rawRowCheck11659]

theorem rawRowCheck11660 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form14 = rawRow11660 := by decide +kernel

theorem rowCheck11660 : row11660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11660 := by decide +kernel

theorem rowEval11660 (x : Key → ℝ) : Integer.Sparse.eval row11660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11660, Integer.Sparse.eval_collectBalanced, rawRowCheck11660]

theorem rawRowCheck11661 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form14 = rawRow11661 := by decide +kernel

theorem rowCheck11661 : row11661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11661 := by decide +kernel

theorem rowEval11661 (x : Key → ℝ) : Integer.Sparse.eval row11661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11661, Integer.Sparse.eval_collectBalanced, rawRowCheck11661]

theorem rawRowCheck11662 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form14 = rawRow11662 := by decide +kernel

theorem rowCheck11662 : row11662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11662 := by decide +kernel

theorem rowEval11662 (x : Key → ℝ) : Integer.Sparse.eval row11662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11662, Integer.Sparse.eval_collectBalanced, rawRowCheck11662]

theorem rawRowCheck11663 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow11663 := by decide +kernel

theorem rowCheck11663 : row11663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11663 := by decide +kernel

theorem rowEval11663 (x : Key → ℝ) : Integer.Sparse.eval row11663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11663, Integer.Sparse.eval_collectBalanced, rawRowCheck11663]

theorem rawRowCheck11664 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow11664 := by decide +kernel

theorem rowCheck11664 : row11664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11664 := by decide +kernel

theorem rowEval11664 (x : Key → ℝ) : Integer.Sparse.eval row11664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11664, Integer.Sparse.eval_collectBalanced, rawRowCheck11664]

theorem rawRowCheck11665 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow11665 := by decide +kernel

theorem rowCheck11665 : row11665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11665 := by decide +kernel

theorem rowEval11665 (x : Key → ℝ) : Integer.Sparse.eval row11665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11665, Integer.Sparse.eval_collectBalanced, rawRowCheck11665]

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

theorem entryCheck22_14 : entry22_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_14 k)) := by decide +kernel

theorem rowsSound22_14 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval11654 x
  · exact rowEval11655 x
  · exact rowEval11656 x
  · exact rowEval11657 x
  · exact rowEval11658 x
  · exact rowEval11659 x
  · exact rowEval11660 x
  · exact rowEval11661 x
  · exact rowEval11662 x
  · exact rowEval11663 x
  · exact rowEval11664 x
  · exact rowEval11665 x
  · exact rowEval11198 x
  · exact rowEval11199 x
  · exact rowEval11200 x
  · exact rowEval11201 x
  · exact rowEval11202 x
  · exact rowEval11203 x
  · exact rowEval11204 x
  · exact rowEval11205 x
  · exact rowEval11206 x
  · exact rowEval11207 x
  · exact rowEval11208 x
  · exact rowEval11209 x
  · exact rowEval11210 x
  · exact rowEval11211 x
  · exact rowEval11212 x
  · exact rowEval11213 x
  · exact rowEval11214 x
  · exact rowEval11215 x
  · exact rowEval11216 x
  · exact rowEval11217 x
  · exact rowEval11218 x
  · exact rowEval11219 x
  · exact rowEval11220 x
  · exact rowEval11221 x

theorem entryEval22_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_14 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck22_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_14]

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

theorem rawRowCheck12026 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12026 := by decide +kernel

theorem rowCheck12026 : row12026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12026 := by decide +kernel

theorem rowEval12026 (x : Key → ℝ) : Integer.Sparse.eval row12026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12026, Integer.Sparse.eval_collectBalanced, rawRowCheck12026]

theorem rawRowCheck12027 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12027 := by decide +kernel

theorem rowCheck12027 : row12027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12027 := by decide +kernel

theorem rowEval12027 (x : Key → ℝ) : Integer.Sparse.eval row12027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12027, Integer.Sparse.eval_collectBalanced, rawRowCheck12027]

theorem rawRowCheck12028 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12028 := by decide +kernel

theorem rowCheck12028 : row12028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12028 := by decide +kernel

theorem rowEval12028 (x : Key → ℝ) : Integer.Sparse.eval row12028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12028, Integer.Sparse.eval_collectBalanced, rawRowCheck12028]

theorem rawRowCheck12029 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form14 = rawRow12029 := by decide +kernel

theorem rowCheck12029 : row12029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12029 := by decide +kernel

theorem rowEval12029 (x : Key → ℝ) : Integer.Sparse.eval row12029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12029, Integer.Sparse.eval_collectBalanced, rawRowCheck12029]

theorem rawRowCheck12030 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form14 = rawRow12030 := by decide +kernel

theorem rowCheck12030 : row12030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12030 := by decide +kernel

theorem rowEval12030 (x : Key → ℝ) : Integer.Sparse.eval row12030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12030, Integer.Sparse.eval_collectBalanced, rawRowCheck12030]

theorem rawRowCheck12031 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form14 = rawRow12031 := by decide +kernel

theorem rowCheck12031 : row12031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12031 := by decide +kernel

theorem rowEval12031 (x : Key → ℝ) : Integer.Sparse.eval row12031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12031, Integer.Sparse.eval_collectBalanced, rawRowCheck12031]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck12032 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12032 := by decide +kernel

theorem rowCheck12032 : row12032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12032 := by decide +kernel

theorem rowEval12032 (x : Key → ℝ) : Integer.Sparse.eval row12032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12032, Integer.Sparse.eval_collectBalanced, rawRowCheck12032]

theorem rawRowCheck12033 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12033 := by decide +kernel

theorem rowCheck12033 : row12033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12033 := by decide +kernel

theorem rowEval12033 (x : Key → ℝ) : Integer.Sparse.eval row12033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12033, Integer.Sparse.eval_collectBalanced, rawRowCheck12033]

theorem rawRowCheck12034 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12034 := by decide +kernel

theorem rowCheck12034 : row12034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12034 := by decide +kernel

theorem rowEval12034 (x : Key → ℝ) : Integer.Sparse.eval row12034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12034, Integer.Sparse.eval_collectBalanced, rawRowCheck12034]

theorem rawRowCheck12035 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14 = rawRow12035 := by decide +kernel

theorem rowCheck12035 : row12035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12035 := by decide +kernel

theorem rowEval12035 (x : Key → ℝ) : Integer.Sparse.eval row12035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12035, Integer.Sparse.eval_collectBalanced, rawRowCheck12035]

theorem rawRowCheck12036 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14 = rawRow12036 := by decide +kernel

theorem rowCheck12036 : row12036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12036 := by decide +kernel

theorem rowEval12036 (x : Key → ℝ) : Integer.Sparse.eval row12036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12036, Integer.Sparse.eval_collectBalanced, rawRowCheck12036]

theorem rawRowCheck12037 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14 = rawRow12037 := by decide +kernel

theorem rowCheck12037 : row12037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12037 := by decide +kernel

theorem rowEval12037 (x : Key → ℝ) : Integer.Sparse.eval row12037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12037, Integer.Sparse.eval_collectBalanced, rawRowCheck12037]

theorem rawRowCheck12038 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14 = rawRow12038 := by decide +kernel

theorem rowCheck12038 : row12038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12038 := by decide +kernel

theorem rowEval12038 (x : Key → ℝ) : Integer.Sparse.eval row12038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12038, Integer.Sparse.eval_collectBalanced, rawRowCheck12038]

theorem rawRowCheck12039 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14 = rawRow12039 := by decide +kernel

theorem rowCheck12039 : row12039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12039 := by decide +kernel

theorem rowEval12039 (x : Key → ℝ) : Integer.Sparse.eval row12039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12039, Integer.Sparse.eval_collectBalanced, rawRowCheck12039]

theorem rawRowCheck12040 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14 = rawRow12040 := by decide +kernel

theorem rowCheck12040 : row12040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12040 := by decide +kernel

theorem rowEval12040 (x : Key → ℝ) : Integer.Sparse.eval row12040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12040, Integer.Sparse.eval_collectBalanced, rawRowCheck12040]

theorem rawRowCheck12041 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14 = rawRow12041 := by decide +kernel

theorem rowCheck12041 : row12041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12041 := by decide +kernel

theorem rowEval12041 (x : Key → ℝ) : Integer.Sparse.eval row12041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12041, Integer.Sparse.eval_collectBalanced, rawRowCheck12041]

theorem rawRowCheck12042 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14 = rawRow12042 := by decide +kernel

theorem rowCheck12042 : row12042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12042 := by decide +kernel

theorem rowEval12042 (x : Key → ℝ) : Integer.Sparse.eval row12042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12042, Integer.Sparse.eval_collectBalanced, rawRowCheck12042]

theorem rawRowCheck12043 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14 = rawRow12043 := by decide +kernel

theorem rowCheck12043 : row12043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12043 := by decide +kernel

theorem rowEval12043 (x : Key → ℝ) : Integer.Sparse.eval row12043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12043, Integer.Sparse.eval_collectBalanced, rawRowCheck12043]

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

theorem rawRowCheck12276 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form14 = rawRow12276 := by decide +kernel

theorem rowCheck12276 : row12276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12276 := by decide +kernel

theorem rowEval12276 (x : Key → ℝ) : Integer.Sparse.eval row12276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12276, Integer.Sparse.eval_collectBalanced, rawRowCheck12276]

theorem rawRowCheck12277 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow12277 := by decide +kernel

theorem rowCheck12277 : row12277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12277 := by decide +kernel

theorem rowEval12277 (x : Key → ℝ) : Integer.Sparse.eval row12277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12277, Integer.Sparse.eval_collectBalanced, rawRowCheck12277]

theorem rawRowCheck12278 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form14 = rawRow12278 := by decide +kernel

theorem rowCheck12278 : row12278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12278 := by decide +kernel

theorem rowEval12278 (x : Key → ℝ) : Integer.Sparse.eval row12278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12278, Integer.Sparse.eval_collectBalanced, rawRowCheck12278]

theorem rawRowCheck12279 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form14 = rawRow12279 := by decide +kernel

theorem rowCheck12279 : row12279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12279 := by decide +kernel

theorem rowEval12279 (x : Key → ℝ) : Integer.Sparse.eval row12279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12279, Integer.Sparse.eval_collectBalanced, rawRowCheck12279]

theorem rawRowCheck12280 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form14 = rawRow12280 := by decide +kernel

theorem rowCheck12280 : row12280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12280 := by decide +kernel

theorem rowEval12280 (x : Key → ℝ) : Integer.Sparse.eval row12280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12280, Integer.Sparse.eval_collectBalanced, rawRowCheck12280]

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

theorem entryCheck23_14 : entry23_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_14 k)) := by decide +kernel

theorem rowsSound23_14 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12026 x
  · exact rowEval12027 x
  · exact rowEval12028 x
  · exact rowEval12029 x
  · exact rowEval12030 x
  · exact rowEval12031 x
  · exact rowEval12032 x
  · exact rowEval12033 x
  · exact rowEval12034 x
  · exact rowEval12035 x
  · exact rowEval12036 x
  · exact rowEval12037 x
  · exact rowEval12038 x
  · exact rowEval12039 x
  · exact rowEval12040 x
  · exact rowEval12041 x
  · exact rowEval12042 x
  · exact rowEval12043 x

theorem entryEval23_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_14 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck23_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_14]

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

theorem entryCheck24_14 : entry24_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_14 k)) := by decide +kernel

theorem rowsSound24_14 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12276 x
  · exact rowEval12277 x
  · exact rowEval12278 x
  · exact rowEval12279 x
  · exact rowEval12280 x

theorem entryEval24_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_14 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck24_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_14]

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

theorem rawRowCheck12875 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12875 := by decide +kernel

theorem rowCheck12875 : row12875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12875 := by decide +kernel

theorem rowEval12875 (x : Key → ℝ) : Integer.Sparse.eval row12875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12875, Integer.Sparse.eval_collectBalanced, rawRowCheck12875]

theorem rawRowCheck12876 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12876 := by decide +kernel

theorem rowCheck12876 : row12876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12876 := by decide +kernel

theorem rowEval12876 (x : Key → ℝ) : Integer.Sparse.eval row12876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12876, Integer.Sparse.eval_collectBalanced, rawRowCheck12876]

theorem rawRowCheck12877 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12877 := by decide +kernel

theorem rowCheck12877 : row12877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12877 := by decide +kernel

theorem rowEval12877 (x : Key → ℝ) : Integer.Sparse.eval row12877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12877, Integer.Sparse.eval_collectBalanced, rawRowCheck12877]

theorem rawRowCheck12878 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form14 = rawRow12878 := by decide +kernel

theorem rowCheck12878 : row12878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12878 := by decide +kernel

theorem rowEval12878 (x : Key → ℝ) : Integer.Sparse.eval row12878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12878, Integer.Sparse.eval_collectBalanced, rawRowCheck12878]

theorem rawRowCheck12879 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form14 = rawRow12879 := by decide +kernel

theorem rowCheck12879 : row12879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12879 := by decide +kernel

theorem rowEval12879 (x : Key → ℝ) : Integer.Sparse.eval row12879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12879, Integer.Sparse.eval_collectBalanced, rawRowCheck12879]

theorem rawRowCheck12880 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form14 = rawRow12880 := by decide +kernel

theorem rowCheck12880 : row12880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12880 := by decide +kernel

theorem rowEval12880 (x : Key → ℝ) : Integer.Sparse.eval row12880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12880, Integer.Sparse.eval_collectBalanced, rawRowCheck12880]

theorem rawRowCheck12881 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow12881 := by decide +kernel

theorem rowCheck12881 : row12881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12881 := by decide +kernel

theorem rowEval12881 (x : Key → ℝ) : Integer.Sparse.eval row12881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12881, Integer.Sparse.eval_collectBalanced, rawRowCheck12881]

theorem rawRowCheck12882 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow12882 := by decide +kernel

theorem rowCheck12882 : row12882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12882 := by decide +kernel

theorem rowEval12882 (x : Key → ℝ) : Integer.Sparse.eval row12882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12882, Integer.Sparse.eval_collectBalanced, rawRowCheck12882]

theorem rawRowCheck12883 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow12883 := by decide +kernel

theorem rowCheck12883 : row12883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12883 := by decide +kernel

theorem rowEval12883 (x : Key → ℝ) : Integer.Sparse.eval row12883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12883, Integer.Sparse.eval_collectBalanced, rawRowCheck12883]

theorem rawRowCheck12884 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow12884 := by decide +kernel

theorem rowCheck12884 : row12884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12884 := by decide +kernel

theorem rowEval12884 (x : Key → ℝ) : Integer.Sparse.eval row12884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12884, Integer.Sparse.eval_collectBalanced, rawRowCheck12884]

theorem rawRowCheck12885 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow12885 := by decide +kernel

theorem rowCheck12885 : row12885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12885 := by decide +kernel

theorem rowEval12885 (x : Key → ℝ) : Integer.Sparse.eval row12885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12885, Integer.Sparse.eval_collectBalanced, rawRowCheck12885]

theorem rawRowCheck12886 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow12886 := by decide +kernel

theorem rowCheck12886 : row12886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12886 := by decide +kernel

theorem rowEval12886 (x : Key → ℝ) : Integer.Sparse.eval row12886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12886, Integer.Sparse.eval_collectBalanced, rawRowCheck12886]

theorem rawRowCheck12887 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form14 = rawRow12887 := by decide +kernel

theorem rowCheck12887 : row12887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12887 := by decide +kernel

theorem rowEval12887 (x : Key → ℝ) : Integer.Sparse.eval row12887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12887, Integer.Sparse.eval_collectBalanced, rawRowCheck12887]

theorem rawRowCheck12888 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form14 = rawRow12888 := by decide +kernel

theorem rowCheck12888 : row12888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12888 := by decide +kernel

theorem rowEval12888 (x : Key → ℝ) : Integer.Sparse.eval row12888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12888, Integer.Sparse.eval_collectBalanced, rawRowCheck12888]

theorem rawRowCheck12889 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form14 = rawRow12889 := by decide +kernel

theorem rowCheck12889 : row12889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12889 := by decide +kernel

theorem rowEval12889 (x : Key → ℝ) : Integer.Sparse.eval row12889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12889, Integer.Sparse.eval_collectBalanced, rawRowCheck12889]

theorem rawRowCheck12890 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form14 = rawRow12890 := by decide +kernel

theorem rowCheck12890 : row12890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12890 := by decide +kernel

theorem rowEval12890 (x : Key → ℝ) : Integer.Sparse.eval row12890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12890, Integer.Sparse.eval_collectBalanced, rawRowCheck12890]

theorem rawRowCheck12891 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form14 = rawRow12891 := by decide +kernel

theorem rowCheck12891 : row12891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12891 := by decide +kernel

theorem rowEval12891 (x : Key → ℝ) : Integer.Sparse.eval row12891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12891, Integer.Sparse.eval_collectBalanced, rawRowCheck12891]

theorem rawRowCheck12892 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form14 = rawRow12892 := by decide +kernel

theorem rowCheck12892 : row12892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12892 := by decide +kernel

theorem rowEval12892 (x : Key → ℝ) : Integer.Sparse.eval row12892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12892, Integer.Sparse.eval_collectBalanced, rawRowCheck12892]

theorem rawRowCheck12893 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form14 = rawRow12893 := by decide +kernel

theorem rowCheck12893 : row12893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12893 := by decide +kernel

theorem rowEval12893 (x : Key → ℝ) : Integer.Sparse.eval row12893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12893, Integer.Sparse.eval_collectBalanced, rawRowCheck12893]

theorem rawRowCheck12894 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form14 = rawRow12894 := by decide +kernel

theorem rowCheck12894 : row12894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12894 := by decide +kernel

theorem rowEval12894 (x : Key → ℝ) : Integer.Sparse.eval row12894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12894, Integer.Sparse.eval_collectBalanced, rawRowCheck12894]

theorem rawRowCheck12895 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form14 = rawRow12895 := by decide +kernel

theorem rowCheck12895 : row12895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12895 := by decide +kernel

theorem rowEval12895 (x : Key → ℝ) : Integer.Sparse.eval row12895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12895, Integer.Sparse.eval_collectBalanced, rawRowCheck12895]

theorem rawRowCheck12896 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow12896 := by decide +kernel

theorem rowCheck12896 : row12896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12896 := by decide +kernel

theorem rowEval12896 (x : Key → ℝ) : Integer.Sparse.eval row12896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12896, Integer.Sparse.eval_collectBalanced, rawRowCheck12896]

theorem rawRowCheck12897 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow12897 := by decide +kernel

theorem rowCheck12897 : row12897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12897 := by decide +kernel

theorem rowEval12897 (x : Key → ℝ) : Integer.Sparse.eval row12897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12897, Integer.Sparse.eval_collectBalanced, rawRowCheck12897]

theorem rawRowCheck12898 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow12898 := by decide +kernel

theorem rowCheck12898 : row12898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12898 := by decide +kernel

theorem rowEval12898 (x : Key → ℝ) : Integer.Sparse.eval row12898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12898, Integer.Sparse.eval_collectBalanced, rawRowCheck12898]

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

theorem entryCheck26_14 : entry26_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_14 k)) := by decide +kernel

theorem rowsSound26_14 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12875 x
  · exact rowEval12876 x
  · exact rowEval12877 x
  · exact rowEval12878 x
  · exact rowEval12879 x
  · exact rowEval12880 x
  · exact rowEval12881 x
  · exact rowEval12882 x
  · exact rowEval12883 x
  · exact rowEval12884 x
  · exact rowEval12885 x
  · exact rowEval12886 x
  · exact rowEval12887 x
  · exact rowEval12888 x
  · exact rowEval12889 x
  · exact rowEval12890 x
  · exact rowEval12891 x
  · exact rowEval12892 x
  · exact rowEval12893 x
  · exact rowEval12894 x
  · exact rowEval12895 x
  · exact rowEval12896 x
  · exact rowEval12897 x
  · exact rowEval12898 x

theorem entryEval26_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_14 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck26_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_14]

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

theorem entryEvalRow14_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 14 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 14).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval14_0 B hB
  · exact entryEval14_1 B hB
  · exact entryEval14_2 B hB
  · exact entryEval14_3 B hB
  · exact entryEval14_4 B hB
  · exact entryEval14_5 B hB
  · exact entryEval14_6 B hB
  · exact entryEval14_7 B hB
  · exact entryEval14_8 B hB
  · exact entryEval14_9 B hB
  · exact entryEval14_10 B hB
  · exact entryEval14_11 B hB
  · exact entryEval14_12 B hB
  · exact entryEval14_13 B hB
  · exact entryEval14_14 B hB
  · exact (entryEval15_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e_oai
