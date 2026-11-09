-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:12:46.232271+00:00
-- url     : https://prove2.me/submissions/389c863e-a607-467e-ab45-55ef2b3bb951

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

theorem rawRowCheck8761 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8761 := by decide +kernel

theorem rowCheck8761 : row8761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8761 := by decide +kernel

theorem rowEval8761 (x : Key → ℝ) : Integer.Sparse.eval row8761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8761, Integer.Sparse.eval_collectBalanced, rawRowCheck8761]

theorem rawRowCheck8762 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow8762 := by decide +kernel

theorem rowCheck8762 : row8762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8762 := by decide +kernel

theorem rowEval8762 (x : Key → ℝ) : Integer.Sparse.eval row8762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8762, Integer.Sparse.eval_collectBalanced, rawRowCheck8762]

theorem rawRowCheck8763 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow8763 := by decide +kernel

theorem rowCheck8763 : row8763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8763 := by decide +kernel

theorem rowEval8763 (x : Key → ℝ) : Integer.Sparse.eval row8763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8763, Integer.Sparse.eval_collectBalanced, rawRowCheck8763]

theorem rawRowCheck8764 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow8764 := by decide +kernel

theorem rowCheck8764 : row8764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8764 := by decide +kernel

theorem rowEval8764 (x : Key → ℝ) : Integer.Sparse.eval row8764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck8764, Integer.Sparse.eval_collectBalanced, rawRowCheck8764]

theorem rawRowCheck8765 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8765 := by decide +kernel

theorem rowCheck8765 : row8765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8765 := by decide +kernel

theorem rowEval8765 (x : Key → ℝ) : Integer.Sparse.eval row8765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8765, Integer.Sparse.eval_collectBalanced, rawRowCheck8765]

theorem rawRowCheck8766 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow8766 := by decide +kernel

theorem rowCheck8766 : row8766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8766 := by decide +kernel

theorem rowEval8766 (x : Key → ℝ) : Integer.Sparse.eval row8766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8766, Integer.Sparse.eval_collectBalanced, rawRowCheck8766]

theorem rawRowCheck8767 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow8767 := by decide +kernel

theorem rowCheck8767 : row8767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8767 := by decide +kernel

theorem rowEval8767 (x : Key → ℝ) : Integer.Sparse.eval row8767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8767, Integer.Sparse.eval_collectBalanced, rawRowCheck8767]

theorem rawRowCheck8768 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow8768 := by decide +kernel

theorem rowCheck8768 : row8768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8768 := by decide +kernel

theorem rowEval8768 (x : Key → ℝ) : Integer.Sparse.eval row8768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck8768, Integer.Sparse.eval_collectBalanced, rawRowCheck8768]

theorem rawRowCheck8769 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8769 := by decide +kernel

theorem rowCheck8769 : row8769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8769 := by decide +kernel

theorem rowEval8769 (x : Key → ℝ) : Integer.Sparse.eval row8769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8769, Integer.Sparse.eval_collectBalanced, rawRowCheck8769]

theorem rawRowCheck8770 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow8770 := by decide +kernel

theorem rowCheck8770 : row8770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8770 := by decide +kernel

theorem rowEval8770 (x : Key → ℝ) : Integer.Sparse.eval row8770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8770, Integer.Sparse.eval_collectBalanced, rawRowCheck8770]

theorem rawRowCheck8771 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow8771 := by decide +kernel

theorem rowCheck8771 : row8771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8771 := by decide +kernel

theorem rowEval8771 (x : Key → ℝ) : Integer.Sparse.eval row8771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8771, Integer.Sparse.eval_collectBalanced, rawRowCheck8771]

theorem rawRowCheck8772 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow8772 := by decide +kernel

theorem rowCheck8772 : row8772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8772 := by decide +kernel

theorem rowEval8772 (x : Key → ℝ) : Integer.Sparse.eval row8772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck8772, Integer.Sparse.eval_collectBalanced, rawRowCheck8772]

theorem rawRowCheck8773 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8773 := by decide +kernel

theorem rowCheck8773 : row8773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8773 := by decide +kernel

theorem rowEval8773 (x : Key → ℝ) : Integer.Sparse.eval row8773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8773, Integer.Sparse.eval_collectBalanced, rawRowCheck8773]

theorem rawRowCheck8774 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow8774 := by decide +kernel

theorem rowCheck8774 : row8774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8774 := by decide +kernel

theorem rowEval8774 (x : Key → ℝ) : Integer.Sparse.eval row8774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8774, Integer.Sparse.eval_collectBalanced, rawRowCheck8774]

theorem rawRowCheck8775 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow8775 := by decide +kernel

theorem rowCheck8775 : row8775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8775 := by decide +kernel

theorem rowEval8775 (x : Key → ℝ) : Integer.Sparse.eval row8775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8775, Integer.Sparse.eval_collectBalanced, rawRowCheck8775]

theorem rawRowCheck8776 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow8776 := by decide +kernel

theorem rowCheck8776 : row8776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8776 := by decide +kernel

theorem rowEval8776 (x : Key → ℝ) : Integer.Sparse.eval row8776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck8776, Integer.Sparse.eval_collectBalanced, rawRowCheck8776]

theorem rawRowCheck8777 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form5 = rawRow8777 := by decide +kernel

theorem rowCheck8777 : row8777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8777 := by decide +kernel

theorem rowEval8777 (x : Key → ℝ) : Integer.Sparse.eval row8777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8777, Integer.Sparse.eval_collectBalanced, rawRowCheck8777]

theorem rawRowCheck8778 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form5 = rawRow8778 := by decide +kernel

theorem rowCheck8778 : row8778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8778 := by decide +kernel

theorem rowEval8778 (x : Key → ℝ) : Integer.Sparse.eval row8778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8778, Integer.Sparse.eval_collectBalanced, rawRowCheck8778]

theorem rawRowCheck8779 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form5 = rawRow8779 := by decide +kernel

theorem rowCheck8779 : row8779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8779 := by decide +kernel

theorem rowEval8779 (x : Key → ℝ) : Integer.Sparse.eval row8779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8779, Integer.Sparse.eval_collectBalanced, rawRowCheck8779]

theorem rawRowCheck8780 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8780 := by decide +kernel

theorem rowCheck8780 : row8780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8780 := by decide +kernel

theorem rowEval8780 (x : Key → ℝ) : Integer.Sparse.eval row8780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8780, Integer.Sparse.eval_collectBalanced, rawRowCheck8780]

theorem rawRowCheck8781 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8781 := by decide +kernel

theorem rowCheck8781 : row8781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8781 := by decide +kernel

theorem rowEval8781 (x : Key → ℝ) : Integer.Sparse.eval row8781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8781, Integer.Sparse.eval_collectBalanced, rawRowCheck8781]

theorem rawRowCheck8782 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form5 = rawRow8782 := by decide +kernel

theorem rowCheck8782 : row8782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8782 := by decide +kernel

theorem rowEval8782 (x : Key → ℝ) : Integer.Sparse.eval row8782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8782, Integer.Sparse.eval_collectBalanced, rawRowCheck8782]

theorem rawRowCheck8783 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form5 = rawRow8783 := by decide +kernel

theorem rowCheck8783 : row8783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8783 := by decide +kernel

theorem rowEval8783 (x : Key → ℝ) : Integer.Sparse.eval row8783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8783, Integer.Sparse.eval_collectBalanced, rawRowCheck8783]

theorem rawRowCheck8784 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form5 = rawRow8784 := by decide +kernel

theorem rowCheck8784 : row8784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8784 := by decide +kernel

theorem rowEval8784 (x : Key → ℝ) : Integer.Sparse.eval row8784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck8784, Integer.Sparse.eval_collectBalanced, rawRowCheck8784]

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

theorem rawRowCheck8793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8793 := by decide +kernel

theorem rowCheck8793 : row8793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8793 := by decide +kernel

theorem rowEval8793 (x : Key → ℝ) : Integer.Sparse.eval row8793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8793, Integer.Sparse.eval_collectBalanced, rawRowCheck8793]

theorem rawRowCheck8794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8794 := by decide +kernel

theorem rowCheck8794 : row8794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8794 := by decide +kernel

theorem rowEval8794 (x : Key → ℝ) : Integer.Sparse.eval row8794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8794, Integer.Sparse.eval_collectBalanced, rawRowCheck8794]

theorem rawRowCheck8795 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8795 := by decide +kernel

theorem rowCheck8795 : row8795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8795 := by decide +kernel

theorem rowEval8795 (x : Key → ℝ) : Integer.Sparse.eval row8795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8795, Integer.Sparse.eval_collectBalanced, rawRowCheck8795]

theorem rawRowCheck8796 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8796 := by decide +kernel

theorem rowCheck8796 : row8796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8796 := by decide +kernel

theorem rowEval8796 (x : Key → ℝ) : Integer.Sparse.eval row8796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8796, Integer.Sparse.eval_collectBalanced, rawRowCheck8796]

theorem rawRowCheck8797 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8797 := by decide +kernel

theorem rowCheck8797 : row8797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8797 := by decide +kernel

theorem rowEval8797 (x : Key → ℝ) : Integer.Sparse.eval row8797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8797, Integer.Sparse.eval_collectBalanced, rawRowCheck8797]

theorem rawRowCheck8798 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7 = rawRow8798 := by decide +kernel

theorem rowCheck8798 : row8798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8798 := by decide +kernel

theorem rowEval8798 (x : Key → ℝ) : Integer.Sparse.eval row8798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8798, Integer.Sparse.eval_collectBalanced, rawRowCheck8798]

theorem rawRowCheck8799 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7 = rawRow8799 := by decide +kernel

theorem rowCheck8799 : row8799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8799 := by decide +kernel

theorem rowEval8799 (x : Key → ℝ) : Integer.Sparse.eval row8799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8799, Integer.Sparse.eval_collectBalanced, rawRowCheck8799]

theorem rawRowCheck8800 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7 = rawRow8800 := by decide +kernel

theorem rowCheck8800 : row8800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8800 := by decide +kernel

theorem rowEval8800 (x : Key → ℝ) : Integer.Sparse.eval row8800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck8800, Integer.Sparse.eval_collectBalanced, rawRowCheck8800]

theorem rawRowCheck8801 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form8 = rawRow8801 := by decide +kernel

theorem rowCheck8801 : row8801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8801 := by decide +kernel

theorem rowEval8801 (x : Key → ℝ) : Integer.Sparse.eval row8801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8801, Integer.Sparse.eval_collectBalanced, rawRowCheck8801]

theorem rawRowCheck8802 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form8 = rawRow8802 := by decide +kernel

theorem rowCheck8802 : row8802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8802 := by decide +kernel

theorem rowEval8802 (x : Key → ℝ) : Integer.Sparse.eval row8802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8802, Integer.Sparse.eval_collectBalanced, rawRowCheck8802]

theorem rawRowCheck8803 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form8 = rawRow8803 := by decide +kernel

theorem rowCheck8803 : row8803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8803 := by decide +kernel

theorem rowEval8803 (x : Key → ℝ) : Integer.Sparse.eval row8803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8803, Integer.Sparse.eval_collectBalanced, rawRowCheck8803]

theorem rawRowCheck8804 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8804 := by decide +kernel

theorem rowCheck8804 : row8804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8804 := by decide +kernel

theorem rowEval8804 (x : Key → ℝ) : Integer.Sparse.eval row8804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8804, Integer.Sparse.eval_collectBalanced, rawRowCheck8804]

theorem rawRowCheck8805 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8805 := by decide +kernel

theorem rowCheck8805 : row8805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8805 := by decide +kernel

theorem rowEval8805 (x : Key → ℝ) : Integer.Sparse.eval row8805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8805, Integer.Sparse.eval_collectBalanced, rawRowCheck8805]

theorem rawRowCheck8806 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form8 = rawRow8806 := by decide +kernel

theorem rowCheck8806 : row8806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8806 := by decide +kernel

theorem rowEval8806 (x : Key → ℝ) : Integer.Sparse.eval row8806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8806, Integer.Sparse.eval_collectBalanced, rawRowCheck8806]

theorem rawRowCheck8807 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form8 = rawRow8807 := by decide +kernel

theorem rowCheck8807 : row8807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8807 := by decide +kernel

theorem rowEval8807 (x : Key → ℝ) : Integer.Sparse.eval row8807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8807, Integer.Sparse.eval_collectBalanced, rawRowCheck8807]

theorem rawRowCheck8808 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form8 = rawRow8808 := by decide +kernel

theorem rowCheck8808 : row8808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8808 := by decide +kernel

theorem rowEval8808 (x : Key → ℝ) : Integer.Sparse.eval row8808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck8808, Integer.Sparse.eval_collectBalanced, rawRowCheck8808]

theorem rawRowCheck8809 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form9 = rawRow8809 := by decide +kernel

theorem rowCheck8809 : row8809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8809 := by decide +kernel

theorem rowEval8809 (x : Key → ℝ) : Integer.Sparse.eval row8809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8809, Integer.Sparse.eval_collectBalanced, rawRowCheck8809]

theorem rawRowCheck8810 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form9 = rawRow8810 := by decide +kernel

theorem rowCheck8810 : row8810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8810 := by decide +kernel

theorem rowEval8810 (x : Key → ℝ) : Integer.Sparse.eval row8810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8810, Integer.Sparse.eval_collectBalanced, rawRowCheck8810]

theorem rawRowCheck8811 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form9 = rawRow8811 := by decide +kernel

theorem rowCheck8811 : row8811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8811 := by decide +kernel

theorem rowEval8811 (x : Key → ℝ) : Integer.Sparse.eval row8811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8811, Integer.Sparse.eval_collectBalanced, rawRowCheck8811]

theorem rawRowCheck8812 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8812 := by decide +kernel

theorem rowCheck8812 : row8812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8812 := by decide +kernel

theorem rowEval8812 (x : Key → ℝ) : Integer.Sparse.eval row8812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8812, Integer.Sparse.eval_collectBalanced, rawRowCheck8812]

theorem rawRowCheck8813 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8813 := by decide +kernel

theorem rowCheck8813 : row8813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8813 := by decide +kernel

theorem rowEval8813 (x : Key → ℝ) : Integer.Sparse.eval row8813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8813, Integer.Sparse.eval_collectBalanced, rawRowCheck8813]

theorem rawRowCheck8814 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form9 = rawRow8814 := by decide +kernel

theorem rowCheck8814 : row8814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8814 := by decide +kernel

theorem rowEval8814 (x : Key → ℝ) : Integer.Sparse.eval row8814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8814, Integer.Sparse.eval_collectBalanced, rawRowCheck8814]

theorem rawRowCheck8815 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form9 = rawRow8815 := by decide +kernel

theorem rowCheck8815 : row8815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8815 := by decide +kernel

theorem rowEval8815 (x : Key → ℝ) : Integer.Sparse.eval row8815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8815, Integer.Sparse.eval_collectBalanced, rawRowCheck8815]

theorem rawRowCheck8816 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9 = rawRow8816 := by decide +kernel

theorem rowCheck8816 : row8816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8816 := by decide +kernel

theorem rowEval8816 (x : Key → ℝ) : Integer.Sparse.eval row8816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck8816, Integer.Sparse.eval_collectBalanced, rawRowCheck8816]

theorem rawRowCheck8817 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow8817 := by decide +kernel

theorem rowCheck8817 : row8817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8817 := by decide +kernel

theorem rowEval8817 (x : Key → ℝ) : Integer.Sparse.eval row8817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck8817, Integer.Sparse.eval_collectBalanced, rawRowCheck8817]

theorem rawRowCheck8818 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow8818 := by decide +kernel

theorem rowCheck8818 : row8818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8818 := by decide +kernel

theorem rowEval8818 (x : Key → ℝ) : Integer.Sparse.eval row8818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8818, Integer.Sparse.eval_collectBalanced, rawRowCheck8818]

theorem rawRowCheck8819 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow8819 := by decide +kernel

theorem rowCheck8819 : row8819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8819 := by decide +kernel

theorem rowEval8819 (x : Key → ℝ) : Integer.Sparse.eval row8819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8819, Integer.Sparse.eval_collectBalanced, rawRowCheck8819]

theorem rawRowCheck8820 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8820 := by decide +kernel

theorem rowCheck8820 : row8820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8820 := by decide +kernel

theorem rowEval8820 (x : Key → ℝ) : Integer.Sparse.eval row8820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8820, Integer.Sparse.eval_collectBalanced, rawRowCheck8820]

theorem rawRowCheck8821 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10 = rawRow8821 := by decide +kernel

theorem rowCheck8821 : row8821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8821 := by decide +kernel

theorem rowEval8821 (x : Key → ℝ) : Integer.Sparse.eval row8821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8821, Integer.Sparse.eval_collectBalanced, rawRowCheck8821]

theorem rawRowCheck8822 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10 = rawRow8822 := by decide +kernel

theorem rowCheck8822 : row8822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8822 := by decide +kernel

theorem rowEval8822 (x : Key → ℝ) : Integer.Sparse.eval row8822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8822, Integer.Sparse.eval_collectBalanced, rawRowCheck8822]

theorem rawRowCheck8823 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10 = rawRow8823 := by decide +kernel

theorem rowCheck8823 : row8823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8823 := by decide +kernel

theorem rowEval8823 (x : Key → ℝ) : Integer.Sparse.eval row8823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8823, Integer.Sparse.eval_collectBalanced, rawRowCheck8823]

theorem rawRowCheck8824 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10 = rawRow8824 := by decide +kernel

theorem rowCheck8824 : row8824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8824 := by decide +kernel

theorem rowEval8824 (x : Key → ℝ) : Integer.Sparse.eval row8824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck8824, Integer.Sparse.eval_collectBalanced, rawRowCheck8824]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

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

theorem rawRowCheck7510 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7510 := by decide +kernel

theorem rowCheck7510 : row7510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7510 := by decide +kernel

theorem rowEval7510 (x : Key → ℝ) : Integer.Sparse.eval row7510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7510, Integer.Sparse.eval_collectBalanced, rawRowCheck7510]

theorem rawRowCheck7511 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7511 := by decide +kernel

theorem rowCheck7511 : row7511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7511 := by decide +kernel

theorem rowEval7511 (x : Key → ℝ) : Integer.Sparse.eval row7511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7511, Integer.Sparse.eval_collectBalanced, rawRowCheck7511]

theorem rawRowCheck7512 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7512 := by decide +kernel

theorem rowCheck7512 : row7512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7512 := by decide +kernel

theorem rowEval7512 (x : Key → ℝ) : Integer.Sparse.eval row7512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7512, Integer.Sparse.eval_collectBalanced, rawRowCheck7512]

theorem rawRowCheck7513 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7513 := by decide +kernel

theorem rowCheck7513 : row7513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7513 := by decide +kernel

theorem rowEval7513 (x : Key → ℝ) : Integer.Sparse.eval row7513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7513, Integer.Sparse.eval_collectBalanced, rawRowCheck7513]

theorem rawRowCheck7526 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7526 := by decide +kernel

theorem rowCheck7526 : row7526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7526 := by decide +kernel

theorem rowEval7526 (x : Key → ℝ) : Integer.Sparse.eval row7526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7526, Integer.Sparse.eval_collectBalanced, rawRowCheck7526]

theorem rawRowCheck7527 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7527 := by decide +kernel

theorem rowCheck7527 : row7527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7527 := by decide +kernel

theorem rowEval7527 (x : Key → ℝ) : Integer.Sparse.eval row7527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7527, Integer.Sparse.eval_collectBalanced, rawRowCheck7527]

theorem rawRowCheck7528 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7528 := by decide +kernel

theorem rowCheck7528 : row7528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7528 := by decide +kernel

theorem rowEval7528 (x : Key → ℝ) : Integer.Sparse.eval row7528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7528, Integer.Sparse.eval_collectBalanced, rawRowCheck7528]

theorem rawRowCheck7529 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7529 := by decide +kernel

theorem rowCheck7529 : row7529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7529 := by decide +kernel

theorem rowEval7529 (x : Key → ℝ) : Integer.Sparse.eval row7529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7529, Integer.Sparse.eval_collectBalanced, rawRowCheck7529]

theorem rawRowCheck7542 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7542 := by decide +kernel

theorem rowCheck7542 : row7542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7542 := by decide +kernel

theorem rowEval7542 (x : Key → ℝ) : Integer.Sparse.eval row7542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7542, Integer.Sparse.eval_collectBalanced, rawRowCheck7542]

theorem rawRowCheck7543 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7543 := by decide +kernel

theorem rowCheck7543 : row7543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7543 := by decide +kernel

theorem rowEval7543 (x : Key → ℝ) : Integer.Sparse.eval row7543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7543, Integer.Sparse.eval_collectBalanced, rawRowCheck7543]

theorem rawRowCheck7544 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7544 := by decide +kernel

theorem rowCheck7544 : row7544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7544 := by decide +kernel

theorem rowEval7544 (x : Key → ℝ) : Integer.Sparse.eval row7544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7544, Integer.Sparse.eval_collectBalanced, rawRowCheck7544]

theorem rawRowCheck7545 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7545 := by decide +kernel

theorem rowCheck7545 : row7545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7545 := by decide +kernel

theorem rowEval7545 (x : Key → ℝ) : Integer.Sparse.eval row7545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7545, Integer.Sparse.eval_collectBalanced, rawRowCheck7545]

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

theorem rawRowCheck7558 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7558 := by decide +kernel

theorem rowCheck7558 : row7558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7558 := by decide +kernel

theorem rowEval7558 (x : Key → ℝ) : Integer.Sparse.eval row7558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7558, Integer.Sparse.eval_collectBalanced, rawRowCheck7558]

theorem rawRowCheck7559 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7559 := by decide +kernel

theorem rowCheck7559 : row7559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7559 := by decide +kernel

theorem rowEval7559 (x : Key → ℝ) : Integer.Sparse.eval row7559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7559, Integer.Sparse.eval_collectBalanced, rawRowCheck7559]

theorem rawRowCheck7560 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7560 := by decide +kernel

theorem rowCheck7560 : row7560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7560 := by decide +kernel

theorem rowEval7560 (x : Key → ℝ) : Integer.Sparse.eval row7560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7560, Integer.Sparse.eval_collectBalanced, rawRowCheck7560]

theorem rawRowCheck7561 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow7561 := by decide +kernel

theorem rowCheck7561 : row7561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7561 := by decide +kernel

theorem rowEval7561 (x : Key → ℝ) : Integer.Sparse.eval row7561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7561, Integer.Sparse.eval_collectBalanced, rawRowCheck7561]

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

theorem rawRowCheck8832 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11 = rawRow8832 := by decide +kernel

theorem rowCheck8832 : row8832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8832 := by decide +kernel

theorem rowEval8832 (x : Key → ℝ) : Integer.Sparse.eval row8832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck8832, Integer.Sparse.eval_collectBalanced, rawRowCheck8832]

theorem rawRowCheck8833 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow8833 := by decide +kernel

theorem rowCheck8833 : row8833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8833 := by decide +kernel

theorem rowEval8833 (x : Key → ℝ) : Integer.Sparse.eval row8833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck8833, Integer.Sparse.eval_collectBalanced, rawRowCheck8833]

theorem rawRowCheck8834 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow8834 := by decide +kernel

theorem rowCheck8834 : row8834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8834 := by decide +kernel

theorem rowEval8834 (x : Key → ℝ) : Integer.Sparse.eval row8834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8834, Integer.Sparse.eval_collectBalanced, rawRowCheck8834]

theorem rawRowCheck8835 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow8835 := by decide +kernel

theorem rowCheck8835 : row8835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8835 := by decide +kernel

theorem rowEval8835 (x : Key → ℝ) : Integer.Sparse.eval row8835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8835, Integer.Sparse.eval_collectBalanced, rawRowCheck8835]

theorem rawRowCheck8836 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow8836 := by decide +kernel

theorem rowCheck8836 : row8836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8836 := by decide +kernel

theorem rowEval8836 (x : Key → ℝ) : Integer.Sparse.eval row8836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8836, Integer.Sparse.eval_collectBalanced, rawRowCheck8836]

theorem rawRowCheck8837 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form12 = rawRow8837 := by decide +kernel

theorem rowCheck8837 : row8837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8837 := by decide +kernel

theorem rowEval8837 (x : Key → ℝ) : Integer.Sparse.eval row8837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8837, Integer.Sparse.eval_collectBalanced, rawRowCheck8837]

theorem rawRowCheck8838 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form12 = rawRow8838 := by decide +kernel

theorem rowCheck8838 : row8838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8838 := by decide +kernel

theorem rowEval8838 (x : Key → ℝ) : Integer.Sparse.eval row8838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8838, Integer.Sparse.eval_collectBalanced, rawRowCheck8838]

theorem rawRowCheck8839 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form12 = rawRow8839 := by decide +kernel

theorem rowCheck8839 : row8839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8839 := by decide +kernel

theorem rowEval8839 (x : Key → ℝ) : Integer.Sparse.eval row8839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8839, Integer.Sparse.eval_collectBalanced, rawRowCheck8839]

theorem rawRowCheck8840 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form12 = rawRow8840 := by decide +kernel

theorem rowCheck8840 : row8840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8840 := by decide +kernel

theorem rowEval8840 (x : Key → ℝ) : Integer.Sparse.eval row8840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck8840, Integer.Sparse.eval_collectBalanced, rawRowCheck8840]

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

theorem entryCheck12_1 : entry12_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_1 k)) := by decide +kernel

theorem rowsSound12_1 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7510 x
  · exact rowEval7511 x
  · exact rowEval7512 x
  · exact rowEval7513 x
  · exact rowEval8761 x
  · exact rowEval8762 x
  · exact rowEval8763 x
  · exact rowEval8764 x

theorem entryEval12_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_1 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck12_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_1]

theorem entryCheck12_2 : entry12_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_2 k)) := by decide +kernel

theorem rowsSound12_2 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7526 x
  · exact rowEval7527 x
  · exact rowEval7528 x
  · exact rowEval7529 x
  · exact rowEval8765 x
  · exact rowEval8766 x
  · exact rowEval8767 x
  · exact rowEval8768 x

theorem entryEval12_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_2 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck12_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_2]

theorem entryCheck12_3 : entry12_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_3 k)) := by decide +kernel

theorem rowsSound12_3 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7542 x
  · exact rowEval7543 x
  · exact rowEval7544 x
  · exact rowEval7545 x
  · exact rowEval8769 x
  · exact rowEval8770 x
  · exact rowEval8771 x
  · exact rowEval8772 x

theorem entryEval12_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_3 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck12_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_3]

theorem entryCheck12_4 : entry12_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_4 k)) := by decide +kernel

theorem rowsSound12_4 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7558 x
  · exact rowEval7559 x
  · exact rowEval7560 x
  · exact rowEval7561 x
  · exact rowEval8773 x
  · exact rowEval8774 x
  · exact rowEval8775 x
  · exact rowEval8776 x

theorem entryEval12_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_4 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck12_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_4]

theorem entryCheck12_5 : entry12_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_5 k)) := by decide +kernel

theorem rowsSound12_5 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8777 x
  · exact rowEval8778 x
  · exact rowEval8779 x
  · exact rowEval8780 x
  · exact rowEval8781 x
  · exact rowEval8782 x
  · exact rowEval8783 x
  · exact rowEval8784 x

theorem entryEval12_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_5 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck12_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_5]

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

theorem entryCheck12_7 : entry12_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_7 k)) := by decide +kernel

theorem rowsSound12_7 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8793 x
  · exact rowEval8794 x
  · exact rowEval8795 x
  · exact rowEval8796 x
  · exact rowEval8797 x
  · exact rowEval8798 x
  · exact rowEval8799 x
  · exact rowEval8800 x

theorem entryEval12_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_7 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck12_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_7]

theorem entryCheck12_8 : entry12_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_8 k)) := by decide +kernel

theorem rowsSound12_8 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8801 x
  · exact rowEval8802 x
  · exact rowEval8803 x
  · exact rowEval8804 x
  · exact rowEval8805 x
  · exact rowEval8806 x
  · exact rowEval8807 x
  · exact rowEval8808 x

theorem entryEval12_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_8 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck12_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_8]

theorem entryCheck12_9 : entry12_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_9 k)) := by decide +kernel

theorem rowsSound12_9 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8809 x
  · exact rowEval8810 x
  · exact rowEval8811 x
  · exact rowEval8812 x
  · exact rowEval8813 x
  · exact rowEval8814 x
  · exact rowEval8815 x
  · exact rowEval8816 x

theorem entryEval12_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_9 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck12_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_9]

theorem entryCheck12_10 : entry12_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_10 k)) := by decide +kernel

theorem rowsSound12_10 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8817 x
  · exact rowEval8818 x
  · exact rowEval8819 x
  · exact rowEval8820 x
  · exact rowEval8821 x
  · exact rowEval8822 x
  · exact rowEval8823 x
  · exact rowEval8824 x

theorem entryEval12_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_10 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck12_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_10]

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

theorem entryCheck12_12 : entry12_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_12 k)) := by decide +kernel

theorem rowsSound12_12 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval8833 x
  · exact rowEval8834 x
  · exact rowEval8835 x
  · exact rowEval8836 x
  · exact rowEval8837 x
  · exact rowEval8838 x
  · exact rowEval8839 x
  · exact rowEval8840 x

theorem entryEval12_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_12 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck12_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_12]

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

theorem rawRowCheck9033 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow9033 := by decide +kernel

theorem rowCheck9033 : row9033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9033 := by decide +kernel

theorem rowEval9033 (x : Key → ℝ) : Integer.Sparse.eval row9033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9033, Integer.Sparse.eval_collectBalanced, rawRowCheck9033]

theorem rawRowCheck9034 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow9034 := by decide +kernel

theorem rowCheck9034 : row9034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9034 := by decide +kernel

theorem rowEval9034 (x : Key → ℝ) : Integer.Sparse.eval row9034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9034, Integer.Sparse.eval_collectBalanced, rawRowCheck9034]

theorem rawRowCheck9035 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow9035 := by decide +kernel

theorem rowCheck9035 : row9035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9035 := by decide +kernel

theorem rowEval9035 (x : Key → ℝ) : Integer.Sparse.eval row9035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9035, Integer.Sparse.eval_collectBalanced, rawRowCheck9035]

theorem rawRowCheck9036 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9036 := by decide +kernel

theorem rowCheck9036 : row9036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9036 := by decide +kernel

theorem rowEval9036 (x : Key → ℝ) : Integer.Sparse.eval row9036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9036, Integer.Sparse.eval_collectBalanced, rawRowCheck9036]

theorem rawRowCheck9037 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form12 = rawRow9037 := by decide +kernel

theorem rowCheck9037 : row9037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9037 := by decide +kernel

theorem rowEval9037 (x : Key → ℝ) : Integer.Sparse.eval row9037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9037, Integer.Sparse.eval_collectBalanced, rawRowCheck9037]

theorem rawRowCheck9038 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form12 = rawRow9038 := by decide +kernel

theorem rowCheck9038 : row9038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9038 := by decide +kernel

theorem rowEval9038 (x : Key → ℝ) : Integer.Sparse.eval row9038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9038, Integer.Sparse.eval_collectBalanced, rawRowCheck9038]

theorem rawRowCheck9039 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form12 = rawRow9039 := by decide +kernel

theorem rowCheck9039 : row9039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9039 := by decide +kernel

theorem rowEval9039 (x : Key → ℝ) : Integer.Sparse.eval row9039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9039, Integer.Sparse.eval_collectBalanced, rawRowCheck9039]

theorem rawRowCheck9040 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form12 = rawRow9040 := by decide +kernel

theorem rowCheck9040 : row9040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9040 := by decide +kernel

theorem rowEval9040 (x : Key → ℝ) : Integer.Sparse.eval row9040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9040, Integer.Sparse.eval_collectBalanced, rawRowCheck9040]

theorem rawRowCheck9041 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form12 = rawRow9041 := by decide +kernel

theorem rowCheck9041 : row9041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9041 := by decide +kernel

theorem rowEval9041 (x : Key → ℝ) : Integer.Sparse.eval row9041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9041, Integer.Sparse.eval_collectBalanced, rawRowCheck9041]

theorem rawRowCheck9042 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form12 = rawRow9042 := by decide +kernel

theorem rowCheck9042 : row9042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9042 := by decide +kernel

theorem rowEval9042 (x : Key → ℝ) : Integer.Sparse.eval row9042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9042, Integer.Sparse.eval_collectBalanced, rawRowCheck9042]

theorem rawRowCheck9043 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form12 = rawRow9043 := by decide +kernel

theorem rowCheck9043 : row9043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9043 := by decide +kernel

theorem rowEval9043 (x : Key → ℝ) : Integer.Sparse.eval row9043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9043, Integer.Sparse.eval_collectBalanced, rawRowCheck9043]

theorem rawRowCheck9044 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form12 = rawRow9044 := by decide +kernel

theorem rowCheck9044 : row9044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9044 := by decide +kernel

theorem rowEval9044 (x : Key → ℝ) : Integer.Sparse.eval row9044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9044, Integer.Sparse.eval_collectBalanced, rawRowCheck9044]

theorem rawRowCheck9045 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form12 = rawRow9045 := by decide +kernel

theorem rowCheck9045 : row9045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9045 := by decide +kernel

theorem rowEval9045 (x : Key → ℝ) : Integer.Sparse.eval row9045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9045, Integer.Sparse.eval_collectBalanced, rawRowCheck9045]

theorem rawRowCheck9046 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form12 = rawRow9046 := by decide +kernel

theorem rowCheck9046 : row9046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9046 := by decide +kernel

theorem rowEval9046 (x : Key → ℝ) : Integer.Sparse.eval row9046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9046, Integer.Sparse.eval_collectBalanced, rawRowCheck9046]

theorem rawRowCheck9047 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form12 = rawRow9047 := by decide +kernel

theorem rowCheck9047 : row9047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9047 := by decide +kernel

theorem rowEval9047 (x : Key → ℝ) : Integer.Sparse.eval row9047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9047, Integer.Sparse.eval_collectBalanced, rawRowCheck9047]

theorem rawRowCheck9048 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form12 = rawRow9048 := by decide +kernel

theorem rowCheck9048 : row9048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9048 := by decide +kernel

theorem rowEval9048 (x : Key → ℝ) : Integer.Sparse.eval row9048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9048, Integer.Sparse.eval_collectBalanced, rawRowCheck9048]

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

theorem entryCheck13_12 : entry13_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_12 k)) := by decide +kernel

theorem rowsSound13_12 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9033 x
  · exact rowEval9034 x
  · exact rowEval9035 x
  · exact rowEval9036 x
  · exact rowEval9037 x
  · exact rowEval9038 x
  · exact rowEval9039 x
  · exact rowEval9040 x
  · exact rowEval9041 x
  · exact rowEval9042 x
  · exact rowEval9043 x
  · exact rowEval9044 x
  · exact rowEval9045 x
  · exact rowEval9046 x
  · exact rowEval9047 x
  · exact rowEval9048 x

theorem entryEval13_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_12 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck13_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_12]

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

theorem rawRowCheck9317 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form12 = rawRow9317 := by decide +kernel

theorem rowCheck9317 : row9317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9317 := by decide +kernel

theorem rowEval9317 (x : Key → ℝ) : Integer.Sparse.eval row9317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9317, Integer.Sparse.eval_collectBalanced, rawRowCheck9317]

theorem rawRowCheck9318 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form12 = rawRow9318 := by decide +kernel

theorem rowCheck9318 : row9318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9318 := by decide +kernel

theorem rowEval9318 (x : Key → ℝ) : Integer.Sparse.eval row9318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9318, Integer.Sparse.eval_collectBalanced, rawRowCheck9318]

theorem rawRowCheck9319 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form12 = rawRow9319 := by decide +kernel

theorem rowCheck9319 : row9319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9319 := by decide +kernel

theorem rowEval9319 (x : Key → ℝ) : Integer.Sparse.eval row9319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9319, Integer.Sparse.eval_collectBalanced, rawRowCheck9319]

theorem rawRowCheck9320 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9320 := by decide +kernel

theorem rowCheck9320 : row9320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9320 := by decide +kernel

theorem rowEval9320 (x : Key → ℝ) : Integer.Sparse.eval row9320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9320, Integer.Sparse.eval_collectBalanced, rawRowCheck9320]

theorem rawRowCheck9321 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form12 = rawRow9321 := by decide +kernel

theorem rowCheck9321 : row9321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9321 := by decide +kernel

theorem rowEval9321 (x : Key → ℝ) : Integer.Sparse.eval row9321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9321, Integer.Sparse.eval_collectBalanced, rawRowCheck9321]

theorem rawRowCheck9322 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form12 = rawRow9322 := by decide +kernel

theorem rowCheck9322 : row9322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9322 := by decide +kernel

theorem rowEval9322 (x : Key → ℝ) : Integer.Sparse.eval row9322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9322, Integer.Sparse.eval_collectBalanced, rawRowCheck9322]

theorem rawRowCheck9323 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form12 = rawRow9323 := by decide +kernel

theorem rowCheck9323 : row9323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9323 := by decide +kernel

theorem rowEval9323 (x : Key → ℝ) : Integer.Sparse.eval row9323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9323, Integer.Sparse.eval_collectBalanced, rawRowCheck9323]

theorem rawRowCheck9324 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form12 = rawRow9324 := by decide +kernel

theorem rowCheck9324 : row9324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9324 := by decide +kernel

theorem rowEval9324 (x : Key → ℝ) : Integer.Sparse.eval row9324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9324, Integer.Sparse.eval_collectBalanced, rawRowCheck9324]

theorem rawRowCheck9325 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form12 = rawRow9325 := by decide +kernel

theorem rowCheck9325 : row9325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9325 := by decide +kernel

theorem rowEval9325 (x : Key → ℝ) : Integer.Sparse.eval row9325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9325, Integer.Sparse.eval_collectBalanced, rawRowCheck9325]

theorem rawRowCheck9326 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form12 = rawRow9326 := by decide +kernel

theorem rowCheck9326 : row9326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9326 := by decide +kernel

theorem rowEval9326 (x : Key → ℝ) : Integer.Sparse.eval row9326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9326, Integer.Sparse.eval_collectBalanced, rawRowCheck9326]

theorem rawRowCheck9327 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form12 = rawRow9327 := by decide +kernel

theorem rowCheck9327 : row9327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9327 := by decide +kernel

theorem rowEval9327 (x : Key → ℝ) : Integer.Sparse.eval row9327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9327, Integer.Sparse.eval_collectBalanced, rawRowCheck9327]

theorem rawRowCheck9328 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form12 = rawRow9328 := by decide +kernel

theorem rowCheck9328 : row9328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9328 := by decide +kernel

theorem rowEval9328 (x : Key → ℝ) : Integer.Sparse.eval row9328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9328, Integer.Sparse.eval_collectBalanced, rawRowCheck9328]

theorem rawRowCheck9329 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form12 = rawRow9329 := by decide +kernel

theorem rowCheck9329 : row9329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9329 := by decide +kernel

theorem rowEval9329 (x : Key → ℝ) : Integer.Sparse.eval row9329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9329, Integer.Sparse.eval_collectBalanced, rawRowCheck9329]

theorem rawRowCheck9330 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form12 = rawRow9330 := by decide +kernel

theorem rowCheck9330 : row9330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9330 := by decide +kernel

theorem rowEval9330 (x : Key → ℝ) : Integer.Sparse.eval row9330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9330, Integer.Sparse.eval_collectBalanced, rawRowCheck9330]

theorem rawRowCheck9331 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form12 = rawRow9331 := by decide +kernel

theorem rowCheck9331 : row9331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9331 := by decide +kernel

theorem rowEval9331 (x : Key → ℝ) : Integer.Sparse.eval row9331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9331, Integer.Sparse.eval_collectBalanced, rawRowCheck9331]

theorem rawRowCheck9332 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form12 = rawRow9332 := by decide +kernel

theorem rowCheck9332 : row9332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9332 := by decide +kernel

theorem rowEval9332 (x : Key → ℝ) : Integer.Sparse.eval row9332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9332, Integer.Sparse.eval_collectBalanced, rawRowCheck9332]

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

theorem entryCheck15_12 : entry15_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_12 k)) := by decide +kernel

theorem rowsSound15_12 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9317 x
  · exact rowEval9318 x
  · exact rowEval9319 x
  · exact rowEval9320 x
  · exact rowEval9321 x
  · exact rowEval9322 x
  · exact rowEval9323 x
  · exact rowEval9324 x
  · exact rowEval9325 x
  · exact rowEval9326 x
  · exact rowEval9327 x
  · exact rowEval9328 x
  · exact rowEval9329 x
  · exact rowEval9330 x
  · exact rowEval9331 x
  · exact rowEval9332 x

theorem entryEval15_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_12 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck15_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_12]

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

theorem rawRowCheck9789 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form12 = rawRow9789 := by decide +kernel

theorem rowCheck9789 : row9789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9789 := by decide +kernel

theorem rowEval9789 (x : Key → ℝ) : Integer.Sparse.eval row9789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9789, Integer.Sparse.eval_collectBalanced, rawRowCheck9789]

theorem rawRowCheck9790 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form12 = rawRow9790 := by decide +kernel

theorem rowCheck9790 : row9790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9790 := by decide +kernel

theorem rowEval9790 (x : Key → ℝ) : Integer.Sparse.eval row9790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9790, Integer.Sparse.eval_collectBalanced, rawRowCheck9790]

theorem rawRowCheck9791 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form12 = rawRow9791 := by decide +kernel

theorem rowCheck9791 : row9791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9791 := by decide +kernel

theorem rowEval9791 (x : Key → ℝ) : Integer.Sparse.eval row9791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9791, Integer.Sparse.eval_collectBalanced, rawRowCheck9791]

theorem rawRowCheck9792 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form12 = rawRow9792 := by decide +kernel

theorem rowCheck9792 : row9792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9792 := by decide +kernel

theorem rowEval9792 (x : Key → ℝ) : Integer.Sparse.eval row9792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9792, Integer.Sparse.eval_collectBalanced, rawRowCheck9792]

theorem rawRowCheck9793 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form12 = rawRow9793 := by decide +kernel

theorem rowCheck9793 : row9793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9793 := by decide +kernel

theorem rowEval9793 (x : Key → ℝ) : Integer.Sparse.eval row9793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9793, Integer.Sparse.eval_collectBalanced, rawRowCheck9793]

theorem rawRowCheck9794 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form12 = rawRow9794 := by decide +kernel

theorem rowCheck9794 : row9794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9794 := by decide +kernel

theorem rowEval9794 (x : Key → ℝ) : Integer.Sparse.eval row9794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9794, Integer.Sparse.eval_collectBalanced, rawRowCheck9794]

theorem rawRowCheck9795 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form12 = rawRow9795 := by decide +kernel

theorem rowCheck9795 : row9795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9795 := by decide +kernel

theorem rowEval9795 (x : Key → ℝ) : Integer.Sparse.eval row9795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9795, Integer.Sparse.eval_collectBalanced, rawRowCheck9795]

theorem rawRowCheck9796 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form12 = rawRow9796 := by decide +kernel

theorem rowCheck9796 : row9796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9796 := by decide +kernel

theorem rowEval9796 (x : Key → ℝ) : Integer.Sparse.eval row9796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9796, Integer.Sparse.eval_collectBalanced, rawRowCheck9796]

theorem rawRowCheck9797 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form12 = rawRow9797 := by decide +kernel

theorem rowCheck9797 : row9797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9797 := by decide +kernel

theorem rowEval9797 (x : Key → ℝ) : Integer.Sparse.eval row9797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9797, Integer.Sparse.eval_collectBalanced, rawRowCheck9797]

theorem rawRowCheck9798 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form12 = rawRow9798 := by decide +kernel

theorem rowCheck9798 : row9798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9798 := by decide +kernel

theorem rowEval9798 (x : Key → ℝ) : Integer.Sparse.eval row9798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9798, Integer.Sparse.eval_collectBalanced, rawRowCheck9798]

theorem rawRowCheck9799 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form12 = rawRow9799 := by decide +kernel

theorem rowCheck9799 : row9799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9799 := by decide +kernel

theorem rowEval9799 (x : Key → ℝ) : Integer.Sparse.eval row9799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9799, Integer.Sparse.eval_collectBalanced, rawRowCheck9799]

theorem rawRowCheck9800 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form12 = rawRow9800 := by decide +kernel

theorem rowCheck9800 : row9800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9800 := by decide +kernel

theorem rowEval9800 (x : Key → ℝ) : Integer.Sparse.eval row9800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9800, Integer.Sparse.eval_collectBalanced, rawRowCheck9800]

theorem rawRowCheck9801 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form12 = rawRow9801 := by decide +kernel

theorem rowCheck9801 : row9801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9801 := by decide +kernel

theorem rowEval9801 (x : Key → ℝ) : Integer.Sparse.eval row9801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9801, Integer.Sparse.eval_collectBalanced, rawRowCheck9801]

theorem rawRowCheck9802 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form12 = rawRow9802 := by decide +kernel

theorem rowCheck9802 : row9802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9802 := by decide +kernel

theorem rowEval9802 (x : Key → ℝ) : Integer.Sparse.eval row9802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9802, Integer.Sparse.eval_collectBalanced, rawRowCheck9802]

theorem rawRowCheck9803 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form12 = rawRow9803 := by decide +kernel

theorem rowCheck9803 : row9803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9803 := by decide +kernel

theorem rowEval9803 (x : Key → ℝ) : Integer.Sparse.eval row9803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9803, Integer.Sparse.eval_collectBalanced, rawRowCheck9803]

theorem rawRowCheck9804 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form12 = rawRow9804 := by decide +kernel

theorem rowCheck9804 : row9804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9804 := by decide +kernel

theorem rowEval9804 (x : Key → ℝ) : Integer.Sparse.eval row9804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9804, Integer.Sparse.eval_collectBalanced, rawRowCheck9804]

theorem rawRowCheck9805 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form12 = rawRow9805 := by decide +kernel

theorem rowCheck9805 : row9805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9805 := by decide +kernel

theorem rowEval9805 (x : Key → ℝ) : Integer.Sparse.eval row9805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9805, Integer.Sparse.eval_collectBalanced, rawRowCheck9805]

theorem rawRowCheck9806 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form12 = rawRow9806 := by decide +kernel

theorem rowCheck9806 : row9806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9806 := by decide +kernel

theorem rowEval9806 (x : Key → ℝ) : Integer.Sparse.eval row9806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9806, Integer.Sparse.eval_collectBalanced, rawRowCheck9806]

theorem rawRowCheck9807 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form12 = rawRow9807 := by decide +kernel

theorem rowCheck9807 : row9807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9807 := by decide +kernel

theorem rowEval9807 (x : Key → ℝ) : Integer.Sparse.eval row9807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9807, Integer.Sparse.eval_collectBalanced, rawRowCheck9807]

theorem rawRowCheck9808 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form12 = rawRow9808 := by decide +kernel

theorem rowCheck9808 : row9808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9808 := by decide +kernel

theorem rowEval9808 (x : Key → ℝ) : Integer.Sparse.eval row9808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9808, Integer.Sparse.eval_collectBalanced, rawRowCheck9808]

theorem rawRowCheck9809 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form12 = rawRow9809 := by decide +kernel

theorem rowCheck9809 : row9809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9809 := by decide +kernel

theorem rowEval9809 (x : Key → ℝ) : Integer.Sparse.eval row9809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9809, Integer.Sparse.eval_collectBalanced, rawRowCheck9809]

theorem rawRowCheck9810 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form12 = rawRow9810 := by decide +kernel

theorem rowCheck9810 : row9810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9810 := by decide +kernel

theorem rowEval9810 (x : Key → ℝ) : Integer.Sparse.eval row9810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9810, Integer.Sparse.eval_collectBalanced, rawRowCheck9810]

theorem rawRowCheck9811 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form12 = rawRow9811 := by decide +kernel

theorem rowCheck9811 : row9811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9811 := by decide +kernel

theorem rowEval9811 (x : Key → ℝ) : Integer.Sparse.eval row9811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9811, Integer.Sparse.eval_collectBalanced, rawRowCheck9811]

theorem rawRowCheck9812 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form12 = rawRow9812 := by decide +kernel

theorem rowCheck9812 : row9812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9812 := by decide +kernel

theorem rowEval9812 (x : Key → ℝ) : Integer.Sparse.eval row9812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9812, Integer.Sparse.eval_collectBalanced, rawRowCheck9812]

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

theorem entryCheck17_12 : entry17_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form17.terms k).coefficient) (rows17_12 k)) := by decide +kernel

theorem rowsSound17_12 (k : Fin GramFunctions.Block3.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form17.terms k).tag (GramFunctions.Block3.form17.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9789 x
  · exact rowEval9790 x
  · exact rowEval9791 x
  · exact rowEval9792 x
  · exact rowEval9793 x
  · exact rowEval9794 x
  · exact rowEval9795 x
  · exact rowEval9796 x
  · exact rowEval9797 x
  · exact rowEval9798 x
  · exact rowEval9799 x
  · exact rowEval9800 x
  · exact rowEval9801 x
  · exact rowEval9802 x
  · exact rowEval9803 x
  · exact rowEval9804 x
  · exact rowEval9805 x
  · exact rowEval9806 x
  · exact rowEval9807 x
  · exact rowEval9808 x
  · exact rowEval9809 x
  · exact rowEval9810 x
  · exact rowEval9811 x
  · exact rowEval9812 x

theorem entryEval17_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_12 (GramNormalization.eval B) = GramFunctions.Block3.form17.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck17_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form17 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_12]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck10509 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form12 = rawRow10509 := by decide +kernel

theorem rowCheck10509 : row10509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10509 := by decide +kernel

theorem rowEval10509 (x : Key → ℝ) : Integer.Sparse.eval row10509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10509, Integer.Sparse.eval_collectBalanced, rawRowCheck10509]

theorem rawRowCheck10510 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form12 = rawRow10510 := by decide +kernel

theorem rowCheck10510 : row10510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10510 := by decide +kernel

theorem rowEval10510 (x : Key → ℝ) : Integer.Sparse.eval row10510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10510, Integer.Sparse.eval_collectBalanced, rawRowCheck10510]

theorem rawRowCheck10511 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form12 = rawRow10511 := by decide +kernel

theorem rowCheck10511 : row10511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10511 := by decide +kernel

theorem rowEval10511 (x : Key → ℝ) : Integer.Sparse.eval row10511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10511, Integer.Sparse.eval_collectBalanced, rawRowCheck10511]

theorem rawRowCheck10512 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form12 = rawRow10512 := by decide +kernel

theorem rowCheck10512 : row10512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10512 := by decide +kernel

theorem rowEval10512 (x : Key → ℝ) : Integer.Sparse.eval row10512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10512, Integer.Sparse.eval_collectBalanced, rawRowCheck10512]

theorem rawRowCheck10513 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form12 = rawRow10513 := by decide +kernel

theorem rowCheck10513 : row10513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10513 := by decide +kernel

theorem rowEval10513 (x : Key → ℝ) : Integer.Sparse.eval row10513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10513, Integer.Sparse.eval_collectBalanced, rawRowCheck10513]

theorem rawRowCheck10514 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form12 = rawRow10514 := by decide +kernel

theorem rowCheck10514 : row10514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10514 := by decide +kernel

theorem rowEval10514 (x : Key → ℝ) : Integer.Sparse.eval row10514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10514, Integer.Sparse.eval_collectBalanced, rawRowCheck10514]

theorem rawRowCheck10515 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form12 = rawRow10515 := by decide +kernel

theorem rowCheck10515 : row10515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10515 := by decide +kernel

theorem rowEval10515 (x : Key → ℝ) : Integer.Sparse.eval row10515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10515, Integer.Sparse.eval_collectBalanced, rawRowCheck10515]

theorem rawRowCheck10516 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form12 = rawRow10516 := by decide +kernel

theorem rowCheck10516 : row10516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10516 := by decide +kernel

theorem rowEval10516 (x : Key → ℝ) : Integer.Sparse.eval row10516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10516, Integer.Sparse.eval_collectBalanced, rawRowCheck10516]

theorem rawRowCheck10517 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form12 = rawRow10517 := by decide +kernel

theorem rowCheck10517 : row10517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10517 := by decide +kernel

theorem rowEval10517 (x : Key → ℝ) : Integer.Sparse.eval row10517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10517, Integer.Sparse.eval_collectBalanced, rawRowCheck10517]

theorem rawRowCheck10518 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form12 = rawRow10518 := by decide +kernel

theorem rowCheck10518 : row10518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10518 := by decide +kernel

theorem rowEval10518 (x : Key → ℝ) : Integer.Sparse.eval row10518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10518, Integer.Sparse.eval_collectBalanced, rawRowCheck10518]

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

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

theorem rowsSound19_12 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval10509 x
  · exact rowEval10510 x
  · exact rowEval10511 x
  · exact rowEval10512 x
  · exact rowEval10513 x
  · exact rowEval10514 x
  · exact rowEval10515 x
  · exact rowEval10516 x
  · exact rowEval10517 x
  · exact rowEval10518 x

theorem entryEval19_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_12 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck19_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_12]

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

theorem rawRowCheck10649 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow10649 := by decide +kernel

theorem rowCheck10649 : row10649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10649 := by decide +kernel

theorem rowEval10649 (x : Key → ℝ) : Integer.Sparse.eval row10649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck10649, Integer.Sparse.eval_collectBalanced, rawRowCheck10649]

theorem rawRowCheck10650 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow10650 := by decide +kernel

theorem rowCheck10650 : row10650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10650 := by decide +kernel

theorem rowEval10650 (x : Key → ℝ) : Integer.Sparse.eval row10650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10650, Integer.Sparse.eval_collectBalanced, rawRowCheck10650]

theorem rawRowCheck10651 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow10651 := by decide +kernel

theorem rowCheck10651 : row10651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10651 := by decide +kernel

theorem rowEval10651 (x : Key → ℝ) : Integer.Sparse.eval row10651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10651, Integer.Sparse.eval_collectBalanced, rawRowCheck10651]

theorem rawRowCheck10652 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow10652 := by decide +kernel

theorem rowCheck10652 : row10652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10652 := by decide +kernel

theorem rowEval10652 (x : Key → ℝ) : Integer.Sparse.eval row10652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10652, Integer.Sparse.eval_collectBalanced, rawRowCheck10652]

theorem rawRowCheck10653 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form12 = rawRow10653 := by decide +kernel

theorem rowCheck10653 : row10653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10653 := by decide +kernel

theorem rowEval10653 (x : Key → ℝ) : Integer.Sparse.eval row10653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10653, Integer.Sparse.eval_collectBalanced, rawRowCheck10653]

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

theorem entryCheck20_12 : entry20_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_12 k)) := by decide +kernel

theorem rowsSound20_12 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval10649 x
  · exact rowEval10650 x
  · exact rowEval10651 x
  · exact rowEval10652 x
  · exact rowEval10653 x

theorem entryEval20_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_12 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck20_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_12]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11126 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form12 = rawRow11126 := by decide +kernel

theorem rowCheck11126 : row11126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11126 := by decide +kernel

theorem rowEval11126 (x : Key → ℝ) : Integer.Sparse.eval row11126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11126, Integer.Sparse.eval_collectBalanced, rawRowCheck11126]

theorem rawRowCheck11127 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form12 = rawRow11127 := by decide +kernel

theorem rowCheck11127 : row11127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11127 := by decide +kernel

theorem rowEval11127 (x : Key → ℝ) : Integer.Sparse.eval row11127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11127, Integer.Sparse.eval_collectBalanced, rawRowCheck11127]

theorem rawRowCheck11128 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form12 = rawRow11128 := by decide +kernel

theorem rowCheck11128 : row11128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11128 := by decide +kernel

theorem rowEval11128 (x : Key → ℝ) : Integer.Sparse.eval row11128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11128, Integer.Sparse.eval_collectBalanced, rawRowCheck11128]

theorem rawRowCheck11129 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form12 = rawRow11129 := by decide +kernel

theorem rowCheck11129 : row11129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11129 := by decide +kernel

theorem rowEval11129 (x : Key → ℝ) : Integer.Sparse.eval row11129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11129, Integer.Sparse.eval_collectBalanced, rawRowCheck11129]

theorem rawRowCheck11130 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form12 = rawRow11130 := by decide +kernel

theorem rowCheck11130 : row11130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11130 := by decide +kernel

theorem rowEval11130 (x : Key → ℝ) : Integer.Sparse.eval row11130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11130, Integer.Sparse.eval_collectBalanced, rawRowCheck11130]

theorem rawRowCheck11131 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form12 = rawRow11131 := by decide +kernel

theorem rowCheck11131 : row11131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11131 := by decide +kernel

theorem rowEval11131 (x : Key → ℝ) : Integer.Sparse.eval row11131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11131, Integer.Sparse.eval_collectBalanced, rawRowCheck11131]

theorem rawRowCheck11132 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form12 = rawRow11132 := by decide +kernel

theorem rowCheck11132 : row11132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11132 := by decide +kernel

theorem rowEval11132 (x : Key → ℝ) : Integer.Sparse.eval row11132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11132, Integer.Sparse.eval_collectBalanced, rawRowCheck11132]

theorem rawRowCheck11133 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form12 = rawRow11133 := by decide +kernel

theorem rowCheck11133 : row11133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11133 := by decide +kernel

theorem rowEval11133 (x : Key → ℝ) : Integer.Sparse.eval row11133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11133, Integer.Sparse.eval_collectBalanced, rawRowCheck11133]

theorem rawRowCheck11134 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form12 = rawRow11134 := by decide +kernel

theorem rowCheck11134 : row11134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11134 := by decide +kernel

theorem rowEval11134 (x : Key → ℝ) : Integer.Sparse.eval row11134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11134, Integer.Sparse.eval_collectBalanced, rawRowCheck11134]

theorem rawRowCheck11135 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form12 = rawRow11135 := by decide +kernel

theorem rowCheck11135 : row11135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11135 := by decide +kernel

theorem rowEval11135 (x : Key → ℝ) : Integer.Sparse.eval row11135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11135, Integer.Sparse.eval_collectBalanced, rawRowCheck11135]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck11136 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form12 = rawRow11136 := by decide +kernel

theorem rowCheck11136 : row11136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11136 := by decide +kernel

theorem rowEval11136 (x : Key → ℝ) : Integer.Sparse.eval row11136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11136, Integer.Sparse.eval_collectBalanced, rawRowCheck11136]

theorem rawRowCheck11137 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form12 = rawRow11137 := by decide +kernel

theorem rowCheck11137 : row11137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11137 := by decide +kernel

theorem rowEval11137 (x : Key → ℝ) : Integer.Sparse.eval row11137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11137, Integer.Sparse.eval_collectBalanced, rawRowCheck11137]

theorem rawRowCheck11138 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form12 = rawRow11138 := by decide +kernel

theorem rowCheck11138 : row11138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11138 := by decide +kernel

theorem rowEval11138 (x : Key → ℝ) : Integer.Sparse.eval row11138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11138, Integer.Sparse.eval_collectBalanced, rawRowCheck11138]

theorem rawRowCheck11139 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form12 = rawRow11139 := by decide +kernel

theorem rowCheck11139 : row11139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11139 := by decide +kernel

theorem rowEval11139 (x : Key → ℝ) : Integer.Sparse.eval row11139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11139, Integer.Sparse.eval_collectBalanced, rawRowCheck11139]

theorem rawRowCheck11140 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form12 = rawRow11140 := by decide +kernel

theorem rowCheck11140 : row11140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11140 := by decide +kernel

theorem rowEval11140 (x : Key → ℝ) : Integer.Sparse.eval row11140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11140, Integer.Sparse.eval_collectBalanced, rawRowCheck11140]

theorem rawRowCheck11141 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form12 = rawRow11141 := by decide +kernel

theorem rowCheck11141 : row11141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11141 := by decide +kernel

theorem rowEval11141 (x : Key → ℝ) : Integer.Sparse.eval row11141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11141, Integer.Sparse.eval_collectBalanced, rawRowCheck11141]

theorem rawRowCheck11142 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form12 = rawRow11142 := by decide +kernel

theorem rowCheck11142 : row11142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11142 := by decide +kernel

theorem rowEval11142 (x : Key → ℝ) : Integer.Sparse.eval row11142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11142, Integer.Sparse.eval_collectBalanced, rawRowCheck11142]

theorem rawRowCheck11143 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form12 = rawRow11143 := by decide +kernel

theorem rowCheck11143 : row11143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11143 := by decide +kernel

theorem rowEval11143 (x : Key → ℝ) : Integer.Sparse.eval row11143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11143, Integer.Sparse.eval_collectBalanced, rawRowCheck11143]

theorem rawRowCheck11144 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form12 = rawRow11144 := by decide +kernel

theorem rowCheck11144 : row11144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11144 := by decide +kernel

theorem rowEval11144 (x : Key → ℝ) : Integer.Sparse.eval row11144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11144, Integer.Sparse.eval_collectBalanced, rawRowCheck11144]

theorem rawRowCheck11145 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form12 = rawRow11145 := by decide +kernel

theorem rowCheck11145 : row11145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11145 := by decide +kernel

theorem rowEval11145 (x : Key → ℝ) : Integer.Sparse.eval row11145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11145, Integer.Sparse.eval_collectBalanced, rawRowCheck11145]

theorem rawRowCheck11146 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form12 = rawRow11146 := by decide +kernel

theorem rowCheck11146 : row11146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11146 := by decide +kernel

theorem rowEval11146 (x : Key → ℝ) : Integer.Sparse.eval row11146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11146, Integer.Sparse.eval_collectBalanced, rawRowCheck11146]

theorem rawRowCheck11147 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form12 = rawRow11147 := by decide +kernel

theorem rowCheck11147 : row11147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11147 := by decide +kernel

theorem rowEval11147 (x : Key → ℝ) : Integer.Sparse.eval row11147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11147, Integer.Sparse.eval_collectBalanced, rawRowCheck11147]

theorem rawRowCheck11148 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form12 = rawRow11148 := by decide +kernel

theorem rowCheck11148 : row11148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11148 := by decide +kernel

theorem rowEval11148 (x : Key → ℝ) : Integer.Sparse.eval row11148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11148, Integer.Sparse.eval_collectBalanced, rawRowCheck11148]

theorem rawRowCheck11149 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form12 = rawRow11149 := by decide +kernel

theorem rowCheck11149 : row11149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11149 := by decide +kernel

theorem rowEval11149 (x : Key → ℝ) : Integer.Sparse.eval row11149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11149, Integer.Sparse.eval_collectBalanced, rawRowCheck11149]

theorem rawRowCheck11150 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form12 = rawRow11150 := by decide +kernel

theorem rowCheck11150 : row11150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11150 := by decide +kernel

theorem rowEval11150 (x : Key → ℝ) : Integer.Sparse.eval row11150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11150, Integer.Sparse.eval_collectBalanced, rawRowCheck11150]

theorem rawRowCheck11151 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form12 = rawRow11151 := by decide +kernel

theorem rowCheck11151 : row11151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11151 := by decide +kernel

theorem rowEval11151 (x : Key → ℝ) : Integer.Sparse.eval row11151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11151, Integer.Sparse.eval_collectBalanced, rawRowCheck11151]

theorem rawRowCheck11152 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form12 = rawRow11152 := by decide +kernel

theorem rowCheck11152 : row11152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11152 := by decide +kernel

theorem rowEval11152 (x : Key → ℝ) : Integer.Sparse.eval row11152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11152, Integer.Sparse.eval_collectBalanced, rawRowCheck11152]

theorem rawRowCheck11153 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form12 = rawRow11153 := by decide +kernel

theorem rowCheck11153 : row11153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11153 := by decide +kernel

theorem rowEval11153 (x : Key → ℝ) : Integer.Sparse.eval row11153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11153, Integer.Sparse.eval_collectBalanced, rawRowCheck11153]

theorem rawRowCheck11154 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form12 = rawRow11154 := by decide +kernel

theorem rowCheck11154 : row11154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11154 := by decide +kernel

theorem rowEval11154 (x : Key → ℝ) : Integer.Sparse.eval row11154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11154, Integer.Sparse.eval_collectBalanced, rawRowCheck11154]

theorem rawRowCheck11155 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form12 = rawRow11155 := by decide +kernel

theorem rowCheck11155 : row11155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11155 := by decide +kernel

theorem rowEval11155 (x : Key → ℝ) : Integer.Sparse.eval row11155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11155, Integer.Sparse.eval_collectBalanced, rawRowCheck11155]

theorem rawRowCheck11156 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form12 = rawRow11156 := by decide +kernel

theorem rowCheck11156 : row11156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11156 := by decide +kernel

theorem rowEval11156 (x : Key → ℝ) : Integer.Sparse.eval row11156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11156, Integer.Sparse.eval_collectBalanced, rawRowCheck11156]

theorem rawRowCheck11157 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form12 = rawRow11157 := by decide +kernel

theorem rowCheck11157 : row11157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11157 := by decide +kernel

theorem rowEval11157 (x : Key → ℝ) : Integer.Sparse.eval row11157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11157, Integer.Sparse.eval_collectBalanced, rawRowCheck11157]

theorem rawRowCheck11158 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form12 = rawRow11158 := by decide +kernel

theorem rowCheck11158 : row11158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11158 := by decide +kernel

theorem rowEval11158 (x : Key → ℝ) : Integer.Sparse.eval row11158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11158, Integer.Sparse.eval_collectBalanced, rawRowCheck11158]

theorem rawRowCheck11159 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form12 = rawRow11159 := by decide +kernel

theorem rowCheck11159 : row11159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11159 := by decide +kernel

theorem rowEval11159 (x : Key → ℝ) : Integer.Sparse.eval row11159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11159, Integer.Sparse.eval_collectBalanced, rawRowCheck11159]

theorem rawRowCheck11160 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form12 = rawRow11160 := by decide +kernel

theorem rowCheck11160 : row11160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11160 := by decide +kernel

theorem rowEval11160 (x : Key → ℝ) : Integer.Sparse.eval row11160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11160, Integer.Sparse.eval_collectBalanced, rawRowCheck11160]

theorem rawRowCheck11161 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form12 = rawRow11161 := by decide +kernel

theorem rowCheck11161 : row11161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11161 := by decide +kernel

theorem rowEval11161 (x : Key → ℝ) : Integer.Sparse.eval row11161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11161, Integer.Sparse.eval_collectBalanced, rawRowCheck11161]

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

theorem entryCheck21_12 : entry21_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_12 k)) := by decide +kernel

theorem rowsSound21_12 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval11126 x
  · exact rowEval11127 x
  · exact rowEval11128 x
  · exact rowEval11129 x
  · exact rowEval11130 x
  · exact rowEval11131 x
  · exact rowEval11132 x
  · exact rowEval11133 x
  · exact rowEval11134 x
  · exact rowEval11135 x
  · exact rowEval11136 x
  · exact rowEval11137 x
  · exact rowEval11138 x
  · exact rowEval11139 x
  · exact rowEval11140 x
  · exact rowEval11141 x
  · exact rowEval11142 x
  · exact rowEval11143 x
  · exact rowEval11144 x
  · exact rowEval11145 x
  · exact rowEval11146 x
  · exact rowEval11147 x
  · exact rowEval11148 x
  · exact rowEval11149 x
  · exact rowEval11150 x
  · exact rowEval11151 x
  · exact rowEval11152 x
  · exact rowEval11153 x
  · exact rowEval11154 x
  · exact rowEval11155 x
  · exact rowEval11156 x
  · exact rowEval11157 x
  · exact rowEval11158 x
  · exact rowEval11159 x
  · exact rowEval11160 x
  · exact rowEval11161 x

theorem entryEval21_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_12 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck21_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_12]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck11630 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form12 = rawRow11630 := by decide +kernel

theorem rowCheck11630 : row11630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11630 := by decide +kernel

theorem rowEval11630 (x : Key → ℝ) : Integer.Sparse.eval row11630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11630, Integer.Sparse.eval_collectBalanced, rawRowCheck11630]

theorem rawRowCheck11631 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form12 = rawRow11631 := by decide +kernel

theorem rowCheck11631 : row11631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11631 := by decide +kernel

theorem rowEval11631 (x : Key → ℝ) : Integer.Sparse.eval row11631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11631, Integer.Sparse.eval_collectBalanced, rawRowCheck11631]

theorem rawRowCheck11632 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form12 = rawRow11632 := by decide +kernel

theorem rowCheck11632 : row11632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11632 := by decide +kernel

theorem rowEval11632 (x : Key → ℝ) : Integer.Sparse.eval row11632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11632, Integer.Sparse.eval_collectBalanced, rawRowCheck11632]

theorem rawRowCheck11633 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form12 = rawRow11633 := by decide +kernel

theorem rowCheck11633 : row11633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11633 := by decide +kernel

theorem rowEval11633 (x : Key → ℝ) : Integer.Sparse.eval row11633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11633, Integer.Sparse.eval_collectBalanced, rawRowCheck11633]

theorem rawRowCheck11634 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form12 = rawRow11634 := by decide +kernel

theorem rowCheck11634 : row11634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11634 := by decide +kernel

theorem rowEval11634 (x : Key → ℝ) : Integer.Sparse.eval row11634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11634, Integer.Sparse.eval_collectBalanced, rawRowCheck11634]

theorem rawRowCheck11635 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form12 = rawRow11635 := by decide +kernel

theorem rowCheck11635 : row11635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11635 := by decide +kernel

theorem rowEval11635 (x : Key → ℝ) : Integer.Sparse.eval row11635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11635, Integer.Sparse.eval_collectBalanced, rawRowCheck11635]

theorem rawRowCheck11636 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form12 = rawRow11636 := by decide +kernel

theorem rowCheck11636 : row11636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11636 := by decide +kernel

theorem rowEval11636 (x : Key → ℝ) : Integer.Sparse.eval row11636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11636, Integer.Sparse.eval_collectBalanced, rawRowCheck11636]

theorem rawRowCheck11637 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form12 = rawRow11637 := by decide +kernel

theorem rowCheck11637 : row11637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11637 := by decide +kernel

theorem rowEval11637 (x : Key → ℝ) : Integer.Sparse.eval row11637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11637, Integer.Sparse.eval_collectBalanced, rawRowCheck11637]

theorem rawRowCheck11638 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form12 = rawRow11638 := by decide +kernel

theorem rowCheck11638 : row11638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11638 := by decide +kernel

theorem rowEval11638 (x : Key → ℝ) : Integer.Sparse.eval row11638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11638, Integer.Sparse.eval_collectBalanced, rawRowCheck11638]

theorem rawRowCheck11639 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form12 = rawRow11639 := by decide +kernel

theorem rowCheck11639 : row11639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11639 := by decide +kernel

theorem rowEval11639 (x : Key → ℝ) : Integer.Sparse.eval row11639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11639, Integer.Sparse.eval_collectBalanced, rawRowCheck11639]

theorem rawRowCheck11640 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form12 = rawRow11640 := by decide +kernel

theorem rowCheck11640 : row11640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11640 := by decide +kernel

theorem rowEval11640 (x : Key → ℝ) : Integer.Sparse.eval row11640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11640, Integer.Sparse.eval_collectBalanced, rawRowCheck11640]

theorem rawRowCheck11641 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form12 = rawRow11641 := by decide +kernel

theorem rowCheck11641 : row11641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11641 := by decide +kernel

theorem rowEval11641 (x : Key → ℝ) : Integer.Sparse.eval row11641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11641, Integer.Sparse.eval_collectBalanced, rawRowCheck11641]

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

theorem entryCheck22_12 : entry22_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_12 k)) := by decide +kernel

theorem rowsSound22_12 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval11630 x
  · exact rowEval11631 x
  · exact rowEval11632 x
  · exact rowEval11633 x
  · exact rowEval11634 x
  · exact rowEval11635 x
  · exact rowEval11636 x
  · exact rowEval11637 x
  · exact rowEval11638 x
  · exact rowEval11639 x
  · exact rowEval11640 x
  · exact rowEval11641 x
  · exact rowEval11126 x
  · exact rowEval11127 x
  · exact rowEval11128 x
  · exact rowEval11129 x
  · exact rowEval11130 x
  · exact rowEval11131 x
  · exact rowEval11132 x
  · exact rowEval11133 x
  · exact rowEval11134 x
  · exact rowEval11135 x
  · exact rowEval11136 x
  · exact rowEval11137 x
  · exact rowEval11138 x
  · exact rowEval11139 x
  · exact rowEval11140 x
  · exact rowEval11141 x
  · exact rowEval11142 x
  · exact rowEval11143 x
  · exact rowEval11144 x
  · exact rowEval11145 x
  · exact rowEval11146 x
  · exact rowEval11147 x
  · exact rowEval11148 x
  · exact rowEval11149 x

theorem entryEval22_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_12 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck22_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_12]

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

theorem rawRowCheck11990 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form12 = rawRow11990 := by decide +kernel

theorem rowCheck11990 : row11990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11990 := by decide +kernel

theorem rowEval11990 (x : Key → ℝ) : Integer.Sparse.eval row11990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11990, Integer.Sparse.eval_collectBalanced, rawRowCheck11990]

theorem rawRowCheck11991 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form12 = rawRow11991 := by decide +kernel

theorem rowCheck11991 : row11991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11991 := by decide +kernel

theorem rowEval11991 (x : Key → ℝ) : Integer.Sparse.eval row11991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11991, Integer.Sparse.eval_collectBalanced, rawRowCheck11991]

theorem rawRowCheck11992 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form12 = rawRow11992 := by decide +kernel

theorem rowCheck11992 : row11992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11992 := by decide +kernel

theorem rowEval11992 (x : Key → ℝ) : Integer.Sparse.eval row11992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11992, Integer.Sparse.eval_collectBalanced, rawRowCheck11992]

theorem rawRowCheck11993 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form12 = rawRow11993 := by decide +kernel

theorem rowCheck11993 : row11993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11993 := by decide +kernel

theorem rowEval11993 (x : Key → ℝ) : Integer.Sparse.eval row11993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11993, Integer.Sparse.eval_collectBalanced, rawRowCheck11993]

theorem rawRowCheck11994 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form12 = rawRow11994 := by decide +kernel

theorem rowCheck11994 : row11994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11994 := by decide +kernel

theorem rowEval11994 (x : Key → ℝ) : Integer.Sparse.eval row11994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11994, Integer.Sparse.eval_collectBalanced, rawRowCheck11994]

theorem rawRowCheck11995 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form12 = rawRow11995 := by decide +kernel

theorem rowCheck11995 : row11995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11995 := by decide +kernel

theorem rowEval11995 (x : Key → ℝ) : Integer.Sparse.eval row11995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11995, Integer.Sparse.eval_collectBalanced, rawRowCheck11995]

theorem rawRowCheck11996 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12 = rawRow11996 := by decide +kernel

theorem rowCheck11996 : row11996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11996 := by decide +kernel

theorem rowEval11996 (x : Key → ℝ) : Integer.Sparse.eval row11996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11996, Integer.Sparse.eval_collectBalanced, rawRowCheck11996]

theorem rawRowCheck11997 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12 = rawRow11997 := by decide +kernel

theorem rowCheck11997 : row11997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11997 := by decide +kernel

theorem rowEval11997 (x : Key → ℝ) : Integer.Sparse.eval row11997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11997, Integer.Sparse.eval_collectBalanced, rawRowCheck11997]

theorem rawRowCheck11998 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12 = rawRow11998 := by decide +kernel

theorem rowCheck11998 : row11998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11998 := by decide +kernel

theorem rowEval11998 (x : Key → ℝ) : Integer.Sparse.eval row11998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11998, Integer.Sparse.eval_collectBalanced, rawRowCheck11998]

theorem rawRowCheck11999 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12 = rawRow11999 := by decide +kernel

theorem rowCheck11999 : row11999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11999 := by decide +kernel

theorem rowEval11999 (x : Key → ℝ) : Integer.Sparse.eval row11999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11999, Integer.Sparse.eval_collectBalanced, rawRowCheck11999]

theorem rawRowCheck12000 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12 = rawRow12000 := by decide +kernel

theorem rowCheck12000 : row12000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12000 := by decide +kernel

theorem rowEval12000 (x : Key → ℝ) : Integer.Sparse.eval row12000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12000, Integer.Sparse.eval_collectBalanced, rawRowCheck12000]

theorem rawRowCheck12001 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12 = rawRow12001 := by decide +kernel

theorem rowCheck12001 : row12001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12001 := by decide +kernel

theorem rowEval12001 (x : Key → ℝ) : Integer.Sparse.eval row12001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12001, Integer.Sparse.eval_collectBalanced, rawRowCheck12001]

theorem rawRowCheck12002 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12 = rawRow12002 := by decide +kernel

theorem rowCheck12002 : row12002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12002 := by decide +kernel

theorem rowEval12002 (x : Key → ℝ) : Integer.Sparse.eval row12002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12002, Integer.Sparse.eval_collectBalanced, rawRowCheck12002]

theorem rawRowCheck12003 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12 = rawRow12003 := by decide +kernel

theorem rowCheck12003 : row12003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12003 := by decide +kernel

theorem rowEval12003 (x : Key → ℝ) : Integer.Sparse.eval row12003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12003, Integer.Sparse.eval_collectBalanced, rawRowCheck12003]

theorem rawRowCheck12004 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12 = rawRow12004 := by decide +kernel

theorem rowCheck12004 : row12004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12004 := by decide +kernel

theorem rowEval12004 (x : Key → ℝ) : Integer.Sparse.eval row12004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12004, Integer.Sparse.eval_collectBalanced, rawRowCheck12004]

theorem rawRowCheck12005 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12 = rawRow12005 := by decide +kernel

theorem rowCheck12005 : row12005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12005 := by decide +kernel

theorem rowEval12005 (x : Key → ℝ) : Integer.Sparse.eval row12005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12005, Integer.Sparse.eval_collectBalanced, rawRowCheck12005]

theorem rawRowCheck12006 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12 = rawRow12006 := by decide +kernel

theorem rowCheck12006 : row12006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12006 := by decide +kernel

theorem rowEval12006 (x : Key → ℝ) : Integer.Sparse.eval row12006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12006, Integer.Sparse.eval_collectBalanced, rawRowCheck12006]

theorem rawRowCheck12007 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12 = rawRow12007 := by decide +kernel

theorem rowCheck12007 : row12007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12007 := by decide +kernel

theorem rowEval12007 (x : Key → ℝ) : Integer.Sparse.eval row12007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12007, Integer.Sparse.eval_collectBalanced, rawRowCheck12007]

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

theorem rawRowCheck12266 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form12 = rawRow12266 := by decide +kernel

theorem rowCheck12266 : row12266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12266 := by decide +kernel

theorem rowEval12266 (x : Key → ℝ) : Integer.Sparse.eval row12266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12266, Integer.Sparse.eval_collectBalanced, rawRowCheck12266]

theorem rawRowCheck12267 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow12267 := by decide +kernel

theorem rowCheck12267 : row12267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12267 := by decide +kernel

theorem rowEval12267 (x : Key → ℝ) : Integer.Sparse.eval row12267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12267, Integer.Sparse.eval_collectBalanced, rawRowCheck12267]

theorem rawRowCheck12268 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form12 = rawRow12268 := by decide +kernel

theorem rowCheck12268 : row12268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12268 := by decide +kernel

theorem rowEval12268 (x : Key → ℝ) : Integer.Sparse.eval row12268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12268, Integer.Sparse.eval_collectBalanced, rawRowCheck12268]

theorem rawRowCheck12269 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form12 = rawRow12269 := by decide +kernel

theorem rowCheck12269 : row12269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12269 := by decide +kernel

theorem rowEval12269 (x : Key → ℝ) : Integer.Sparse.eval row12269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12269, Integer.Sparse.eval_collectBalanced, rawRowCheck12269]

theorem rawRowCheck12270 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form12 = rawRow12270 := by decide +kernel

theorem rowCheck12270 : row12270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12270 := by decide +kernel

theorem rowEval12270 (x : Key → ℝ) : Integer.Sparse.eval row12270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12270, Integer.Sparse.eval_collectBalanced, rawRowCheck12270]

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

theorem entryCheck23_12 : entry23_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_12 k)) := by decide +kernel

theorem rowsSound23_12 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval11990 x
  · exact rowEval11991 x
  · exact rowEval11992 x
  · exact rowEval11993 x
  · exact rowEval11994 x
  · exact rowEval11995 x
  · exact rowEval11996 x
  · exact rowEval11997 x
  · exact rowEval11998 x
  · exact rowEval11999 x
  · exact rowEval12000 x
  · exact rowEval12001 x
  · exact rowEval12002 x
  · exact rowEval12003 x
  · exact rowEval12004 x
  · exact rowEval12005 x
  · exact rowEval12006 x
  · exact rowEval12007 x

theorem entryEval23_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_12 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck23_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_12]

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

theorem entryCheck24_12 : entry24_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_12 k)) := by decide +kernel

theorem rowsSound24_12 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval12266 x
  · exact rowEval12267 x
  · exact rowEval12268 x
  · exact rowEval12269 x
  · exact rowEval12270 x

theorem entryEval24_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_12 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck24_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_12]

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

theorem rawRowCheck12827 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form12 = rawRow12827 := by decide +kernel

theorem rowCheck12827 : row12827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12827 := by decide +kernel

theorem rowEval12827 (x : Key → ℝ) : Integer.Sparse.eval row12827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12827, Integer.Sparse.eval_collectBalanced, rawRowCheck12827]

theorem rawRowCheck12828 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form12 = rawRow12828 := by decide +kernel

theorem rowCheck12828 : row12828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12828 := by decide +kernel

theorem rowEval12828 (x : Key → ℝ) : Integer.Sparse.eval row12828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12828, Integer.Sparse.eval_collectBalanced, rawRowCheck12828]

theorem rawRowCheck12829 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form12 = rawRow12829 := by decide +kernel

theorem rowCheck12829 : row12829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12829 := by decide +kernel

theorem rowEval12829 (x : Key → ℝ) : Integer.Sparse.eval row12829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12829, Integer.Sparse.eval_collectBalanced, rawRowCheck12829]

theorem rawRowCheck12830 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form12 = rawRow12830 := by decide +kernel

theorem rowCheck12830 : row12830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12830 := by decide +kernel

theorem rowEval12830 (x : Key → ℝ) : Integer.Sparse.eval row12830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12830, Integer.Sparse.eval_collectBalanced, rawRowCheck12830]

theorem rawRowCheck12831 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form12 = rawRow12831 := by decide +kernel

theorem rowCheck12831 : row12831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12831 := by decide +kernel

theorem rowEval12831 (x : Key → ℝ) : Integer.Sparse.eval row12831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12831, Integer.Sparse.eval_collectBalanced, rawRowCheck12831]

theorem rawRowCheck12832 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form12 = rawRow12832 := by decide +kernel

theorem rowCheck12832 : row12832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12832 := by decide +kernel

theorem rowEval12832 (x : Key → ℝ) : Integer.Sparse.eval row12832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12832, Integer.Sparse.eval_collectBalanced, rawRowCheck12832]

theorem rawRowCheck12833 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form12 = rawRow12833 := by decide +kernel

theorem rowCheck12833 : row12833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12833 := by decide +kernel

theorem rowEval12833 (x : Key → ℝ) : Integer.Sparse.eval row12833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12833, Integer.Sparse.eval_collectBalanced, rawRowCheck12833]

theorem rawRowCheck12834 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form12 = rawRow12834 := by decide +kernel

theorem rowCheck12834 : row12834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12834 := by decide +kernel

theorem rowEval12834 (x : Key → ℝ) : Integer.Sparse.eval row12834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12834, Integer.Sparse.eval_collectBalanced, rawRowCheck12834]

theorem rawRowCheck12835 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form12 = rawRow12835 := by decide +kernel

theorem rowCheck12835 : row12835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12835 := by decide +kernel

theorem rowEval12835 (x : Key → ℝ) : Integer.Sparse.eval row12835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12835, Integer.Sparse.eval_collectBalanced, rawRowCheck12835]

theorem rawRowCheck12836 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form12 = rawRow12836 := by decide +kernel

theorem rowCheck12836 : row12836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12836 := by decide +kernel

theorem rowEval12836 (x : Key → ℝ) : Integer.Sparse.eval row12836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12836, Integer.Sparse.eval_collectBalanced, rawRowCheck12836]

theorem rawRowCheck12837 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form12 = rawRow12837 := by decide +kernel

theorem rowCheck12837 : row12837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12837 := by decide +kernel

theorem rowEval12837 (x : Key → ℝ) : Integer.Sparse.eval row12837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12837, Integer.Sparse.eval_collectBalanced, rawRowCheck12837]

theorem rawRowCheck12838 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form12 = rawRow12838 := by decide +kernel

theorem rowCheck12838 : row12838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12838 := by decide +kernel

theorem rowEval12838 (x : Key → ℝ) : Integer.Sparse.eval row12838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12838, Integer.Sparse.eval_collectBalanced, rawRowCheck12838]

theorem rawRowCheck12839 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form12 = rawRow12839 := by decide +kernel

theorem rowCheck12839 : row12839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12839 := by decide +kernel

theorem rowEval12839 (x : Key → ℝ) : Integer.Sparse.eval row12839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12839, Integer.Sparse.eval_collectBalanced, rawRowCheck12839]

theorem rawRowCheck12840 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form12 = rawRow12840 := by decide +kernel

theorem rowCheck12840 : row12840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12840 := by decide +kernel

theorem rowEval12840 (x : Key → ℝ) : Integer.Sparse.eval row12840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12840, Integer.Sparse.eval_collectBalanced, rawRowCheck12840]

theorem rawRowCheck12841 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form12 = rawRow12841 := by decide +kernel

theorem rowCheck12841 : row12841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12841 := by decide +kernel

theorem rowEval12841 (x : Key → ℝ) : Integer.Sparse.eval row12841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12841, Integer.Sparse.eval_collectBalanced, rawRowCheck12841]

theorem rawRowCheck12842 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form12 = rawRow12842 := by decide +kernel

theorem rowCheck12842 : row12842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12842 := by decide +kernel

theorem rowEval12842 (x : Key → ℝ) : Integer.Sparse.eval row12842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12842, Integer.Sparse.eval_collectBalanced, rawRowCheck12842]

theorem rawRowCheck12843 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form12 = rawRow12843 := by decide +kernel

theorem rowCheck12843 : row12843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12843 := by decide +kernel

theorem rowEval12843 (x : Key → ℝ) : Integer.Sparse.eval row12843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12843, Integer.Sparse.eval_collectBalanced, rawRowCheck12843]

theorem rawRowCheck12844 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form12 = rawRow12844 := by decide +kernel

theorem rowCheck12844 : row12844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12844 := by decide +kernel

theorem rowEval12844 (x : Key → ℝ) : Integer.Sparse.eval row12844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12844, Integer.Sparse.eval_collectBalanced, rawRowCheck12844]

theorem rawRowCheck12845 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form12 = rawRow12845 := by decide +kernel

theorem rowCheck12845 : row12845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12845 := by decide +kernel

theorem rowEval12845 (x : Key → ℝ) : Integer.Sparse.eval row12845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12845, Integer.Sparse.eval_collectBalanced, rawRowCheck12845]

theorem rawRowCheck12846 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form12 = rawRow12846 := by decide +kernel

theorem rowCheck12846 : row12846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12846 := by decide +kernel

theorem rowEval12846 (x : Key → ℝ) : Integer.Sparse.eval row12846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12846, Integer.Sparse.eval_collectBalanced, rawRowCheck12846]

theorem rawRowCheck12847 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form12 = rawRow12847 := by decide +kernel

theorem rowCheck12847 : row12847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12847 := by decide +kernel

theorem rowEval12847 (x : Key → ℝ) : Integer.Sparse.eval row12847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12847, Integer.Sparse.eval_collectBalanced, rawRowCheck12847]

theorem rawRowCheck12848 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form12 = rawRow12848 := by decide +kernel

theorem rowCheck12848 : row12848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12848 := by decide +kernel

theorem rowEval12848 (x : Key → ℝ) : Integer.Sparse.eval row12848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12848, Integer.Sparse.eval_collectBalanced, rawRowCheck12848]

theorem rawRowCheck12849 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form12 = rawRow12849 := by decide +kernel

theorem rowCheck12849 : row12849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12849 := by decide +kernel

theorem rowEval12849 (x : Key → ℝ) : Integer.Sparse.eval row12849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12849, Integer.Sparse.eval_collectBalanced, rawRowCheck12849]

theorem rawRowCheck12850 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form12 = rawRow12850 := by decide +kernel

theorem rowCheck12850 : row12850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12850 := by decide +kernel

theorem rowEval12850 (x : Key → ℝ) : Integer.Sparse.eval row12850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12850, Integer.Sparse.eval_collectBalanced, rawRowCheck12850]

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

theorem entryCheck26_12 : entry26_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_12 k)) := by decide +kernel

theorem rowsSound26_12 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval12827 x
  · exact rowEval12828 x
  · exact rowEval12829 x
  · exact rowEval12830 x
  · exact rowEval12831 x
  · exact rowEval12832 x
  · exact rowEval12833 x
  · exact rowEval12834 x
  · exact rowEval12835 x
  · exact rowEval12836 x
  · exact rowEval12837 x
  · exact rowEval12838 x
  · exact rowEval12839 x
  · exact rowEval12840 x
  · exact rowEval12841 x
  · exact rowEval12842 x
  · exact rowEval12843 x
  · exact rowEval12844 x
  · exact rowEval12845 x
  · exact rowEval12846 x
  · exact rowEval12847 x
  · exact rowEval12848 x
  · exact rowEval12849 x
  · exact rowEval12850 x

theorem entryEval26_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_12 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck26_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_12]

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

theorem entryEvalRow12_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 12 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 12).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval12_0 B hB
  · exact entryEval12_1 B hB
  · exact entryEval12_2 B hB
  · exact entryEval12_3 B hB
  · exact entryEval12_4 B hB
  · exact entryEval12_5 B hB
  · exact entryEval12_6 B hB
  · exact entryEval12_7 B hB
  · exact entryEval12_8 B hB
  · exact entryEval12_9 B hB
  · exact entryEval12_10 B hB
  · exact entryEval12_11 B hB
  · exact entryEval12_12 B hB
  · exact (entryEval13_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e_oai
