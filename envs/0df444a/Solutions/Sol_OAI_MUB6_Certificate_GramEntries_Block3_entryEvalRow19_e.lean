-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:13:50.519766+00:00
-- url     : https://prove2.me/submissions/0489e946-ea08-407e-b4dd-944adad19df7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E039
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10389 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form0 = rawRow10389 := by decide +kernel

theorem rowCheck10389 : row10389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10389 := by decide +kernel

theorem rowEval10389 (x : Key → ℝ) : Integer.Sparse.eval row10389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10389, Integer.Sparse.eval_collectBalanced, rawRowCheck10389]

theorem rawRowCheck10390 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form0 = rawRow10390 := by decide +kernel

theorem rowCheck10390 : row10390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10390 := by decide +kernel

theorem rowEval10390 (x : Key → ℝ) : Integer.Sparse.eval row10390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10390, Integer.Sparse.eval_collectBalanced, rawRowCheck10390]

theorem rawRowCheck10391 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form0 = rawRow10391 := by decide +kernel

theorem rowCheck10391 : row10391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10391 := by decide +kernel

theorem rowEval10391 (x : Key → ℝ) : Integer.Sparse.eval row10391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10391, Integer.Sparse.eval_collectBalanced, rawRowCheck10391]

theorem rawRowCheck10392 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form0 = rawRow10392 := by decide +kernel

theorem rowCheck10392 : row10392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10392 := by decide +kernel

theorem rowEval10392 (x : Key → ℝ) : Integer.Sparse.eval row10392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10392, Integer.Sparse.eval_collectBalanced, rawRowCheck10392]

theorem rawRowCheck10393 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form0 = rawRow10393 := by decide +kernel

theorem rowCheck10393 : row10393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10393 := by decide +kernel

theorem rowEval10393 (x : Key → ℝ) : Integer.Sparse.eval row10393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10393, Integer.Sparse.eval_collectBalanced, rawRowCheck10393]

theorem rawRowCheck10394 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form0 = rawRow10394 := by decide +kernel

theorem rowCheck10394 : row10394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10394 := by decide +kernel

theorem rowEval10394 (x : Key → ℝ) : Integer.Sparse.eval row10394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10394, Integer.Sparse.eval_collectBalanced, rawRowCheck10394]

theorem rawRowCheck10395 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form0 = rawRow10395 := by decide +kernel

theorem rowCheck10395 : row10395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10395 := by decide +kernel

theorem rowEval10395 (x : Key → ℝ) : Integer.Sparse.eval row10395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10395, Integer.Sparse.eval_collectBalanced, rawRowCheck10395]

theorem rawRowCheck10396 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form0 = rawRow10396 := by decide +kernel

theorem rowCheck10396 : row10396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10396 := by decide +kernel

theorem rowEval10396 (x : Key → ℝ) : Integer.Sparse.eval row10396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10396, Integer.Sparse.eval_collectBalanced, rawRowCheck10396]

theorem rawRowCheck10397 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form0 = rawRow10397 := by decide +kernel

theorem rowCheck10397 : row10397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10397 := by decide +kernel

theorem rowEval10397 (x : Key → ℝ) : Integer.Sparse.eval row10397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10397, Integer.Sparse.eval_collectBalanced, rawRowCheck10397]

theorem rawRowCheck10398 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form0 = rawRow10398 := by decide +kernel

theorem rowCheck10398 : row10398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10398 := by decide +kernel

theorem rowEval10398 (x : Key → ℝ) : Integer.Sparse.eval row10398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10398, Integer.Sparse.eval_collectBalanced, rawRowCheck10398]

theorem rawRowCheck10399 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form1 = rawRow10399 := by decide +kernel

theorem rowCheck10399 : row10399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10399 := by decide +kernel

theorem rowEval10399 (x : Key → ℝ) : Integer.Sparse.eval row10399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10399, Integer.Sparse.eval_collectBalanced, rawRowCheck10399]

theorem rawRowCheck10400 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form1 = rawRow10400 := by decide +kernel

theorem rowCheck10400 : row10400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10400 := by decide +kernel

theorem rowEval10400 (x : Key → ℝ) : Integer.Sparse.eval row10400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10400, Integer.Sparse.eval_collectBalanced, rawRowCheck10400]

theorem rawRowCheck10401 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form1 = rawRow10401 := by decide +kernel

theorem rowCheck10401 : row10401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10401 := by decide +kernel

theorem rowEval10401 (x : Key → ℝ) : Integer.Sparse.eval row10401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10401, Integer.Sparse.eval_collectBalanced, rawRowCheck10401]

theorem rawRowCheck10402 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form1 = rawRow10402 := by decide +kernel

theorem rowCheck10402 : row10402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10402 := by decide +kernel

theorem rowEval10402 (x : Key → ℝ) : Integer.Sparse.eval row10402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10402, Integer.Sparse.eval_collectBalanced, rawRowCheck10402]

theorem rawRowCheck10403 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form1 = rawRow10403 := by decide +kernel

theorem rowCheck10403 : row10403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10403 := by decide +kernel

theorem rowEval10403 (x : Key → ℝ) : Integer.Sparse.eval row10403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10403, Integer.Sparse.eval_collectBalanced, rawRowCheck10403]

theorem rawRowCheck10404 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form1 = rawRow10404 := by decide +kernel

theorem rowCheck10404 : row10404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10404 := by decide +kernel

theorem rowEval10404 (x : Key → ℝ) : Integer.Sparse.eval row10404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10404, Integer.Sparse.eval_collectBalanced, rawRowCheck10404]

theorem rawRowCheck10405 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form1 = rawRow10405 := by decide +kernel

theorem rowCheck10405 : row10405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10405 := by decide +kernel

theorem rowEval10405 (x : Key → ℝ) : Integer.Sparse.eval row10405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10405, Integer.Sparse.eval_collectBalanced, rawRowCheck10405]

theorem rawRowCheck10406 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form1 = rawRow10406 := by decide +kernel

theorem rowCheck10406 : row10406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10406 := by decide +kernel

theorem rowEval10406 (x : Key → ℝ) : Integer.Sparse.eval row10406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10406, Integer.Sparse.eval_collectBalanced, rawRowCheck10406]

theorem rawRowCheck10407 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form1 = rawRow10407 := by decide +kernel

theorem rowCheck10407 : row10407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10407 := by decide +kernel

theorem rowEval10407 (x : Key → ℝ) : Integer.Sparse.eval row10407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10407, Integer.Sparse.eval_collectBalanced, rawRowCheck10407]

theorem rawRowCheck10408 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form1 = rawRow10408 := by decide +kernel

theorem rowCheck10408 : row10408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10408 := by decide +kernel

theorem rowEval10408 (x : Key → ℝ) : Integer.Sparse.eval row10408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10408, Integer.Sparse.eval_collectBalanced, rawRowCheck10408]

theorem rawRowCheck10409 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form2 = rawRow10409 := by decide +kernel

theorem rowCheck10409 : row10409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10409 := by decide +kernel

theorem rowEval10409 (x : Key → ℝ) : Integer.Sparse.eval row10409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10409, Integer.Sparse.eval_collectBalanced, rawRowCheck10409]

theorem rawRowCheck10410 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form2 = rawRow10410 := by decide +kernel

theorem rowCheck10410 : row10410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10410 := by decide +kernel

theorem rowEval10410 (x : Key → ℝ) : Integer.Sparse.eval row10410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10410, Integer.Sparse.eval_collectBalanced, rawRowCheck10410]

theorem rawRowCheck10411 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form2 = rawRow10411 := by decide +kernel

theorem rowCheck10411 : row10411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10411 := by decide +kernel

theorem rowEval10411 (x : Key → ℝ) : Integer.Sparse.eval row10411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10411, Integer.Sparse.eval_collectBalanced, rawRowCheck10411]

theorem rawRowCheck10412 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form2 = rawRow10412 := by decide +kernel

theorem rowCheck10412 : row10412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10412 := by decide +kernel

theorem rowEval10412 (x : Key → ℝ) : Integer.Sparse.eval row10412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10412, Integer.Sparse.eval_collectBalanced, rawRowCheck10412]

theorem rawRowCheck10413 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form2 = rawRow10413 := by decide +kernel

theorem rowCheck10413 : row10413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10413 := by decide +kernel

theorem rowEval10413 (x : Key → ℝ) : Integer.Sparse.eval row10413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10413, Integer.Sparse.eval_collectBalanced, rawRowCheck10413]

theorem rawRowCheck10414 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form2 = rawRow10414 := by decide +kernel

theorem rowCheck10414 : row10414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10414 := by decide +kernel

theorem rowEval10414 (x : Key → ℝ) : Integer.Sparse.eval row10414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10414, Integer.Sparse.eval_collectBalanced, rawRowCheck10414]

theorem rawRowCheck10415 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form2 = rawRow10415 := by decide +kernel

theorem rowCheck10415 : row10415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10415 := by decide +kernel

theorem rowEval10415 (x : Key → ℝ) : Integer.Sparse.eval row10415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10415, Integer.Sparse.eval_collectBalanced, rawRowCheck10415]

theorem rawRowCheck10416 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form2 = rawRow10416 := by decide +kernel

theorem rowCheck10416 : row10416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10416 := by decide +kernel

theorem rowEval10416 (x : Key → ℝ) : Integer.Sparse.eval row10416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10416, Integer.Sparse.eval_collectBalanced, rawRowCheck10416]

theorem rawRowCheck10417 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form2 = rawRow10417 := by decide +kernel

theorem rowCheck10417 : row10417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10417 := by decide +kernel

theorem rowEval10417 (x : Key → ℝ) : Integer.Sparse.eval row10417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10417, Integer.Sparse.eval_collectBalanced, rawRowCheck10417]

theorem rawRowCheck10418 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form2 = rawRow10418 := by decide +kernel

theorem rowCheck10418 : row10418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10418 := by decide +kernel

theorem rowEval10418 (x : Key → ℝ) : Integer.Sparse.eval row10418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10418, Integer.Sparse.eval_collectBalanced, rawRowCheck10418]

theorem rawRowCheck10419 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form3 = rawRow10419 := by decide +kernel

theorem rowCheck10419 : row10419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10419 := by decide +kernel

theorem rowEval10419 (x : Key → ℝ) : Integer.Sparse.eval row10419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10419, Integer.Sparse.eval_collectBalanced, rawRowCheck10419]

theorem rawRowCheck10420 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form3 = rawRow10420 := by decide +kernel

theorem rowCheck10420 : row10420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10420 := by decide +kernel

theorem rowEval10420 (x : Key → ℝ) : Integer.Sparse.eval row10420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10420, Integer.Sparse.eval_collectBalanced, rawRowCheck10420]

theorem rawRowCheck10421 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form3 = rawRow10421 := by decide +kernel

theorem rowCheck10421 : row10421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10421 := by decide +kernel

theorem rowEval10421 (x : Key → ℝ) : Integer.Sparse.eval row10421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10421, Integer.Sparse.eval_collectBalanced, rawRowCheck10421]

theorem rawRowCheck10422 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form3 = rawRow10422 := by decide +kernel

theorem rowCheck10422 : row10422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10422 := by decide +kernel

theorem rowEval10422 (x : Key → ℝ) : Integer.Sparse.eval row10422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10422, Integer.Sparse.eval_collectBalanced, rawRowCheck10422]

theorem rawRowCheck10423 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form3 = rawRow10423 := by decide +kernel

theorem rowCheck10423 : row10423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10423 := by decide +kernel

theorem rowEval10423 (x : Key → ℝ) : Integer.Sparse.eval row10423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10423, Integer.Sparse.eval_collectBalanced, rawRowCheck10423]

theorem rawRowCheck10424 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form3 = rawRow10424 := by decide +kernel

theorem rowCheck10424 : row10424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10424 := by decide +kernel

theorem rowEval10424 (x : Key → ℝ) : Integer.Sparse.eval row10424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10424, Integer.Sparse.eval_collectBalanced, rawRowCheck10424]

theorem rawRowCheck10425 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form3 = rawRow10425 := by decide +kernel

theorem rowCheck10425 : row10425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10425 := by decide +kernel

theorem rowEval10425 (x : Key → ℝ) : Integer.Sparse.eval row10425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10425, Integer.Sparse.eval_collectBalanced, rawRowCheck10425]

theorem rawRowCheck10426 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form3 = rawRow10426 := by decide +kernel

theorem rowCheck10426 : row10426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10426 := by decide +kernel

theorem rowEval10426 (x : Key → ℝ) : Integer.Sparse.eval row10426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10426, Integer.Sparse.eval_collectBalanced, rawRowCheck10426]

theorem rawRowCheck10427 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form3 = rawRow10427 := by decide +kernel

theorem rowCheck10427 : row10427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10427 := by decide +kernel

theorem rowEval10427 (x : Key → ℝ) : Integer.Sparse.eval row10427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10427, Integer.Sparse.eval_collectBalanced, rawRowCheck10427]

theorem rawRowCheck10428 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form3 = rawRow10428 := by decide +kernel

theorem rowCheck10428 : row10428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10428 := by decide +kernel

theorem rowEval10428 (x : Key → ℝ) : Integer.Sparse.eval row10428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10428, Integer.Sparse.eval_collectBalanced, rawRowCheck10428]

theorem rawRowCheck10429 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form4 = rawRow10429 := by decide +kernel

theorem rowCheck10429 : row10429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10429 := by decide +kernel

theorem rowEval10429 (x : Key → ℝ) : Integer.Sparse.eval row10429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10429, Integer.Sparse.eval_collectBalanced, rawRowCheck10429]

theorem rawRowCheck10430 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form4 = rawRow10430 := by decide +kernel

theorem rowCheck10430 : row10430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10430 := by decide +kernel

theorem rowEval10430 (x : Key → ℝ) : Integer.Sparse.eval row10430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10430, Integer.Sparse.eval_collectBalanced, rawRowCheck10430]

theorem rawRowCheck10431 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form4 = rawRow10431 := by decide +kernel

theorem rowCheck10431 : row10431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10431 := by decide +kernel

theorem rowEval10431 (x : Key → ℝ) : Integer.Sparse.eval row10431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10431, Integer.Sparse.eval_collectBalanced, rawRowCheck10431]

theorem rawRowCheck10432 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form4 = rawRow10432 := by decide +kernel

theorem rowCheck10432 : row10432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10432 := by decide +kernel

theorem rowEval10432 (x : Key → ℝ) : Integer.Sparse.eval row10432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10432, Integer.Sparse.eval_collectBalanced, rawRowCheck10432]

theorem rawRowCheck10433 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form4 = rawRow10433 := by decide +kernel

theorem rowCheck10433 : row10433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10433 := by decide +kernel

theorem rowEval10433 (x : Key → ℝ) : Integer.Sparse.eval row10433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10433, Integer.Sparse.eval_collectBalanced, rawRowCheck10433]

theorem rawRowCheck10434 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form4 = rawRow10434 := by decide +kernel

theorem rowCheck10434 : row10434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10434 := by decide +kernel

theorem rowEval10434 (x : Key → ℝ) : Integer.Sparse.eval row10434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10434, Integer.Sparse.eval_collectBalanced, rawRowCheck10434]

theorem rawRowCheck10435 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form4 = rawRow10435 := by decide +kernel

theorem rowCheck10435 : row10435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10435 := by decide +kernel

theorem rowEval10435 (x : Key → ℝ) : Integer.Sparse.eval row10435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10435, Integer.Sparse.eval_collectBalanced, rawRowCheck10435]

theorem rawRowCheck10436 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form4 = rawRow10436 := by decide +kernel

theorem rowCheck10436 : row10436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10436 := by decide +kernel

theorem rowEval10436 (x : Key → ℝ) : Integer.Sparse.eval row10436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10436, Integer.Sparse.eval_collectBalanced, rawRowCheck10436]

theorem rawRowCheck10437 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form4 = rawRow10437 := by decide +kernel

theorem rowCheck10437 : row10437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10437 := by decide +kernel

theorem rowEval10437 (x : Key → ℝ) : Integer.Sparse.eval row10437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10437, Integer.Sparse.eval_collectBalanced, rawRowCheck10437]

theorem rawRowCheck10438 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form4 = rawRow10438 := by decide +kernel

theorem rowCheck10438 : row10438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10438 := by decide +kernel

theorem rowEval10438 (x : Key → ℝ) : Integer.Sparse.eval row10438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10438, Integer.Sparse.eval_collectBalanced, rawRowCheck10438]

theorem rawRowCheck10439 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form5 = rawRow10439 := by decide +kernel

theorem rowCheck10439 : row10439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10439 := by decide +kernel

theorem rowEval10439 (x : Key → ℝ) : Integer.Sparse.eval row10439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10439, Integer.Sparse.eval_collectBalanced, rawRowCheck10439]

theorem rawRowCheck10440 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form5 = rawRow10440 := by decide +kernel

theorem rowCheck10440 : row10440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10440 := by decide +kernel

theorem rowEval10440 (x : Key → ℝ) : Integer.Sparse.eval row10440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10440, Integer.Sparse.eval_collectBalanced, rawRowCheck10440]

theorem rawRowCheck10441 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form5 = rawRow10441 := by decide +kernel

theorem rowCheck10441 : row10441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10441 := by decide +kernel

theorem rowEval10441 (x : Key → ℝ) : Integer.Sparse.eval row10441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10441, Integer.Sparse.eval_collectBalanced, rawRowCheck10441]

theorem rawRowCheck10442 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form5 = rawRow10442 := by decide +kernel

theorem rowCheck10442 : row10442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10442 := by decide +kernel

theorem rowEval10442 (x : Key → ℝ) : Integer.Sparse.eval row10442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10442, Integer.Sparse.eval_collectBalanced, rawRowCheck10442]

theorem rawRowCheck10443 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form5 = rawRow10443 := by decide +kernel

theorem rowCheck10443 : row10443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10443 := by decide +kernel

theorem rowEval10443 (x : Key → ℝ) : Integer.Sparse.eval row10443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10443, Integer.Sparse.eval_collectBalanced, rawRowCheck10443]

theorem rawRowCheck10444 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form5 = rawRow10444 := by decide +kernel

theorem rowCheck10444 : row10444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10444 := by decide +kernel

theorem rowEval10444 (x : Key → ℝ) : Integer.Sparse.eval row10444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10444, Integer.Sparse.eval_collectBalanced, rawRowCheck10444]

theorem rawRowCheck10445 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form5 = rawRow10445 := by decide +kernel

theorem rowCheck10445 : row10445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10445 := by decide +kernel

theorem rowEval10445 (x : Key → ℝ) : Integer.Sparse.eval row10445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10445, Integer.Sparse.eval_collectBalanced, rawRowCheck10445]

theorem rawRowCheck10446 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form5 = rawRow10446 := by decide +kernel

theorem rowCheck10446 : row10446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10446 := by decide +kernel

theorem rowEval10446 (x : Key → ℝ) : Integer.Sparse.eval row10446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10446, Integer.Sparse.eval_collectBalanced, rawRowCheck10446]

theorem rawRowCheck10447 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form5 = rawRow10447 := by decide +kernel

theorem rowCheck10447 : row10447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10447 := by decide +kernel

theorem rowEval10447 (x : Key → ℝ) : Integer.Sparse.eval row10447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10447, Integer.Sparse.eval_collectBalanced, rawRowCheck10447]

theorem rawRowCheck10448 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form5 = rawRow10448 := by decide +kernel

theorem rowCheck10448 : row10448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10448 := by decide +kernel

theorem rowEval10448 (x : Key → ℝ) : Integer.Sparse.eval row10448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10448, Integer.Sparse.eval_collectBalanced, rawRowCheck10448]

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

theorem rawRowCheck10459 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form7 = rawRow10459 := by decide +kernel

theorem rowCheck10459 : row10459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10459 := by decide +kernel

theorem rowEval10459 (x : Key → ℝ) : Integer.Sparse.eval row10459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10459, Integer.Sparse.eval_collectBalanced, rawRowCheck10459]

theorem rawRowCheck10460 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form7 = rawRow10460 := by decide +kernel

theorem rowCheck10460 : row10460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10460 := by decide +kernel

theorem rowEval10460 (x : Key → ℝ) : Integer.Sparse.eval row10460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10460, Integer.Sparse.eval_collectBalanced, rawRowCheck10460]

theorem rawRowCheck10461 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form7 = rawRow10461 := by decide +kernel

theorem rowCheck10461 : row10461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10461 := by decide +kernel

theorem rowEval10461 (x : Key → ℝ) : Integer.Sparse.eval row10461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10461, Integer.Sparse.eval_collectBalanced, rawRowCheck10461]

theorem rawRowCheck10462 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form7 = rawRow10462 := by decide +kernel

theorem rowCheck10462 : row10462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10462 := by decide +kernel

theorem rowEval10462 (x : Key → ℝ) : Integer.Sparse.eval row10462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10462, Integer.Sparse.eval_collectBalanced, rawRowCheck10462]

theorem rawRowCheck10463 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form7 = rawRow10463 := by decide +kernel

theorem rowCheck10463 : row10463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10463 := by decide +kernel

theorem rowEval10463 (x : Key → ℝ) : Integer.Sparse.eval row10463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10463, Integer.Sparse.eval_collectBalanced, rawRowCheck10463]

theorem rawRowCheck10464 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form7 = rawRow10464 := by decide +kernel

theorem rowCheck10464 : row10464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10464 := by decide +kernel

theorem rowEval10464 (x : Key → ℝ) : Integer.Sparse.eval row10464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10464, Integer.Sparse.eval_collectBalanced, rawRowCheck10464]

theorem rawRowCheck10465 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form7 = rawRow10465 := by decide +kernel

theorem rowCheck10465 : row10465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10465 := by decide +kernel

theorem rowEval10465 (x : Key → ℝ) : Integer.Sparse.eval row10465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10465, Integer.Sparse.eval_collectBalanced, rawRowCheck10465]

theorem rawRowCheck10466 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form7 = rawRow10466 := by decide +kernel

theorem rowCheck10466 : row10466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10466 := by decide +kernel

theorem rowEval10466 (x : Key → ℝ) : Integer.Sparse.eval row10466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10466, Integer.Sparse.eval_collectBalanced, rawRowCheck10466]

theorem rawRowCheck10467 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form7 = rawRow10467 := by decide +kernel

theorem rowCheck10467 : row10467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10467 := by decide +kernel

theorem rowEval10467 (x : Key → ℝ) : Integer.Sparse.eval row10467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10467, Integer.Sparse.eval_collectBalanced, rawRowCheck10467]

theorem rawRowCheck10468 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form7 = rawRow10468 := by decide +kernel

theorem rowCheck10468 : row10468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10468 := by decide +kernel

theorem rowEval10468 (x : Key → ℝ) : Integer.Sparse.eval row10468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10468, Integer.Sparse.eval_collectBalanced, rawRowCheck10468]

theorem rawRowCheck10469 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form8 = rawRow10469 := by decide +kernel

theorem rowCheck10469 : row10469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10469 := by decide +kernel

theorem rowEval10469 (x : Key → ℝ) : Integer.Sparse.eval row10469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10469, Integer.Sparse.eval_collectBalanced, rawRowCheck10469]

theorem rawRowCheck10470 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form8 = rawRow10470 := by decide +kernel

theorem rowCheck10470 : row10470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10470 := by decide +kernel

theorem rowEval10470 (x : Key → ℝ) : Integer.Sparse.eval row10470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10470, Integer.Sparse.eval_collectBalanced, rawRowCheck10470]

theorem rawRowCheck10471 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form8 = rawRow10471 := by decide +kernel

theorem rowCheck10471 : row10471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10471 := by decide +kernel

theorem rowEval10471 (x : Key → ℝ) : Integer.Sparse.eval row10471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10471, Integer.Sparse.eval_collectBalanced, rawRowCheck10471]

theorem rawRowCheck10472 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form8 = rawRow10472 := by decide +kernel

theorem rowCheck10472 : row10472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10472 := by decide +kernel

theorem rowEval10472 (x : Key → ℝ) : Integer.Sparse.eval row10472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10472, Integer.Sparse.eval_collectBalanced, rawRowCheck10472]

theorem rawRowCheck10473 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form8 = rawRow10473 := by decide +kernel

theorem rowCheck10473 : row10473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10473 := by decide +kernel

theorem rowEval10473 (x : Key → ℝ) : Integer.Sparse.eval row10473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10473, Integer.Sparse.eval_collectBalanced, rawRowCheck10473]

theorem rawRowCheck10474 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form8 = rawRow10474 := by decide +kernel

theorem rowCheck10474 : row10474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10474 := by decide +kernel

theorem rowEval10474 (x : Key → ℝ) : Integer.Sparse.eval row10474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10474, Integer.Sparse.eval_collectBalanced, rawRowCheck10474]

theorem rawRowCheck10475 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form8 = rawRow10475 := by decide +kernel

theorem rowCheck10475 : row10475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10475 := by decide +kernel

theorem rowEval10475 (x : Key → ℝ) : Integer.Sparse.eval row10475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10475, Integer.Sparse.eval_collectBalanced, rawRowCheck10475]

theorem rawRowCheck10476 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form8 = rawRow10476 := by decide +kernel

theorem rowCheck10476 : row10476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10476 := by decide +kernel

theorem rowEval10476 (x : Key → ℝ) : Integer.Sparse.eval row10476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10476, Integer.Sparse.eval_collectBalanced, rawRowCheck10476]

theorem rawRowCheck10477 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form8 = rawRow10477 := by decide +kernel

theorem rowCheck10477 : row10477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10477 := by decide +kernel

theorem rowEval10477 (x : Key → ℝ) : Integer.Sparse.eval row10477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10477, Integer.Sparse.eval_collectBalanced, rawRowCheck10477]

theorem rawRowCheck10478 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form8 = rawRow10478 := by decide +kernel

theorem rowCheck10478 : row10478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10478 := by decide +kernel

theorem rowEval10478 (x : Key → ℝ) : Integer.Sparse.eval row10478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10478, Integer.Sparse.eval_collectBalanced, rawRowCheck10478]

theorem rawRowCheck10479 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form9 = rawRow10479 := by decide +kernel

theorem rowCheck10479 : row10479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10479 := by decide +kernel

theorem rowEval10479 (x : Key → ℝ) : Integer.Sparse.eval row10479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10479, Integer.Sparse.eval_collectBalanced, rawRowCheck10479]

theorem rawRowCheck10480 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form9 = rawRow10480 := by decide +kernel

theorem rowCheck10480 : row10480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10480 := by decide +kernel

theorem rowEval10480 (x : Key → ℝ) : Integer.Sparse.eval row10480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10480, Integer.Sparse.eval_collectBalanced, rawRowCheck10480]

theorem rawRowCheck10481 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form9 = rawRow10481 := by decide +kernel

theorem rowCheck10481 : row10481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10481 := by decide +kernel

theorem rowEval10481 (x : Key → ℝ) : Integer.Sparse.eval row10481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10481, Integer.Sparse.eval_collectBalanced, rawRowCheck10481]

theorem rawRowCheck10482 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form9 = rawRow10482 := by decide +kernel

theorem rowCheck10482 : row10482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10482 := by decide +kernel

theorem rowEval10482 (x : Key → ℝ) : Integer.Sparse.eval row10482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10482, Integer.Sparse.eval_collectBalanced, rawRowCheck10482]

theorem rawRowCheck10483 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form9 = rawRow10483 := by decide +kernel

theorem rowCheck10483 : row10483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10483 := by decide +kernel

theorem rowEval10483 (x : Key → ℝ) : Integer.Sparse.eval row10483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10483, Integer.Sparse.eval_collectBalanced, rawRowCheck10483]

theorem rawRowCheck10484 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form9 = rawRow10484 := by decide +kernel

theorem rowCheck10484 : row10484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10484 := by decide +kernel

theorem rowEval10484 (x : Key → ℝ) : Integer.Sparse.eval row10484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10484, Integer.Sparse.eval_collectBalanced, rawRowCheck10484]

theorem rawRowCheck10485 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form9 = rawRow10485 := by decide +kernel

theorem rowCheck10485 : row10485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10485 := by decide +kernel

theorem rowEval10485 (x : Key → ℝ) : Integer.Sparse.eval row10485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10485, Integer.Sparse.eval_collectBalanced, rawRowCheck10485]

theorem rawRowCheck10486 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form9 = rawRow10486 := by decide +kernel

theorem rowCheck10486 : row10486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10486 := by decide +kernel

theorem rowEval10486 (x : Key → ℝ) : Integer.Sparse.eval row10486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10486, Integer.Sparse.eval_collectBalanced, rawRowCheck10486]

theorem rawRowCheck10487 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form9 = rawRow10487 := by decide +kernel

theorem rowCheck10487 : row10487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10487 := by decide +kernel

theorem rowEval10487 (x : Key → ℝ) : Integer.Sparse.eval row10487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10487, Integer.Sparse.eval_collectBalanced, rawRowCheck10487]

theorem rawRowCheck10488 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form9 = rawRow10488 := by decide +kernel

theorem rowCheck10488 : row10488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10488 := by decide +kernel

theorem rowEval10488 (x : Key → ℝ) : Integer.Sparse.eval row10488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10488, Integer.Sparse.eval_collectBalanced, rawRowCheck10488]

theorem rawRowCheck10489 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form10 = rawRow10489 := by decide +kernel

theorem rowCheck10489 : row10489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10489 := by decide +kernel

theorem rowEval10489 (x : Key → ℝ) : Integer.Sparse.eval row10489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10489, Integer.Sparse.eval_collectBalanced, rawRowCheck10489]

theorem rawRowCheck10490 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form10 = rawRow10490 := by decide +kernel

theorem rowCheck10490 : row10490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10490 := by decide +kernel

theorem rowEval10490 (x : Key → ℝ) : Integer.Sparse.eval row10490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10490, Integer.Sparse.eval_collectBalanced, rawRowCheck10490]

theorem rawRowCheck10491 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form10 = rawRow10491 := by decide +kernel

theorem rowCheck10491 : row10491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10491 := by decide +kernel

theorem rowEval10491 (x : Key → ℝ) : Integer.Sparse.eval row10491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10491, Integer.Sparse.eval_collectBalanced, rawRowCheck10491]

theorem rawRowCheck10492 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form10 = rawRow10492 := by decide +kernel

theorem rowCheck10492 : row10492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10492 := by decide +kernel

theorem rowEval10492 (x : Key → ℝ) : Integer.Sparse.eval row10492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10492, Integer.Sparse.eval_collectBalanced, rawRowCheck10492]

theorem rawRowCheck10493 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form10 = rawRow10493 := by decide +kernel

theorem rowCheck10493 : row10493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10493 := by decide +kernel

theorem rowEval10493 (x : Key → ℝ) : Integer.Sparse.eval row10493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10493, Integer.Sparse.eval_collectBalanced, rawRowCheck10493]

theorem rawRowCheck10494 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form10 = rawRow10494 := by decide +kernel

theorem rowCheck10494 : row10494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10494 := by decide +kernel

theorem rowEval10494 (x : Key → ℝ) : Integer.Sparse.eval row10494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10494, Integer.Sparse.eval_collectBalanced, rawRowCheck10494]

theorem rawRowCheck10495 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form10 = rawRow10495 := by decide +kernel

theorem rowCheck10495 : row10495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10495 := by decide +kernel

theorem rowEval10495 (x : Key → ℝ) : Integer.Sparse.eval row10495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10495, Integer.Sparse.eval_collectBalanced, rawRowCheck10495]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck10496 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form10 = rawRow10496 := by decide +kernel

theorem rowCheck10496 : row10496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10496 := by decide +kernel

theorem rowEval10496 (x : Key → ℝ) : Integer.Sparse.eval row10496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10496, Integer.Sparse.eval_collectBalanced, rawRowCheck10496]

theorem rawRowCheck10497 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form10 = rawRow10497 := by decide +kernel

theorem rowCheck10497 : row10497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10497 := by decide +kernel

theorem rowEval10497 (x : Key → ℝ) : Integer.Sparse.eval row10497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10497, Integer.Sparse.eval_collectBalanced, rawRowCheck10497]

theorem rawRowCheck10498 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form10 = rawRow10498 := by decide +kernel

theorem rowCheck10498 : row10498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10498 := by decide +kernel

theorem rowEval10498 (x : Key → ℝ) : Integer.Sparse.eval row10498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10498, Integer.Sparse.eval_collectBalanced, rawRowCheck10498]

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

theorem rawRowCheck10519 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form13 = rawRow10519 := by decide +kernel

theorem rowCheck10519 : row10519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10519 := by decide +kernel

theorem rowEval10519 (x : Key → ℝ) : Integer.Sparse.eval row10519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10519, Integer.Sparse.eval_collectBalanced, rawRowCheck10519]

theorem rawRowCheck10520 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form13 = rawRow10520 := by decide +kernel

theorem rowCheck10520 : row10520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10520 := by decide +kernel

theorem rowEval10520 (x : Key → ℝ) : Integer.Sparse.eval row10520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10520, Integer.Sparse.eval_collectBalanced, rawRowCheck10520]

theorem rawRowCheck10521 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form13 = rawRow10521 := by decide +kernel

theorem rowCheck10521 : row10521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10521 := by decide +kernel

theorem rowEval10521 (x : Key → ℝ) : Integer.Sparse.eval row10521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10521, Integer.Sparse.eval_collectBalanced, rawRowCheck10521]

theorem rawRowCheck10522 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form13 = rawRow10522 := by decide +kernel

theorem rowCheck10522 : row10522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10522 := by decide +kernel

theorem rowEval10522 (x : Key → ℝ) : Integer.Sparse.eval row10522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10522, Integer.Sparse.eval_collectBalanced, rawRowCheck10522]

theorem rawRowCheck10523 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form13 = rawRow10523 := by decide +kernel

theorem rowCheck10523 : row10523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10523 := by decide +kernel

theorem rowEval10523 (x : Key → ℝ) : Integer.Sparse.eval row10523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10523, Integer.Sparse.eval_collectBalanced, rawRowCheck10523]

theorem rawRowCheck10524 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form13 = rawRow10524 := by decide +kernel

theorem rowCheck10524 : row10524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10524 := by decide +kernel

theorem rowEval10524 (x : Key → ℝ) : Integer.Sparse.eval row10524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10524, Integer.Sparse.eval_collectBalanced, rawRowCheck10524]

theorem rawRowCheck10525 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form13 = rawRow10525 := by decide +kernel

theorem rowCheck10525 : row10525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10525 := by decide +kernel

theorem rowEval10525 (x : Key → ℝ) : Integer.Sparse.eval row10525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10525, Integer.Sparse.eval_collectBalanced, rawRowCheck10525]

theorem rawRowCheck10526 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form13 = rawRow10526 := by decide +kernel

theorem rowCheck10526 : row10526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10526 := by decide +kernel

theorem rowEval10526 (x : Key → ℝ) : Integer.Sparse.eval row10526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10526, Integer.Sparse.eval_collectBalanced, rawRowCheck10526]

theorem rawRowCheck10527 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form13 = rawRow10527 := by decide +kernel

theorem rowCheck10527 : row10527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10527 := by decide +kernel

theorem rowEval10527 (x : Key → ℝ) : Integer.Sparse.eval row10527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10527, Integer.Sparse.eval_collectBalanced, rawRowCheck10527]

theorem rawRowCheck10528 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form13 = rawRow10528 := by decide +kernel

theorem rowCheck10528 : row10528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10528 := by decide +kernel

theorem rowEval10528 (x : Key → ℝ) : Integer.Sparse.eval row10528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10528, Integer.Sparse.eval_collectBalanced, rawRowCheck10528]

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

theorem rawRowCheck10539 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form15 = rawRow10539 := by decide +kernel

theorem rowCheck10539 : row10539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10539 := by decide +kernel

theorem rowEval10539 (x : Key → ℝ) : Integer.Sparse.eval row10539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10539, Integer.Sparse.eval_collectBalanced, rawRowCheck10539]

theorem rawRowCheck10540 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form15 = rawRow10540 := by decide +kernel

theorem rowCheck10540 : row10540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10540 := by decide +kernel

theorem rowEval10540 (x : Key → ℝ) : Integer.Sparse.eval row10540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10540, Integer.Sparse.eval_collectBalanced, rawRowCheck10540]

theorem rawRowCheck10541 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form15 = rawRow10541 := by decide +kernel

theorem rowCheck10541 : row10541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10541 := by decide +kernel

theorem rowEval10541 (x : Key → ℝ) : Integer.Sparse.eval row10541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10541, Integer.Sparse.eval_collectBalanced, rawRowCheck10541]

theorem rawRowCheck10542 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form15 = rawRow10542 := by decide +kernel

theorem rowCheck10542 : row10542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10542 := by decide +kernel

theorem rowEval10542 (x : Key → ℝ) : Integer.Sparse.eval row10542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10542, Integer.Sparse.eval_collectBalanced, rawRowCheck10542]

theorem rawRowCheck10543 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form15 = rawRow10543 := by decide +kernel

theorem rowCheck10543 : row10543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10543 := by decide +kernel

theorem rowEval10543 (x : Key → ℝ) : Integer.Sparse.eval row10543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10543, Integer.Sparse.eval_collectBalanced, rawRowCheck10543]

theorem rawRowCheck10544 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form15 = rawRow10544 := by decide +kernel

theorem rowCheck10544 : row10544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10544 := by decide +kernel

theorem rowEval10544 (x : Key → ℝ) : Integer.Sparse.eval row10544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10544, Integer.Sparse.eval_collectBalanced, rawRowCheck10544]

theorem rawRowCheck10545 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form15 = rawRow10545 := by decide +kernel

theorem rowCheck10545 : row10545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10545 := by decide +kernel

theorem rowEval10545 (x : Key → ℝ) : Integer.Sparse.eval row10545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10545, Integer.Sparse.eval_collectBalanced, rawRowCheck10545]

theorem rawRowCheck10546 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form15 = rawRow10546 := by decide +kernel

theorem rowCheck10546 : row10546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10546 := by decide +kernel

theorem rowEval10546 (x : Key → ℝ) : Integer.Sparse.eval row10546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10546, Integer.Sparse.eval_collectBalanced, rawRowCheck10546]

theorem rawRowCheck10547 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form15 = rawRow10547 := by decide +kernel

theorem rowCheck10547 : row10547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10547 := by decide +kernel

theorem rowEval10547 (x : Key → ℝ) : Integer.Sparse.eval row10547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10547, Integer.Sparse.eval_collectBalanced, rawRowCheck10547]

theorem rawRowCheck10548 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form15 = rawRow10548 := by decide +kernel

theorem rowCheck10548 : row10548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10548 := by decide +kernel

theorem rowEval10548 (x : Key → ℝ) : Integer.Sparse.eval row10548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10548, Integer.Sparse.eval_collectBalanced, rawRowCheck10548]

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

theorem rawRowCheck10559 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form17 = rawRow10559 := by decide +kernel

theorem rowCheck10559 : row10559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10559 := by decide +kernel

theorem rowEval10559 (x : Key → ℝ) : Integer.Sparse.eval row10559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10559, Integer.Sparse.eval_collectBalanced, rawRowCheck10559]

theorem rawRowCheck10560 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form17 = rawRow10560 := by decide +kernel

theorem rowCheck10560 : row10560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10560 := by decide +kernel

theorem rowEval10560 (x : Key → ℝ) : Integer.Sparse.eval row10560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10560, Integer.Sparse.eval_collectBalanced, rawRowCheck10560]

theorem rawRowCheck10561 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form17 = rawRow10561 := by decide +kernel

theorem rowCheck10561 : row10561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10561 := by decide +kernel

theorem rowEval10561 (x : Key → ℝ) : Integer.Sparse.eval row10561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10561, Integer.Sparse.eval_collectBalanced, rawRowCheck10561]

theorem rawRowCheck10562 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form17 = rawRow10562 := by decide +kernel

theorem rowCheck10562 : row10562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10562 := by decide +kernel

theorem rowEval10562 (x : Key → ℝ) : Integer.Sparse.eval row10562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10562, Integer.Sparse.eval_collectBalanced, rawRowCheck10562]

theorem rawRowCheck10563 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form17 = rawRow10563 := by decide +kernel

theorem rowCheck10563 : row10563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10563 := by decide +kernel

theorem rowEval10563 (x : Key → ℝ) : Integer.Sparse.eval row10563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10563, Integer.Sparse.eval_collectBalanced, rawRowCheck10563]

theorem rawRowCheck10564 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form17 = rawRow10564 := by decide +kernel

theorem rowCheck10564 : row10564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10564 := by decide +kernel

theorem rowEval10564 (x : Key → ℝ) : Integer.Sparse.eval row10564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10564, Integer.Sparse.eval_collectBalanced, rawRowCheck10564]

theorem rawRowCheck10565 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form17 = rawRow10565 := by decide +kernel

theorem rowCheck10565 : row10565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10565 := by decide +kernel

theorem rowEval10565 (x : Key → ℝ) : Integer.Sparse.eval row10565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10565, Integer.Sparse.eval_collectBalanced, rawRowCheck10565]

theorem rawRowCheck10566 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form17 = rawRow10566 := by decide +kernel

theorem rowCheck10566 : row10566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10566 := by decide +kernel

theorem rowEval10566 (x : Key → ℝ) : Integer.Sparse.eval row10566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10566, Integer.Sparse.eval_collectBalanced, rawRowCheck10566]

theorem rawRowCheck10567 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form17 = rawRow10567 := by decide +kernel

theorem rowCheck10567 : row10567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10567 := by decide +kernel

theorem rowEval10567 (x : Key → ℝ) : Integer.Sparse.eval row10567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10567, Integer.Sparse.eval_collectBalanced, rawRowCheck10567]

theorem rawRowCheck10568 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form17 = rawRow10568 := by decide +kernel

theorem rowCheck10568 : row10568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10568 := by decide +kernel

theorem rowEval10568 (x : Key → ℝ) : Integer.Sparse.eval row10568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10568, Integer.Sparse.eval_collectBalanced, rawRowCheck10568]

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

theorem rawRowCheck10579 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form19 = rawRow10579 := by decide +kernel

theorem rowCheck10579 : row10579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10579 := by decide +kernel

theorem rowEval10579 (x : Key → ℝ) : Integer.Sparse.eval row10579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10579, Integer.Sparse.eval_collectBalanced, rawRowCheck10579]

theorem rawRowCheck10580 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form19 = rawRow10580 := by decide +kernel

theorem rowCheck10580 : row10580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10580 := by decide +kernel

theorem rowEval10580 (x : Key → ℝ) : Integer.Sparse.eval row10580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10580, Integer.Sparse.eval_collectBalanced, rawRowCheck10580]

theorem rawRowCheck10581 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form19 = rawRow10581 := by decide +kernel

theorem rowCheck10581 : row10581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10581 := by decide +kernel

theorem rowEval10581 (x : Key → ℝ) : Integer.Sparse.eval row10581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10581, Integer.Sparse.eval_collectBalanced, rawRowCheck10581]

theorem rawRowCheck10582 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form19 = rawRow10582 := by decide +kernel

theorem rowCheck10582 : row10582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10582 := by decide +kernel

theorem rowEval10582 (x : Key → ℝ) : Integer.Sparse.eval row10582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10582, Integer.Sparse.eval_collectBalanced, rawRowCheck10582]

theorem rawRowCheck10583 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form19 = rawRow10583 := by decide +kernel

theorem rowCheck10583 : row10583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10583 := by decide +kernel

theorem rowEval10583 (x : Key → ℝ) : Integer.Sparse.eval row10583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10583, Integer.Sparse.eval_collectBalanced, rawRowCheck10583]

theorem rawRowCheck10584 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form19 = rawRow10584 := by decide +kernel

theorem rowCheck10584 : row10584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10584 := by decide +kernel

theorem rowEval10584 (x : Key → ℝ) : Integer.Sparse.eval row10584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10584, Integer.Sparse.eval_collectBalanced, rawRowCheck10584]

theorem rawRowCheck10585 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form19 = rawRow10585 := by decide +kernel

theorem rowCheck10585 : row10585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10585 := by decide +kernel

theorem rowEval10585 (x : Key → ℝ) : Integer.Sparse.eval row10585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10585, Integer.Sparse.eval_collectBalanced, rawRowCheck10585]

theorem rawRowCheck10586 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form19 = rawRow10586 := by decide +kernel

theorem rowCheck10586 : row10586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10586 := by decide +kernel

theorem rowEval10586 (x : Key → ℝ) : Integer.Sparse.eval row10586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10586, Integer.Sparse.eval_collectBalanced, rawRowCheck10586]

theorem rawRowCheck10587 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form19 = rawRow10587 := by decide +kernel

theorem rowCheck10587 : row10587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10587 := by decide +kernel

theorem rowEval10587 (x : Key → ℝ) : Integer.Sparse.eval row10587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10587, Integer.Sparse.eval_collectBalanced, rawRowCheck10587]

theorem rawRowCheck10588 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form19 = rawRow10588 := by decide +kernel

theorem rowCheck10588 : row10588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10588 := by decide +kernel

theorem rowEval10588 (x : Key → ℝ) : Integer.Sparse.eval row10588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10588, Integer.Sparse.eval_collectBalanced, rawRowCheck10588]

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

theorem entryCheck19_0 : entry19_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_0 k)) := by decide +kernel

theorem rowsSound19_0 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval10389 x
  · exact rowEval10390 x
  · exact rowEval10391 x
  · exact rowEval10392 x
  · exact rowEval10393 x
  · exact rowEval10394 x
  · exact rowEval10395 x
  · exact rowEval10396 x
  · exact rowEval10397 x
  · exact rowEval10398 x

theorem entryEval19_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_0 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck19_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_0]

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval10399 x
  · exact rowEval10400 x
  · exact rowEval10401 x
  · exact rowEval10402 x
  · exact rowEval10403 x
  · exact rowEval10404 x
  · exact rowEval10405 x
  · exact rowEval10406 x
  · exact rowEval10407 x
  · exact rowEval10408 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

theorem entryCheck19_2 : entry19_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_2 k)) := by decide +kernel

theorem rowsSound19_2 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval10409 x
  · exact rowEval10410 x
  · exact rowEval10411 x
  · exact rowEval10412 x
  · exact rowEval10413 x
  · exact rowEval10414 x
  · exact rowEval10415 x
  · exact rowEval10416 x
  · exact rowEval10417 x
  · exact rowEval10418 x

theorem entryEval19_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_2 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck19_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_2]

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval10419 x
  · exact rowEval10420 x
  · exact rowEval10421 x
  · exact rowEval10422 x
  · exact rowEval10423 x
  · exact rowEval10424 x
  · exact rowEval10425 x
  · exact rowEval10426 x
  · exact rowEval10427 x
  · exact rowEval10428 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval10429 x
  · exact rowEval10430 x
  · exact rowEval10431 x
  · exact rowEval10432 x
  · exact rowEval10433 x
  · exact rowEval10434 x
  · exact rowEval10435 x
  · exact rowEval10436 x
  · exact rowEval10437 x
  · exact rowEval10438 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

theorem entryCheck19_5 : entry19_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_5 k)) := by decide +kernel

theorem rowsSound19_5 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval10439 x
  · exact rowEval10440 x
  · exact rowEval10441 x
  · exact rowEval10442 x
  · exact rowEval10443 x
  · exact rowEval10444 x
  · exact rowEval10445 x
  · exact rowEval10446 x
  · exact rowEval10447 x
  · exact rowEval10448 x

theorem entryEval19_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_5 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck19_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_5]

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

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval10459 x
  · exact rowEval10460 x
  · exact rowEval10461 x
  · exact rowEval10462 x
  · exact rowEval10463 x
  · exact rowEval10464 x
  · exact rowEval10465 x
  · exact rowEval10466 x
  · exact rowEval10467 x
  · exact rowEval10468 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval10469 x
  · exact rowEval10470 x
  · exact rowEval10471 x
  · exact rowEval10472 x
  · exact rowEval10473 x
  · exact rowEval10474 x
  · exact rowEval10475 x
  · exact rowEval10476 x
  · exact rowEval10477 x
  · exact rowEval10478 x

theorem entryEval19_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

theorem entryCheck19_9 : entry19_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_9 k)) := by decide +kernel

theorem rowsSound19_9 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval10479 x
  · exact rowEval10480 x
  · exact rowEval10481 x
  · exact rowEval10482 x
  · exact rowEval10483 x
  · exact rowEval10484 x
  · exact rowEval10485 x
  · exact rowEval10486 x
  · exact rowEval10487 x
  · exact rowEval10488 x

theorem entryEval19_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_9 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck19_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_9]

theorem entryCheck19_10 : entry19_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_10 k)) := by decide +kernel

theorem rowsSound19_10 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval10489 x
  · exact rowEval10490 x
  · exact rowEval10491 x
  · exact rowEval10492 x
  · exact rowEval10493 x
  · exact rowEval10494 x
  · exact rowEval10495 x
  · exact rowEval10496 x
  · exact rowEval10497 x
  · exact rowEval10498 x

theorem entryEval19_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_10 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck19_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_10]

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

theorem entryCheck19_13 : entry19_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_13 k)) := by decide +kernel

theorem rowsSound19_13 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval10519 x
  · exact rowEval10520 x
  · exact rowEval10521 x
  · exact rowEval10522 x
  · exact rowEval10523 x
  · exact rowEval10524 x
  · exact rowEval10525 x
  · exact rowEval10526 x
  · exact rowEval10527 x
  · exact rowEval10528 x

theorem entryEval19_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_13 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck19_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_13]

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

theorem entryCheck19_15 : entry19_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_15 k)) := by decide +kernel

theorem rowsSound19_15 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10539 x
  · exact rowEval10540 x
  · exact rowEval10541 x
  · exact rowEval10542 x
  · exact rowEval10543 x
  · exact rowEval10544 x
  · exact rowEval10545 x
  · exact rowEval10546 x
  · exact rowEval10547 x
  · exact rowEval10548 x

theorem entryEval19_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_15 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck19_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_15]

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

theorem entryCheck19_17 : entry19_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_17 k)) := by decide +kernel

theorem rowsSound19_17 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval10559 x
  · exact rowEval10560 x
  · exact rowEval10561 x
  · exact rowEval10562 x
  · exact rowEval10563 x
  · exact rowEval10564 x
  · exact rowEval10565 x
  · exact rowEval10566 x
  · exact rowEval10567 x
  · exact rowEval10568 x

theorem entryEval19_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_17 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck19_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_17]

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

theorem entryCheck19_19 : entry19_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_19 k)) := by decide +kernel

theorem rowsSound19_19 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval10579 x
  · exact rowEval10580 x
  · exact rowEval10581 x
  · exact rowEval10582 x
  · exact rowEval10583 x
  · exact rowEval10584 x
  · exact rowEval10585 x
  · exact rowEval10586 x
  · exact rowEval10587 x
  · exact rowEval10588 x

theorem entryEval19_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_19 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck19_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_19]

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

theorem rawRowCheck10684 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form19 = rawRow10684 := by decide +kernel

theorem rowCheck10684 : row10684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10684 := by decide +kernel

theorem rowEval10684 (x : Key → ℝ) : Integer.Sparse.eval row10684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form19) x := by
  rw [rowCheck10684, Integer.Sparse.eval_collectBalanced, rawRowCheck10684]

theorem rawRowCheck10685 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form19 = rawRow10685 := by decide +kernel

theorem rowCheck10685 : row10685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10685 := by decide +kernel

theorem rowEval10685 (x : Key → ℝ) : Integer.Sparse.eval row10685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10685, Integer.Sparse.eval_collectBalanced, rawRowCheck10685]

theorem rawRowCheck10686 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form19 = rawRow10686 := by decide +kernel

theorem rowCheck10686 : row10686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10686 := by decide +kernel

theorem rowEval10686 (x : Key → ℝ) : Integer.Sparse.eval row10686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10686, Integer.Sparse.eval_collectBalanced, rawRowCheck10686]

theorem rawRowCheck10687 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form19 = rawRow10687 := by decide +kernel

theorem rowCheck10687 : row10687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10687 := by decide +kernel

theorem rowEval10687 (x : Key → ℝ) : Integer.Sparse.eval row10687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10687, Integer.Sparse.eval_collectBalanced, rawRowCheck10687]

theorem rawRowCheck10688 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form19 = rawRow10688 := by decide +kernel

theorem rowCheck10688 : row10688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10688 := by decide +kernel

theorem rowEval10688 (x : Key → ℝ) : Integer.Sparse.eval row10688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10688, Integer.Sparse.eval_collectBalanced, rawRowCheck10688]

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

theorem entryCheck20_19 : entry20_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_19 k)) := by decide +kernel

theorem rowsSound20_19 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval10684 x
  · exact rowEval10685 x
  · exact rowEval10686 x
  · exact rowEval10687 x
  · exact rowEval10688 x

theorem entryEval20_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_19 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck20_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_19]

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

theorem rawRowCheck11378 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form19 = rawRow11378 := by decide +kernel

theorem rowCheck11378 : row11378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11378 := by decide +kernel

theorem rowEval11378 (x : Key → ℝ) : Integer.Sparse.eval row11378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11378, Integer.Sparse.eval_collectBalanced, rawRowCheck11378]

theorem rawRowCheck11379 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form19 = rawRow11379 := by decide +kernel

theorem rowCheck11379 : row11379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11379 := by decide +kernel

theorem rowEval11379 (x : Key → ℝ) : Integer.Sparse.eval row11379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11379, Integer.Sparse.eval_collectBalanced, rawRowCheck11379]

theorem rawRowCheck11380 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form19 = rawRow11380 := by decide +kernel

theorem rowCheck11380 : row11380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11380 := by decide +kernel

theorem rowEval11380 (x : Key → ℝ) : Integer.Sparse.eval row11380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11380, Integer.Sparse.eval_collectBalanced, rawRowCheck11380]

theorem rawRowCheck11381 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form19 = rawRow11381 := by decide +kernel

theorem rowCheck11381 : row11381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11381 := by decide +kernel

theorem rowEval11381 (x : Key → ℝ) : Integer.Sparse.eval row11381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11381, Integer.Sparse.eval_collectBalanced, rawRowCheck11381]

theorem rawRowCheck11382 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form19 = rawRow11382 := by decide +kernel

theorem rowCheck11382 : row11382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11382 := by decide +kernel

theorem rowEval11382 (x : Key → ℝ) : Integer.Sparse.eval row11382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11382, Integer.Sparse.eval_collectBalanced, rawRowCheck11382]

theorem rawRowCheck11383 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form19 = rawRow11383 := by decide +kernel

theorem rowCheck11383 : row11383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11383 := by decide +kernel

theorem rowEval11383 (x : Key → ℝ) : Integer.Sparse.eval row11383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11383, Integer.Sparse.eval_collectBalanced, rawRowCheck11383]

theorem rawRowCheck11384 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form19 = rawRow11384 := by decide +kernel

theorem rowCheck11384 : row11384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11384 := by decide +kernel

theorem rowEval11384 (x : Key → ℝ) : Integer.Sparse.eval row11384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11384, Integer.Sparse.eval_collectBalanced, rawRowCheck11384]

theorem rawRowCheck11385 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form19 = rawRow11385 := by decide +kernel

theorem rowCheck11385 : row11385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11385 := by decide +kernel

theorem rowEval11385 (x : Key → ℝ) : Integer.Sparse.eval row11385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11385, Integer.Sparse.eval_collectBalanced, rawRowCheck11385]

theorem rawRowCheck11386 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form19 = rawRow11386 := by decide +kernel

theorem rowCheck11386 : row11386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11386 := by decide +kernel

theorem rowEval11386 (x : Key → ℝ) : Integer.Sparse.eval row11386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11386, Integer.Sparse.eval_collectBalanced, rawRowCheck11386]

theorem rawRowCheck11387 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form19 = rawRow11387 := by decide +kernel

theorem rowCheck11387 : row11387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11387 := by decide +kernel

theorem rowEval11387 (x : Key → ℝ) : Integer.Sparse.eval row11387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11387, Integer.Sparse.eval_collectBalanced, rawRowCheck11387]

theorem rawRowCheck11388 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form19 = rawRow11388 := by decide +kernel

theorem rowCheck11388 : row11388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11388 := by decide +kernel

theorem rowEval11388 (x : Key → ℝ) : Integer.Sparse.eval row11388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11388, Integer.Sparse.eval_collectBalanced, rawRowCheck11388]

theorem rawRowCheck11389 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form19 = rawRow11389 := by decide +kernel

theorem rowCheck11389 : row11389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11389 := by decide +kernel

theorem rowEval11389 (x : Key → ℝ) : Integer.Sparse.eval row11389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11389, Integer.Sparse.eval_collectBalanced, rawRowCheck11389]

theorem rawRowCheck11390 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form19 = rawRow11390 := by decide +kernel

theorem rowCheck11390 : row11390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11390 := by decide +kernel

theorem rowEval11390 (x : Key → ℝ) : Integer.Sparse.eval row11390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11390, Integer.Sparse.eval_collectBalanced, rawRowCheck11390]

theorem rawRowCheck11391 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form19 = rawRow11391 := by decide +kernel

theorem rowCheck11391 : row11391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11391 := by decide +kernel

theorem rowEval11391 (x : Key → ℝ) : Integer.Sparse.eval row11391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11391, Integer.Sparse.eval_collectBalanced, rawRowCheck11391]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck11392 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form19 = rawRow11392 := by decide +kernel

theorem rowCheck11392 : row11392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11392 := by decide +kernel

theorem rowEval11392 (x : Key → ℝ) : Integer.Sparse.eval row11392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11392, Integer.Sparse.eval_collectBalanced, rawRowCheck11392]

theorem rawRowCheck11393 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form19 = rawRow11393 := by decide +kernel

theorem rowCheck11393 : row11393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11393 := by decide +kernel

theorem rowEval11393 (x : Key → ℝ) : Integer.Sparse.eval row11393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11393, Integer.Sparse.eval_collectBalanced, rawRowCheck11393]

theorem rawRowCheck11394 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form19 = rawRow11394 := by decide +kernel

theorem rowCheck11394 : row11394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11394 := by decide +kernel

theorem rowEval11394 (x : Key → ℝ) : Integer.Sparse.eval row11394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11394, Integer.Sparse.eval_collectBalanced, rawRowCheck11394]

theorem rawRowCheck11395 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form19 = rawRow11395 := by decide +kernel

theorem rowCheck11395 : row11395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11395 := by decide +kernel

theorem rowEval11395 (x : Key → ℝ) : Integer.Sparse.eval row11395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11395, Integer.Sparse.eval_collectBalanced, rawRowCheck11395]

theorem rawRowCheck11396 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form19 = rawRow11396 := by decide +kernel

theorem rowCheck11396 : row11396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11396 := by decide +kernel

theorem rowEval11396 (x : Key → ℝ) : Integer.Sparse.eval row11396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11396, Integer.Sparse.eval_collectBalanced, rawRowCheck11396]

theorem rawRowCheck11397 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form19 = rawRow11397 := by decide +kernel

theorem rowCheck11397 : row11397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11397 := by decide +kernel

theorem rowEval11397 (x : Key → ℝ) : Integer.Sparse.eval row11397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11397, Integer.Sparse.eval_collectBalanced, rawRowCheck11397]

theorem rawRowCheck11398 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form19 = rawRow11398 := by decide +kernel

theorem rowCheck11398 : row11398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11398 := by decide +kernel

theorem rowEval11398 (x : Key → ℝ) : Integer.Sparse.eval row11398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11398, Integer.Sparse.eval_collectBalanced, rawRowCheck11398]

theorem rawRowCheck11399 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form19 = rawRow11399 := by decide +kernel

theorem rowCheck11399 : row11399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11399 := by decide +kernel

theorem rowEval11399 (x : Key → ℝ) : Integer.Sparse.eval row11399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11399, Integer.Sparse.eval_collectBalanced, rawRowCheck11399]

theorem rawRowCheck11400 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form19 = rawRow11400 := by decide +kernel

theorem rowCheck11400 : row11400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11400 := by decide +kernel

theorem rowEval11400 (x : Key → ℝ) : Integer.Sparse.eval row11400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11400, Integer.Sparse.eval_collectBalanced, rawRowCheck11400]

theorem rawRowCheck11401 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form19 = rawRow11401 := by decide +kernel

theorem rowCheck11401 : row11401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11401 := by decide +kernel

theorem rowEval11401 (x : Key → ℝ) : Integer.Sparse.eval row11401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11401, Integer.Sparse.eval_collectBalanced, rawRowCheck11401]

theorem rawRowCheck11402 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form19 = rawRow11402 := by decide +kernel

theorem rowCheck11402 : row11402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11402 := by decide +kernel

theorem rowEval11402 (x : Key → ℝ) : Integer.Sparse.eval row11402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11402, Integer.Sparse.eval_collectBalanced, rawRowCheck11402]

theorem rawRowCheck11403 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form19 = rawRow11403 := by decide +kernel

theorem rowCheck11403 : row11403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11403 := by decide +kernel

theorem rowEval11403 (x : Key → ℝ) : Integer.Sparse.eval row11403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11403, Integer.Sparse.eval_collectBalanced, rawRowCheck11403]

theorem rawRowCheck11404 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form19 = rawRow11404 := by decide +kernel

theorem rowCheck11404 : row11404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11404 := by decide +kernel

theorem rowEval11404 (x : Key → ℝ) : Integer.Sparse.eval row11404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11404, Integer.Sparse.eval_collectBalanced, rawRowCheck11404]

theorem rawRowCheck11405 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form19 = rawRow11405 := by decide +kernel

theorem rowCheck11405 : row11405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11405 := by decide +kernel

theorem rowEval11405 (x : Key → ℝ) : Integer.Sparse.eval row11405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11405, Integer.Sparse.eval_collectBalanced, rawRowCheck11405]

theorem rawRowCheck11406 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form19 = rawRow11406 := by decide +kernel

theorem rowCheck11406 : row11406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11406 := by decide +kernel

theorem rowEval11406 (x : Key → ℝ) : Integer.Sparse.eval row11406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11406, Integer.Sparse.eval_collectBalanced, rawRowCheck11406]

theorem rawRowCheck11407 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form19 = rawRow11407 := by decide +kernel

theorem rowCheck11407 : row11407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11407 := by decide +kernel

theorem rowEval11407 (x : Key → ℝ) : Integer.Sparse.eval row11407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11407, Integer.Sparse.eval_collectBalanced, rawRowCheck11407]

theorem rawRowCheck11408 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form19 = rawRow11408 := by decide +kernel

theorem rowCheck11408 : row11408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11408 := by decide +kernel

theorem rowEval11408 (x : Key → ℝ) : Integer.Sparse.eval row11408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11408, Integer.Sparse.eval_collectBalanced, rawRowCheck11408]

theorem rawRowCheck11409 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form19 = rawRow11409 := by decide +kernel

theorem rowCheck11409 : row11409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11409 := by decide +kernel

theorem rowEval11409 (x : Key → ℝ) : Integer.Sparse.eval row11409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11409, Integer.Sparse.eval_collectBalanced, rawRowCheck11409]

theorem rawRowCheck11410 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form19 = rawRow11410 := by decide +kernel

theorem rowCheck11410 : row11410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11410 := by decide +kernel

theorem rowEval11410 (x : Key → ℝ) : Integer.Sparse.eval row11410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11410, Integer.Sparse.eval_collectBalanced, rawRowCheck11410]

theorem rawRowCheck11411 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form19 = rawRow11411 := by decide +kernel

theorem rowCheck11411 : row11411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11411 := by decide +kernel

theorem rowEval11411 (x : Key → ℝ) : Integer.Sparse.eval row11411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11411, Integer.Sparse.eval_collectBalanced, rawRowCheck11411]

theorem rawRowCheck11412 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form19 = rawRow11412 := by decide +kernel

theorem rowCheck11412 : row11412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11412 := by decide +kernel

theorem rowEval11412 (x : Key → ℝ) : Integer.Sparse.eval row11412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11412, Integer.Sparse.eval_collectBalanced, rawRowCheck11412]

theorem rawRowCheck11413 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form19 = rawRow11413 := by decide +kernel

theorem rowCheck11413 : row11413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11413 := by decide +kernel

theorem rowEval11413 (x : Key → ℝ) : Integer.Sparse.eval row11413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11413, Integer.Sparse.eval_collectBalanced, rawRowCheck11413]

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

theorem entryCheck21_19 : entry21_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_19 k)) := by decide +kernel

theorem rowsSound21_19 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval11378 x
  · exact rowEval11379 x
  · exact rowEval11380 x
  · exact rowEval11381 x
  · exact rowEval11382 x
  · exact rowEval11383 x
  · exact rowEval11384 x
  · exact rowEval11385 x
  · exact rowEval11386 x
  · exact rowEval11387 x
  · exact rowEval11388 x
  · exact rowEval11389 x
  · exact rowEval11390 x
  · exact rowEval11391 x
  · exact rowEval11392 x
  · exact rowEval11393 x
  · exact rowEval11394 x
  · exact rowEval11395 x
  · exact rowEval11396 x
  · exact rowEval11397 x
  · exact rowEval11398 x
  · exact rowEval11399 x
  · exact rowEval11400 x
  · exact rowEval11401 x
  · exact rowEval11402 x
  · exact rowEval11403 x
  · exact rowEval11404 x
  · exact rowEval11405 x
  · exact rowEval11406 x
  · exact rowEval11407 x
  · exact rowEval11408 x
  · exact rowEval11409 x
  · exact rowEval11410 x
  · exact rowEval11411 x
  · exact rowEval11412 x
  · exact rowEval11413 x

theorem entryEval21_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_19 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck21_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_19]

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

theorem rawRowCheck11714 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form19 = rawRow11714 := by decide +kernel

theorem rowCheck11714 : row11714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11714 := by decide +kernel

theorem rowEval11714 (x : Key → ℝ) : Integer.Sparse.eval row11714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11714, Integer.Sparse.eval_collectBalanced, rawRowCheck11714]

theorem rawRowCheck11715 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form19 = rawRow11715 := by decide +kernel

theorem rowCheck11715 : row11715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11715 := by decide +kernel

theorem rowEval11715 (x : Key → ℝ) : Integer.Sparse.eval row11715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11715, Integer.Sparse.eval_collectBalanced, rawRowCheck11715]

theorem rawRowCheck11716 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form19 = rawRow11716 := by decide +kernel

theorem rowCheck11716 : row11716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11716 := by decide +kernel

theorem rowEval11716 (x : Key → ℝ) : Integer.Sparse.eval row11716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11716, Integer.Sparse.eval_collectBalanced, rawRowCheck11716]

theorem rawRowCheck11717 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form19 = rawRow11717 := by decide +kernel

theorem rowCheck11717 : row11717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11717 := by decide +kernel

theorem rowEval11717 (x : Key → ℝ) : Integer.Sparse.eval row11717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11717, Integer.Sparse.eval_collectBalanced, rawRowCheck11717]

theorem rawRowCheck11718 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form19 = rawRow11718 := by decide +kernel

theorem rowCheck11718 : row11718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11718 := by decide +kernel

theorem rowEval11718 (x : Key → ℝ) : Integer.Sparse.eval row11718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11718, Integer.Sparse.eval_collectBalanced, rawRowCheck11718]

theorem rawRowCheck11719 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form19 = rawRow11719 := by decide +kernel

theorem rowCheck11719 : row11719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11719 := by decide +kernel

theorem rowEval11719 (x : Key → ℝ) : Integer.Sparse.eval row11719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11719, Integer.Sparse.eval_collectBalanced, rawRowCheck11719]

theorem rawRowCheck11720 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form19 = rawRow11720 := by decide +kernel

theorem rowCheck11720 : row11720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11720 := by decide +kernel

theorem rowEval11720 (x : Key → ℝ) : Integer.Sparse.eval row11720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11720, Integer.Sparse.eval_collectBalanced, rawRowCheck11720]

theorem rawRowCheck11721 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form19 = rawRow11721 := by decide +kernel

theorem rowCheck11721 : row11721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11721 := by decide +kernel

theorem rowEval11721 (x : Key → ℝ) : Integer.Sparse.eval row11721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11721, Integer.Sparse.eval_collectBalanced, rawRowCheck11721]

theorem rawRowCheck11722 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form19 = rawRow11722 := by decide +kernel

theorem rowCheck11722 : row11722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11722 := by decide +kernel

theorem rowEval11722 (x : Key → ℝ) : Integer.Sparse.eval row11722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11722, Integer.Sparse.eval_collectBalanced, rawRowCheck11722]

theorem rawRowCheck11723 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form19 = rawRow11723 := by decide +kernel

theorem rowCheck11723 : row11723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11723 := by decide +kernel

theorem rowEval11723 (x : Key → ℝ) : Integer.Sparse.eval row11723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11723, Integer.Sparse.eval_collectBalanced, rawRowCheck11723]

theorem rawRowCheck11724 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form19 = rawRow11724 := by decide +kernel

theorem rowCheck11724 : row11724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11724 := by decide +kernel

theorem rowEval11724 (x : Key → ℝ) : Integer.Sparse.eval row11724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11724, Integer.Sparse.eval_collectBalanced, rawRowCheck11724]

theorem rawRowCheck11725 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form19 = rawRow11725 := by decide +kernel

theorem rowCheck11725 : row11725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11725 := by decide +kernel

theorem rowEval11725 (x : Key → ℝ) : Integer.Sparse.eval row11725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11725, Integer.Sparse.eval_collectBalanced, rawRowCheck11725]

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

theorem entryCheck22_19 : entry22_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_19 k)) := by decide +kernel

theorem rowsSound22_19 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval11714 x
  · exact rowEval11715 x
  · exact rowEval11716 x
  · exact rowEval11717 x
  · exact rowEval11718 x
  · exact rowEval11719 x
  · exact rowEval11720 x
  · exact rowEval11721 x
  · exact rowEval11722 x
  · exact rowEval11723 x
  · exact rowEval11724 x
  · exact rowEval11725 x
  · exact rowEval11378 x
  · exact rowEval11379 x
  · exact rowEval11380 x
  · exact rowEval11381 x
  · exact rowEval11382 x
  · exact rowEval11383 x
  · exact rowEval11384 x
  · exact rowEval11385 x
  · exact rowEval11386 x
  · exact rowEval11387 x
  · exact rowEval11388 x
  · exact rowEval11389 x
  · exact rowEval11390 x
  · exact rowEval11391 x
  · exact rowEval11392 x
  · exact rowEval11393 x
  · exact rowEval11394 x
  · exact rowEval11395 x
  · exact rowEval11396 x
  · exact rowEval11397 x
  · exact rowEval11398 x
  · exact rowEval11399 x
  · exact rowEval11400 x
  · exact rowEval11401 x

theorem entryEval22_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_19 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck22_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_19]

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

theorem rawRowCheck12116 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form19 = rawRow12116 := by decide +kernel

theorem rowCheck12116 : row12116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12116 := by decide +kernel

theorem rowEval12116 (x : Key → ℝ) : Integer.Sparse.eval row12116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12116, Integer.Sparse.eval_collectBalanced, rawRowCheck12116]

theorem rawRowCheck12117 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form19 = rawRow12117 := by decide +kernel

theorem rowCheck12117 : row12117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12117 := by decide +kernel

theorem rowEval12117 (x : Key → ℝ) : Integer.Sparse.eval row12117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12117, Integer.Sparse.eval_collectBalanced, rawRowCheck12117]

theorem rawRowCheck12118 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form19 = rawRow12118 := by decide +kernel

theorem rowCheck12118 : row12118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12118 := by decide +kernel

theorem rowEval12118 (x : Key → ℝ) : Integer.Sparse.eval row12118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12118, Integer.Sparse.eval_collectBalanced, rawRowCheck12118]

theorem rawRowCheck12119 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form19 = rawRow12119 := by decide +kernel

theorem rowCheck12119 : row12119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12119 := by decide +kernel

theorem rowEval12119 (x : Key → ℝ) : Integer.Sparse.eval row12119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12119, Integer.Sparse.eval_collectBalanced, rawRowCheck12119]

theorem rawRowCheck12120 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form19 = rawRow12120 := by decide +kernel

theorem rowCheck12120 : row12120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12120 := by decide +kernel

theorem rowEval12120 (x : Key → ℝ) : Integer.Sparse.eval row12120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12120, Integer.Sparse.eval_collectBalanced, rawRowCheck12120]

theorem rawRowCheck12121 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form19 = rawRow12121 := by decide +kernel

theorem rowCheck12121 : row12121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12121 := by decide +kernel

theorem rowEval12121 (x : Key → ℝ) : Integer.Sparse.eval row12121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12121, Integer.Sparse.eval_collectBalanced, rawRowCheck12121]

theorem rawRowCheck12122 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form19 = rawRow12122 := by decide +kernel

theorem rowCheck12122 : row12122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12122 := by decide +kernel

theorem rowEval12122 (x : Key → ℝ) : Integer.Sparse.eval row12122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12122, Integer.Sparse.eval_collectBalanced, rawRowCheck12122]

theorem rawRowCheck12123 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form19 = rawRow12123 := by decide +kernel

theorem rowCheck12123 : row12123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12123 := by decide +kernel

theorem rowEval12123 (x : Key → ℝ) : Integer.Sparse.eval row12123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12123, Integer.Sparse.eval_collectBalanced, rawRowCheck12123]

theorem rawRowCheck12124 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form19 = rawRow12124 := by decide +kernel

theorem rowCheck12124 : row12124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12124 := by decide +kernel

theorem rowEval12124 (x : Key → ℝ) : Integer.Sparse.eval row12124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12124, Integer.Sparse.eval_collectBalanced, rawRowCheck12124]

theorem rawRowCheck12125 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form19 = rawRow12125 := by decide +kernel

theorem rowCheck12125 : row12125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12125 := by decide +kernel

theorem rowEval12125 (x : Key → ℝ) : Integer.Sparse.eval row12125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12125, Integer.Sparse.eval_collectBalanced, rawRowCheck12125]

theorem rawRowCheck12126 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form19 = rawRow12126 := by decide +kernel

theorem rowCheck12126 : row12126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12126 := by decide +kernel

theorem rowEval12126 (x : Key → ℝ) : Integer.Sparse.eval row12126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12126, Integer.Sparse.eval_collectBalanced, rawRowCheck12126]

theorem rawRowCheck12127 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form19 = rawRow12127 := by decide +kernel

theorem rowCheck12127 : row12127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12127 := by decide +kernel

theorem rowEval12127 (x : Key → ℝ) : Integer.Sparse.eval row12127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12127, Integer.Sparse.eval_collectBalanced, rawRowCheck12127]

theorem rawRowCheck12128 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form19 = rawRow12128 := by decide +kernel

theorem rowCheck12128 : row12128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12128 := by decide +kernel

theorem rowEval12128 (x : Key → ℝ) : Integer.Sparse.eval row12128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12128, Integer.Sparse.eval_collectBalanced, rawRowCheck12128]

theorem rawRowCheck12129 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form19 = rawRow12129 := by decide +kernel

theorem rowCheck12129 : row12129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12129 := by decide +kernel

theorem rowEval12129 (x : Key → ℝ) : Integer.Sparse.eval row12129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12129, Integer.Sparse.eval_collectBalanced, rawRowCheck12129]

theorem rawRowCheck12130 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form19 = rawRow12130 := by decide +kernel

theorem rowCheck12130 : row12130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12130 := by decide +kernel

theorem rowEval12130 (x : Key → ℝ) : Integer.Sparse.eval row12130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12130, Integer.Sparse.eval_collectBalanced, rawRowCheck12130]

theorem rawRowCheck12131 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form19 = rawRow12131 := by decide +kernel

theorem rowCheck12131 : row12131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12131 := by decide +kernel

theorem rowEval12131 (x : Key → ℝ) : Integer.Sparse.eval row12131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12131, Integer.Sparse.eval_collectBalanced, rawRowCheck12131]

theorem rawRowCheck12132 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form19 = rawRow12132 := by decide +kernel

theorem rowCheck12132 : row12132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12132 := by decide +kernel

theorem rowEval12132 (x : Key → ℝ) : Integer.Sparse.eval row12132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12132, Integer.Sparse.eval_collectBalanced, rawRowCheck12132]

theorem rawRowCheck12133 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form19 = rawRow12133 := by decide +kernel

theorem rowCheck12133 : row12133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12133 := by decide +kernel

theorem rowEval12133 (x : Key → ℝ) : Integer.Sparse.eval row12133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12133, Integer.Sparse.eval_collectBalanced, rawRowCheck12133]

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

theorem entryCheck23_19 : entry23_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_19 k)) := by decide +kernel

theorem rowsSound23_19 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12116 x
  · exact rowEval12117 x
  · exact rowEval12118 x
  · exact rowEval12119 x
  · exact rowEval12120 x
  · exact rowEval12121 x
  · exact rowEval12122 x
  · exact rowEval12123 x
  · exact rowEval12124 x
  · exact rowEval12125 x
  · exact rowEval12126 x
  · exact rowEval12127 x
  · exact rowEval12128 x
  · exact rowEval12129 x
  · exact rowEval12130 x
  · exact rowEval12131 x
  · exact rowEval12132 x
  · exact rowEval12133 x

theorem entryEval23_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_19 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck23_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_19]

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

theorem rawRowCheck12301 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form19 = rawRow12301 := by decide +kernel

theorem rowCheck12301 : row12301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12301 := by decide +kernel

theorem rowEval12301 (x : Key → ℝ) : Integer.Sparse.eval row12301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12301, Integer.Sparse.eval_collectBalanced, rawRowCheck12301]

theorem rawRowCheck12302 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form19 = rawRow12302 := by decide +kernel

theorem rowCheck12302 : row12302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12302 := by decide +kernel

theorem rowEval12302 (x : Key → ℝ) : Integer.Sparse.eval row12302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12302, Integer.Sparse.eval_collectBalanced, rawRowCheck12302]

theorem rawRowCheck12303 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form19 = rawRow12303 := by decide +kernel

theorem rowCheck12303 : row12303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12303 := by decide +kernel

theorem rowEval12303 (x : Key → ℝ) : Integer.Sparse.eval row12303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12303, Integer.Sparse.eval_collectBalanced, rawRowCheck12303]

theorem rawRowCheck12304 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form19 = rawRow12304 := by decide +kernel

theorem rowCheck12304 : row12304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12304 := by decide +kernel

theorem rowEval12304 (x : Key → ℝ) : Integer.Sparse.eval row12304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12304, Integer.Sparse.eval_collectBalanced, rawRowCheck12304]

theorem rawRowCheck12305 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form19 = rawRow12305 := by decide +kernel

theorem rowCheck12305 : row12305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12305 := by decide +kernel

theorem rowEval12305 (x : Key → ℝ) : Integer.Sparse.eval row12305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck12305, Integer.Sparse.eval_collectBalanced, rawRowCheck12305]

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

theorem entryCheck24_19 : entry24_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_19 k)) := by decide +kernel

theorem rowsSound24_19 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12301 x
  · exact rowEval12302 x
  · exact rowEval12303 x
  · exact rowEval12304 x
  · exact rowEval12305 x

theorem entryEval24_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_19 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck24_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_19]

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

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck12995 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form19 = rawRow12995 := by decide +kernel

theorem rowCheck12995 : row12995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12995 := by decide +kernel

theorem rowEval12995 (x : Key → ℝ) : Integer.Sparse.eval row12995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12995, Integer.Sparse.eval_collectBalanced, rawRowCheck12995]

theorem rawRowCheck12996 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form19 = rawRow12996 := by decide +kernel

theorem rowCheck12996 : row12996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12996 := by decide +kernel

theorem rowEval12996 (x : Key → ℝ) : Integer.Sparse.eval row12996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12996, Integer.Sparse.eval_collectBalanced, rawRowCheck12996]

theorem rawRowCheck12997 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form19 = rawRow12997 := by decide +kernel

theorem rowCheck12997 : row12997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12997 := by decide +kernel

theorem rowEval12997 (x : Key → ℝ) : Integer.Sparse.eval row12997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12997, Integer.Sparse.eval_collectBalanced, rawRowCheck12997]

theorem rawRowCheck12998 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form19 = rawRow12998 := by decide +kernel

theorem rowCheck12998 : row12998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12998 := by decide +kernel

theorem rowEval12998 (x : Key → ℝ) : Integer.Sparse.eval row12998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12998, Integer.Sparse.eval_collectBalanced, rawRowCheck12998]

theorem rawRowCheck12999 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form19 = rawRow12999 := by decide +kernel

theorem rowCheck12999 : row12999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12999 := by decide +kernel

theorem rowEval12999 (x : Key → ℝ) : Integer.Sparse.eval row12999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12999, Integer.Sparse.eval_collectBalanced, rawRowCheck12999]

theorem rawRowCheck13000 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form19 = rawRow13000 := by decide +kernel

theorem rowCheck13000 : row13000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13000 := by decide +kernel

theorem rowEval13000 (x : Key → ℝ) : Integer.Sparse.eval row13000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13000, Integer.Sparse.eval_collectBalanced, rawRowCheck13000]

theorem rawRowCheck13001 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form19 = rawRow13001 := by decide +kernel

theorem rowCheck13001 : row13001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13001 := by decide +kernel

theorem rowEval13001 (x : Key → ℝ) : Integer.Sparse.eval row13001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13001, Integer.Sparse.eval_collectBalanced, rawRowCheck13001]

theorem rawRowCheck13002 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form19 = rawRow13002 := by decide +kernel

theorem rowCheck13002 : row13002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13002 := by decide +kernel

theorem rowEval13002 (x : Key → ℝ) : Integer.Sparse.eval row13002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13002, Integer.Sparse.eval_collectBalanced, rawRowCheck13002]

theorem rawRowCheck13003 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form19 = rawRow13003 := by decide +kernel

theorem rowCheck13003 : row13003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13003 := by decide +kernel

theorem rowEval13003 (x : Key → ℝ) : Integer.Sparse.eval row13003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13003, Integer.Sparse.eval_collectBalanced, rawRowCheck13003]

theorem rawRowCheck13004 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form19 = rawRow13004 := by decide +kernel

theorem rowCheck13004 : row13004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13004 := by decide +kernel

theorem rowEval13004 (x : Key → ℝ) : Integer.Sparse.eval row13004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13004, Integer.Sparse.eval_collectBalanced, rawRowCheck13004]

theorem rawRowCheck13005 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form19 = rawRow13005 := by decide +kernel

theorem rowCheck13005 : row13005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13005 := by decide +kernel

theorem rowEval13005 (x : Key → ℝ) : Integer.Sparse.eval row13005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13005, Integer.Sparse.eval_collectBalanced, rawRowCheck13005]

theorem rawRowCheck13006 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form19 = rawRow13006 := by decide +kernel

theorem rowCheck13006 : row13006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13006 := by decide +kernel

theorem rowEval13006 (x : Key → ℝ) : Integer.Sparse.eval row13006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13006, Integer.Sparse.eval_collectBalanced, rawRowCheck13006]

theorem rawRowCheck13007 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form19 = rawRow13007 := by decide +kernel

theorem rowCheck13007 : row13007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13007 := by decide +kernel

theorem rowEval13007 (x : Key → ℝ) : Integer.Sparse.eval row13007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13007, Integer.Sparse.eval_collectBalanced, rawRowCheck13007]

theorem rawRowCheck13008 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form19 = rawRow13008 := by decide +kernel

theorem rowCheck13008 : row13008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13008 := by decide +kernel

theorem rowEval13008 (x : Key → ℝ) : Integer.Sparse.eval row13008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13008, Integer.Sparse.eval_collectBalanced, rawRowCheck13008]

theorem rawRowCheck13009 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form19 = rawRow13009 := by decide +kernel

theorem rowCheck13009 : row13009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13009 := by decide +kernel

theorem rowEval13009 (x : Key → ℝ) : Integer.Sparse.eval row13009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13009, Integer.Sparse.eval_collectBalanced, rawRowCheck13009]

theorem rawRowCheck13010 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form19 = rawRow13010 := by decide +kernel

theorem rowCheck13010 : row13010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13010 := by decide +kernel

theorem rowEval13010 (x : Key → ℝ) : Integer.Sparse.eval row13010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13010, Integer.Sparse.eval_collectBalanced, rawRowCheck13010]

theorem rawRowCheck13011 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form19 = rawRow13011 := by decide +kernel

theorem rowCheck13011 : row13011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13011 := by decide +kernel

theorem rowEval13011 (x : Key → ℝ) : Integer.Sparse.eval row13011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13011, Integer.Sparse.eval_collectBalanced, rawRowCheck13011]

theorem rawRowCheck13012 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form19 = rawRow13012 := by decide +kernel

theorem rowCheck13012 : row13012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13012 := by decide +kernel

theorem rowEval13012 (x : Key → ℝ) : Integer.Sparse.eval row13012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13012, Integer.Sparse.eval_collectBalanced, rawRowCheck13012]

theorem rawRowCheck13013 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form19 = rawRow13013 := by decide +kernel

theorem rowCheck13013 : row13013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13013 := by decide +kernel

theorem rowEval13013 (x : Key → ℝ) : Integer.Sparse.eval row13013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13013, Integer.Sparse.eval_collectBalanced, rawRowCheck13013]

theorem rawRowCheck13014 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form19 = rawRow13014 := by decide +kernel

theorem rowCheck13014 : row13014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13014 := by decide +kernel

theorem rowEval13014 (x : Key → ℝ) : Integer.Sparse.eval row13014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13014, Integer.Sparse.eval_collectBalanced, rawRowCheck13014]

theorem rawRowCheck13015 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form19 = rawRow13015 := by decide +kernel

theorem rowCheck13015 : row13015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13015 := by decide +kernel

theorem rowEval13015 (x : Key → ℝ) : Integer.Sparse.eval row13015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13015, Integer.Sparse.eval_collectBalanced, rawRowCheck13015]

theorem rawRowCheck13016 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form19 = rawRow13016 := by decide +kernel

theorem rowCheck13016 : row13016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13016 := by decide +kernel

theorem rowEval13016 (x : Key → ℝ) : Integer.Sparse.eval row13016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13016, Integer.Sparse.eval_collectBalanced, rawRowCheck13016]

theorem rawRowCheck13017 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form19 = rawRow13017 := by decide +kernel

theorem rowCheck13017 : row13017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13017 := by decide +kernel

theorem rowEval13017 (x : Key → ℝ) : Integer.Sparse.eval row13017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13017, Integer.Sparse.eval_collectBalanced, rawRowCheck13017]

theorem rawRowCheck13018 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form19 = rawRow13018 := by decide +kernel

theorem rowCheck13018 : row13018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13018 := by decide +kernel

theorem rowEval13018 (x : Key → ℝ) : Integer.Sparse.eval row13018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13018, Integer.Sparse.eval_collectBalanced, rawRowCheck13018]

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

theorem entryCheck26_19 : entry26_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_19 k)) := by decide +kernel

theorem rowsSound26_19 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12995 x
  · exact rowEval12996 x
  · exact rowEval12997 x
  · exact rowEval12998 x
  · exact rowEval12999 x
  · exact rowEval13000 x
  · exact rowEval13001 x
  · exact rowEval13002 x
  · exact rowEval13003 x
  · exact rowEval13004 x
  · exact rowEval13005 x
  · exact rowEval13006 x
  · exact rowEval13007 x
  · exact rowEval13008 x
  · exact rowEval13009 x
  · exact rowEval13010 x
  · exact rowEval13011 x
  · exact rowEval13012 x
  · exact rowEval13013 x
  · exact rowEval13014 x
  · exact rowEval13015 x
  · exact rowEval13016 x
  · exact rowEval13017 x
  · exact rowEval13018 x

theorem entryEval26_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_19 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck26_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_19]

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

theorem entryEvalRow19_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 19 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 19).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval19_0 B hB
  · exact entryEval19_1 B hB
  · exact entryEval19_2 B hB
  · exact entryEval19_3 B hB
  · exact entryEval19_4 B hB
  · exact entryEval19_5 B hB
  · exact entryEval19_6 B hB
  · exact entryEval19_7 B hB
  · exact entryEval19_8 B hB
  · exact entryEval19_9 B hB
  · exact entryEval19_10 B hB
  · exact entryEval19_11 B hB
  · exact entryEval19_12 B hB
  · exact entryEval19_13 B hB
  · exact entryEval19_14 B hB
  · exact entryEval19_15 B hB
  · exact entryEval19_16 B hB
  · exact entryEval19_17 B hB
  · exact entryEval19_18 B hB
  · exact entryEval19_19 B hB
  · exact (entryEval20_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_19 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e_oai
