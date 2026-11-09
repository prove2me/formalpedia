-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T18:17:43.816379+00:00
-- url     : https://prove2.me/submissions/c6aab356-052e-41fc-9ee1-4f78b7d899cd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E038
import Definitions.Def_OAIQ106E041
import Definitions.Def_OAIQ106E044
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19354 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form7 = rawRow19354 := by decide +kernel

theorem rowCheck19354 : row19354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19354 := by decide +kernel

theorem rowEval19354 (x : Key → ℝ) : Integer.Sparse.eval row19354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19354, Integer.Sparse.eval_collectBalanced, rawRowCheck19354]

theorem rawRowCheck19355 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form7 = rawRow19355 := by decide +kernel

theorem rowCheck19355 : row19355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19355 := by decide +kernel

theorem rowEval19355 (x : Key → ℝ) : Integer.Sparse.eval row19355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19355, Integer.Sparse.eval_collectBalanced, rawRowCheck19355]

theorem rawRowCheck19356 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form7 = rawRow19356 := by decide +kernel

theorem rowCheck19356 : row19356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19356 := by decide +kernel

theorem rowEval19356 (x : Key → ℝ) : Integer.Sparse.eval row19356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19356, Integer.Sparse.eval_collectBalanced, rawRowCheck19356]

theorem rawRowCheck19357 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form7 = rawRow19357 := by decide +kernel

theorem rowCheck19357 : row19357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19357 := by decide +kernel

theorem rowEval19357 (x : Key → ℝ) : Integer.Sparse.eval row19357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19357, Integer.Sparse.eval_collectBalanced, rawRowCheck19357]

theorem rawRowCheck19358 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form7 = rawRow19358 := by decide +kernel

theorem rowCheck19358 : row19358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19358 := by decide +kernel

theorem rowEval19358 (x : Key → ℝ) : Integer.Sparse.eval row19358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19358, Integer.Sparse.eval_collectBalanced, rawRowCheck19358]

theorem rawRowCheck19359 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form7 = rawRow19359 := by decide +kernel

theorem rowCheck19359 : row19359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19359 := by decide +kernel

theorem rowEval19359 (x : Key → ℝ) : Integer.Sparse.eval row19359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19359, Integer.Sparse.eval_collectBalanced, rawRowCheck19359]

theorem rawRowCheck19360 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form7 = rawRow19360 := by decide +kernel

theorem rowCheck19360 : row19360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19360 := by decide +kernel

theorem rowEval19360 (x : Key → ℝ) : Integer.Sparse.eval row19360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19360, Integer.Sparse.eval_collectBalanced, rawRowCheck19360]

theorem rawRowCheck19361 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form7 = rawRow19361 := by decide +kernel

theorem rowCheck19361 : row19361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19361 := by decide +kernel

theorem rowEval19361 (x : Key → ℝ) : Integer.Sparse.eval row19361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19361, Integer.Sparse.eval_collectBalanced, rawRowCheck19361]

theorem rawRowCheck19362 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form7 = rawRow19362 := by decide +kernel

theorem rowCheck19362 : row19362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19362 := by decide +kernel

theorem rowEval19362 (x : Key → ℝ) : Integer.Sparse.eval row19362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19362, Integer.Sparse.eval_collectBalanced, rawRowCheck19362]

theorem rawRowCheck19363 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form7 = rawRow19363 := by decide +kernel

theorem rowCheck19363 : row19363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19363 := by decide +kernel

theorem rowEval19363 (x : Key → ℝ) : Integer.Sparse.eval row19363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19363, Integer.Sparse.eval_collectBalanced, rawRowCheck19363]

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

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck20024 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form7 = rawRow20024 := by decide +kernel

theorem rowCheck20024 : row20024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20024 := by decide +kernel

theorem rowEval20024 (x : Key → ℝ) : Integer.Sparse.eval row20024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20024, Integer.Sparse.eval_collectBalanced, rawRowCheck20024]

theorem rawRowCheck20025 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form7 = rawRow20025 := by decide +kernel

theorem rowCheck20025 : row20025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20025 := by decide +kernel

theorem rowEval20025 (x : Key → ℝ) : Integer.Sparse.eval row20025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20025, Integer.Sparse.eval_collectBalanced, rawRowCheck20025]

theorem rawRowCheck20026 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form7 = rawRow20026 := by decide +kernel

theorem rowCheck20026 : row20026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20026 := by decide +kernel

theorem rowEval20026 (x : Key → ℝ) : Integer.Sparse.eval row20026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20026, Integer.Sparse.eval_collectBalanced, rawRowCheck20026]

theorem rawRowCheck20027 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form7 = rawRow20027 := by decide +kernel

theorem rowCheck20027 : row20027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20027 := by decide +kernel

theorem rowEval20027 (x : Key → ℝ) : Integer.Sparse.eval row20027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20027, Integer.Sparse.eval_collectBalanced, rawRowCheck20027]

theorem rawRowCheck20028 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form7 = rawRow20028 := by decide +kernel

theorem rowCheck20028 : row20028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20028 := by decide +kernel

theorem rowEval20028 (x : Key → ℝ) : Integer.Sparse.eval row20028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20028, Integer.Sparse.eval_collectBalanced, rawRowCheck20028]

theorem rawRowCheck20029 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form7 = rawRow20029 := by decide +kernel

theorem rowCheck20029 : row20029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20029 := by decide +kernel

theorem rowEval20029 (x : Key → ℝ) : Integer.Sparse.eval row20029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20029, Integer.Sparse.eval_collectBalanced, rawRowCheck20029]

theorem rawRowCheck20030 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form7 = rawRow20030 := by decide +kernel

theorem rowCheck20030 : row20030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20030 := by decide +kernel

theorem rowEval20030 (x : Key → ℝ) : Integer.Sparse.eval row20030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20030, Integer.Sparse.eval_collectBalanced, rawRowCheck20030]

theorem rawRowCheck20031 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form7 = rawRow20031 := by decide +kernel

theorem rowCheck20031 : row20031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20031 := by decide +kernel

theorem rowEval20031 (x : Key → ℝ) : Integer.Sparse.eval row20031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20031, Integer.Sparse.eval_collectBalanced, rawRowCheck20031]

theorem rawRowCheck20032 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form7 = rawRow20032 := by decide +kernel

theorem rowCheck20032 : row20032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20032 := by decide +kernel

theorem rowEval20032 (x : Key → ℝ) : Integer.Sparse.eval row20032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20032, Integer.Sparse.eval_collectBalanced, rawRowCheck20032]

theorem rawRowCheck20033 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form7 = rawRow20033 := by decide +kernel

theorem rowCheck20033 : row20033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20033 := by decide +kernel

theorem rowEval20033 (x : Key → ℝ) : Integer.Sparse.eval row20033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20033, Integer.Sparse.eval_collectBalanced, rawRowCheck20033]

theorem rawRowCheck20034 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form7 = rawRow20034 := by decide +kernel

theorem rowCheck20034 : row20034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20034 := by decide +kernel

theorem rowEval20034 (x : Key → ℝ) : Integer.Sparse.eval row20034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20034, Integer.Sparse.eval_collectBalanced, rawRowCheck20034]

theorem rawRowCheck20035 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form7 = rawRow20035 := by decide +kernel

theorem rowCheck20035 : row20035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20035 := by decide +kernel

theorem rowEval20035 (x : Key → ℝ) : Integer.Sparse.eval row20035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20035, Integer.Sparse.eval_collectBalanced, rawRowCheck20035]

theorem rawRowCheck20036 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form7 = rawRow20036 := by decide +kernel

theorem rowCheck20036 : row20036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20036 := by decide +kernel

theorem rowEval20036 (x : Key → ℝ) : Integer.Sparse.eval row20036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20036, Integer.Sparse.eval_collectBalanced, rawRowCheck20036]

theorem rawRowCheck20037 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form7 = rawRow20037 := by decide +kernel

theorem rowCheck20037 : row20037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20037 := by decide +kernel

theorem rowEval20037 (x : Key → ℝ) : Integer.Sparse.eval row20037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20037, Integer.Sparse.eval_collectBalanced, rawRowCheck20037]

theorem rawRowCheck20038 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form7 = rawRow20038 := by decide +kernel

theorem rowCheck20038 : row20038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20038 := by decide +kernel

theorem rowEval20038 (x : Key → ℝ) : Integer.Sparse.eval row20038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20038, Integer.Sparse.eval_collectBalanced, rawRowCheck20038]

theorem rawRowCheck20039 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form7 = rawRow20039 := by decide +kernel

theorem rowCheck20039 : row20039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20039 := by decide +kernel

theorem rowEval20039 (x : Key → ℝ) : Integer.Sparse.eval row20039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20039, Integer.Sparse.eval_collectBalanced, rawRowCheck20039]

theorem rawRowCheck20040 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form7 = rawRow20040 := by decide +kernel

theorem rowCheck20040 : row20040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20040 := by decide +kernel

theorem rowEval20040 (x : Key → ℝ) : Integer.Sparse.eval row20040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20040, Integer.Sparse.eval_collectBalanced, rawRowCheck20040]

theorem rawRowCheck20041 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form7 = rawRow20041 := by decide +kernel

theorem rowCheck20041 : row20041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20041 := by decide +kernel

theorem rowEval20041 (x : Key → ℝ) : Integer.Sparse.eval row20041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20041, Integer.Sparse.eval_collectBalanced, rawRowCheck20041]

theorem rawRowCheck20042 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form7 = rawRow20042 := by decide +kernel

theorem rowCheck20042 : row20042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20042 := by decide +kernel

theorem rowEval20042 (x : Key → ℝ) : Integer.Sparse.eval row20042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20042, Integer.Sparse.eval_collectBalanced, rawRowCheck20042]

theorem rawRowCheck20043 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form7 = rawRow20043 := by decide +kernel

theorem rowCheck20043 : row20043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20043 := by decide +kernel

theorem rowEval20043 (x : Key → ℝ) : Integer.Sparse.eval row20043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20043, Integer.Sparse.eval_collectBalanced, rawRowCheck20043]

theorem rawRowCheck20044 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form7 = rawRow20044 := by decide +kernel

theorem rowCheck20044 : row20044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20044 := by decide +kernel

theorem rowEval20044 (x : Key → ℝ) : Integer.Sparse.eval row20044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20044, Integer.Sparse.eval_collectBalanced, rawRowCheck20044]

theorem rawRowCheck20045 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form7 = rawRow20045 := by decide +kernel

theorem rowCheck20045 : row20045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20045 := by decide +kernel

theorem rowEval20045 (x : Key → ℝ) : Integer.Sparse.eval row20045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20045, Integer.Sparse.eval_collectBalanced, rawRowCheck20045]

theorem rawRowCheck20046 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form7 = rawRow20046 := by decide +kernel

theorem rowCheck20046 : row20046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20046 := by decide +kernel

theorem rowEval20046 (x : Key → ℝ) : Integer.Sparse.eval row20046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20046, Integer.Sparse.eval_collectBalanced, rawRowCheck20046]

theorem rawRowCheck20047 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form7 = rawRow20047 := by decide +kernel

theorem rowCheck20047 : row20047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20047 := by decide +kernel

theorem rowEval20047 (x : Key → ℝ) : Integer.Sparse.eval row20047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20047, Integer.Sparse.eval_collectBalanced, rawRowCheck20047]

theorem rawRowCheck20048 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form7 = rawRow20048 := by decide +kernel

theorem rowCheck20048 : row20048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20048 := by decide +kernel

theorem rowEval20048 (x : Key → ℝ) : Integer.Sparse.eval row20048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20048, Integer.Sparse.eval_collectBalanced, rawRowCheck20048]

theorem rawRowCheck20049 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form7 = rawRow20049 := by decide +kernel

theorem rowCheck20049 : row20049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20049 := by decide +kernel

theorem rowEval20049 (x : Key → ℝ) : Integer.Sparse.eval row20049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20049, Integer.Sparse.eval_collectBalanced, rawRowCheck20049]

theorem rawRowCheck20050 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form7 = rawRow20050 := by decide +kernel

theorem rowCheck20050 : row20050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20050 := by decide +kernel

theorem rowEval20050 (x : Key → ℝ) : Integer.Sparse.eval row20050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20050, Integer.Sparse.eval_collectBalanced, rawRowCheck20050]

theorem rawRowCheck20051 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form7 = rawRow20051 := by decide +kernel

theorem rowCheck20051 : row20051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20051 := by decide +kernel

theorem rowEval20051 (x : Key → ℝ) : Integer.Sparse.eval row20051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20051, Integer.Sparse.eval_collectBalanced, rawRowCheck20051]

theorem rawRowCheck20052 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form7 = rawRow20052 := by decide +kernel

theorem rowCheck20052 : row20052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20052 := by decide +kernel

theorem rowEval20052 (x : Key → ℝ) : Integer.Sparse.eval row20052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20052, Integer.Sparse.eval_collectBalanced, rawRowCheck20052]

theorem rawRowCheck20053 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form7 = rawRow20053 := by decide +kernel

theorem rowCheck20053 : row20053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20053 := by decide +kernel

theorem rowEval20053 (x : Key → ℝ) : Integer.Sparse.eval row20053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20053, Integer.Sparse.eval_collectBalanced, rawRowCheck20053]

theorem rawRowCheck20054 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form7 = rawRow20054 := by decide +kernel

theorem rowCheck20054 : row20054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20054 := by decide +kernel

theorem rowEval20054 (x : Key → ℝ) : Integer.Sparse.eval row20054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20054, Integer.Sparse.eval_collectBalanced, rawRowCheck20054]

theorem rawRowCheck20055 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form7 = rawRow20055 := by decide +kernel

theorem rowCheck20055 : row20055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20055 := by decide +kernel

theorem rowEval20055 (x : Key → ℝ) : Integer.Sparse.eval row20055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20055, Integer.Sparse.eval_collectBalanced, rawRowCheck20055]

theorem rawRowCheck20056 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form7 = rawRow20056 := by decide +kernel

theorem rowCheck20056 : row20056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20056 := by decide +kernel

theorem rowEval20056 (x : Key → ℝ) : Integer.Sparse.eval row20056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20056, Integer.Sparse.eval_collectBalanced, rawRowCheck20056]

theorem rawRowCheck20057 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form7 = rawRow20057 := by decide +kernel

theorem rowCheck20057 : row20057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20057 := by decide +kernel

theorem rowEval20057 (x : Key → ℝ) : Integer.Sparse.eval row20057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20057, Integer.Sparse.eval_collectBalanced, rawRowCheck20057]

theorem rawRowCheck20058 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form7 = rawRow20058 := by decide +kernel

theorem rowCheck20058 : row20058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20058 := by decide +kernel

theorem rowEval20058 (x : Key → ℝ) : Integer.Sparse.eval row20058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20058, Integer.Sparse.eval_collectBalanced, rawRowCheck20058]

theorem rawRowCheck20059 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form7 = rawRow20059 := by decide +kernel

theorem rowCheck20059 : row20059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20059 := by decide +kernel

theorem rowEval20059 (x : Key → ℝ) : Integer.Sparse.eval row20059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20059, Integer.Sparse.eval_collectBalanced, rawRowCheck20059]

theorem rawRowCheck20060 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form7 = rawRow20060 := by decide +kernel

theorem rowCheck20060 : row20060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20060 := by decide +kernel

theorem rowEval20060 (x : Key → ℝ) : Integer.Sparse.eval row20060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20060, Integer.Sparse.eval_collectBalanced, rawRowCheck20060]

theorem rawRowCheck20061 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form7 = rawRow20061 := by decide +kernel

theorem rowCheck20061 : row20061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20061 := by decide +kernel

theorem rowEval20061 (x : Key → ℝ) : Integer.Sparse.eval row20061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20061, Integer.Sparse.eval_collectBalanced, rawRowCheck20061]

theorem rawRowCheck20062 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form7 = rawRow20062 := by decide +kernel

theorem rowCheck20062 : row20062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20062 := by decide +kernel

theorem rowEval20062 (x : Key → ℝ) : Integer.Sparse.eval row20062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20062, Integer.Sparse.eval_collectBalanced, rawRowCheck20062]

theorem rawRowCheck20063 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form7 = rawRow20063 := by decide +kernel

theorem rowCheck20063 : row20063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20063 := by decide +kernel

theorem rowEval20063 (x : Key → ℝ) : Integer.Sparse.eval row20063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20063, Integer.Sparse.eval_collectBalanced, rawRowCheck20063]

theorem rawRowCheck20064 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form7 = rawRow20064 := by decide +kernel

theorem rowCheck20064 : row20064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20064 := by decide +kernel

theorem rowEval20064 (x : Key → ℝ) : Integer.Sparse.eval row20064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20064, Integer.Sparse.eval_collectBalanced, rawRowCheck20064]

theorem rawRowCheck20065 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form7 = rawRow20065 := by decide +kernel

theorem rowCheck20065 : row20065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20065 := by decide +kernel

theorem rowEval20065 (x : Key → ℝ) : Integer.Sparse.eval row20065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20065, Integer.Sparse.eval_collectBalanced, rawRowCheck20065]

theorem rawRowCheck20066 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form7 = rawRow20066 := by decide +kernel

theorem rowCheck20066 : row20066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20066 := by decide +kernel

theorem rowEval20066 (x : Key → ℝ) : Integer.Sparse.eval row20066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20066, Integer.Sparse.eval_collectBalanced, rawRowCheck20066]

theorem rawRowCheck20067 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form7 = rawRow20067 := by decide +kernel

theorem rowCheck20067 : row20067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20067 := by decide +kernel

theorem rowEval20067 (x : Key → ℝ) : Integer.Sparse.eval row20067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20067, Integer.Sparse.eval_collectBalanced, rawRowCheck20067]

theorem rawRowCheck20068 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form7 = rawRow20068 := by decide +kernel

theorem rowCheck20068 : row20068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20068 := by decide +kernel

theorem rowEval20068 (x : Key → ℝ) : Integer.Sparse.eval row20068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20068, Integer.Sparse.eval_collectBalanced, rawRowCheck20068]

theorem rawRowCheck20069 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form7 = rawRow20069 := by decide +kernel

theorem rowCheck20069 : row20069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20069 := by decide +kernel

theorem rowEval20069 (x : Key → ℝ) : Integer.Sparse.eval row20069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20069, Integer.Sparse.eval_collectBalanced, rawRowCheck20069]

theorem rawRowCheck20070 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form7 = rawRow20070 := by decide +kernel

theorem rowCheck20070 : row20070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20070 := by decide +kernel

theorem rowEval20070 (x : Key → ℝ) : Integer.Sparse.eval row20070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20070, Integer.Sparse.eval_collectBalanced, rawRowCheck20070]

theorem rawRowCheck20071 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form7 = rawRow20071 := by decide +kernel

theorem rowCheck20071 : row20071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20071 := by decide +kernel

theorem rowEval20071 (x : Key → ℝ) : Integer.Sparse.eval row20071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20071, Integer.Sparse.eval_collectBalanced, rawRowCheck20071]

theorem rawRowCheck20072 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form7 = rawRow20072 := by decide +kernel

theorem rowCheck20072 : row20072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20072 := by decide +kernel

theorem rowEval20072 (x : Key → ℝ) : Integer.Sparse.eval row20072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20072, Integer.Sparse.eval_collectBalanced, rawRowCheck20072]

theorem rawRowCheck20073 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form7 = rawRow20073 := by decide +kernel

theorem rowCheck20073 : row20073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20073 := by decide +kernel

theorem rowEval20073 (x : Key → ℝ) : Integer.Sparse.eval row20073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20073, Integer.Sparse.eval_collectBalanced, rawRowCheck20073]

theorem rawRowCheck20074 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form7 = rawRow20074 := by decide +kernel

theorem rowCheck20074 : row20074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20074 := by decide +kernel

theorem rowEval20074 (x : Key → ℝ) : Integer.Sparse.eval row20074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20074, Integer.Sparse.eval_collectBalanced, rawRowCheck20074]

theorem rawRowCheck20075 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form7 = rawRow20075 := by decide +kernel

theorem rowCheck20075 : row20075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20075 := by decide +kernel

theorem rowEval20075 (x : Key → ℝ) : Integer.Sparse.eval row20075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20075, Integer.Sparse.eval_collectBalanced, rawRowCheck20075]

theorem rawRowCheck20076 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form7 = rawRow20076 := by decide +kernel

theorem rowCheck20076 : row20076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20076 := by decide +kernel

theorem rowEval20076 (x : Key → ℝ) : Integer.Sparse.eval row20076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20076, Integer.Sparse.eval_collectBalanced, rawRowCheck20076]

theorem rawRowCheck20077 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form7 = rawRow20077 := by decide +kernel

theorem rowCheck20077 : row20077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20077 := by decide +kernel

theorem rowEval20077 (x : Key → ℝ) : Integer.Sparse.eval row20077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20077, Integer.Sparse.eval_collectBalanced, rawRowCheck20077]

theorem rawRowCheck20078 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form7 = rawRow20078 := by decide +kernel

theorem rowCheck20078 : row20078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20078 := by decide +kernel

theorem rowEval20078 (x : Key → ℝ) : Integer.Sparse.eval row20078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20078, Integer.Sparse.eval_collectBalanced, rawRowCheck20078]

theorem rawRowCheck20079 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form7 = rawRow20079 := by decide +kernel

theorem rowCheck20079 : row20079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20079 := by decide +kernel

theorem rowEval20079 (x : Key → ℝ) : Integer.Sparse.eval row20079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20079, Integer.Sparse.eval_collectBalanced, rawRowCheck20079]

theorem rawRowCheck20080 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form7 = rawRow20080 := by decide +kernel

theorem rowCheck20080 : row20080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20080 := by decide +kernel

theorem rowEval20080 (x : Key → ℝ) : Integer.Sparse.eval row20080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20080, Integer.Sparse.eval_collectBalanced, rawRowCheck20080]

theorem rawRowCheck20081 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form7 = rawRow20081 := by decide +kernel

theorem rowCheck20081 : row20081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20081 := by decide +kernel

theorem rowEval20081 (x : Key → ℝ) : Integer.Sparse.eval row20081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20081, Integer.Sparse.eval_collectBalanced, rawRowCheck20081]

theorem rawRowCheck20082 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form7 = rawRow20082 := by decide +kernel

theorem rowCheck20082 : row20082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20082 := by decide +kernel

theorem rowEval20082 (x : Key → ℝ) : Integer.Sparse.eval row20082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20082, Integer.Sparse.eval_collectBalanced, rawRowCheck20082]

theorem rawRowCheck20083 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form7 = rawRow20083 := by decide +kernel

theorem rowCheck20083 : row20083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20083 := by decide +kernel

theorem rowEval20083 (x : Key → ℝ) : Integer.Sparse.eval row20083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20083, Integer.Sparse.eval_collectBalanced, rawRowCheck20083]

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

theorem entryCheck11_7 : entry11_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_7 k)) := by decide +kernel

theorem rowsSound11_7 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval20024 x
  · exact rowEval20025 x
  · exact rowEval20026 x
  · exact rowEval20027 x
  · exact rowEval20028 x
  · exact rowEval20029 x
  · exact rowEval20030 x
  · exact rowEval20031 x
  · exact rowEval20032 x
  · exact rowEval20033 x
  · exact rowEval20034 x
  · exact rowEval20035 x
  · exact rowEval20036 x
  · exact rowEval20037 x
  · exact rowEval20038 x
  · exact rowEval20039 x
  · exact rowEval20040 x
  · exact rowEval20041 x
  · exact rowEval20042 x
  · exact rowEval20043 x
  · exact rowEval20044 x
  · exact rowEval20045 x
  · exact rowEval20046 x
  · exact rowEval20047 x
  · exact rowEval20048 x
  · exact rowEval20049 x
  · exact rowEval20050 x
  · exact rowEval20051 x
  · exact rowEval20052 x
  · exact rowEval20053 x
  · exact rowEval20054 x
  · exact rowEval20055 x
  · exact rowEval20056 x
  · exact rowEval20057 x
  · exact rowEval20058 x
  · exact rowEval20059 x
  · exact rowEval20060 x
  · exact rowEval20061 x
  · exact rowEval20062 x
  · exact rowEval20063 x
  · exact rowEval20064 x
  · exact rowEval20065 x
  · exact rowEval20066 x
  · exact rowEval20067 x
  · exact rowEval20068 x
  · exact rowEval20069 x
  · exact rowEval20070 x
  · exact rowEval20071 x
  · exact rowEval20072 x
  · exact rowEval20073 x
  · exact rowEval20074 x
  · exact rowEval20075 x
  · exact rowEval20076 x
  · exact rowEval20077 x
  · exact rowEval20078 x
  · exact rowEval20079 x
  · exact rowEval20080 x
  · exact rowEval20081 x
  · exact rowEval20082 x
  · exact rowEval20083 x

theorem entryEval11_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_7 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck11_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_7]

end MUB6.Certificate.GramEntries.Block5

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

theorem rawRowCheck19079 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19079 := by decide +kernel

theorem rowCheck19079 : row19079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19079 := by decide +kernel

theorem rowEval19079 (x : Key → ℝ) : Integer.Sparse.eval row19079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19079, Integer.Sparse.eval_collectBalanced, rawRowCheck19079]

theorem rawRowCheck19080 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19080 := by decide +kernel

theorem rowCheck19080 : row19080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19080 := by decide +kernel

theorem rowEval19080 (x : Key → ℝ) : Integer.Sparse.eval row19080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19080, Integer.Sparse.eval_collectBalanced, rawRowCheck19080]

theorem rawRowCheck19081 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19081 := by decide +kernel

theorem rowCheck19081 : row19081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19081 := by decide +kernel

theorem rowEval19081 (x : Key → ℝ) : Integer.Sparse.eval row19081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19081, Integer.Sparse.eval_collectBalanced, rawRowCheck19081]

theorem rawRowCheck19082 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19082 := by decide +kernel

theorem rowCheck19082 : row19082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19082 := by decide +kernel

theorem rowEval19082 (x : Key → ℝ) : Integer.Sparse.eval row19082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19082, Integer.Sparse.eval_collectBalanced, rawRowCheck19082]

theorem rawRowCheck19083 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19083 := by decide +kernel

theorem rowCheck19083 : row19083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19083 := by decide +kernel

theorem rowEval19083 (x : Key → ℝ) : Integer.Sparse.eval row19083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19083, Integer.Sparse.eval_collectBalanced, rawRowCheck19083]

theorem rawRowCheck19084 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19084 := by decide +kernel

theorem rowCheck19084 : row19084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19084 := by decide +kernel

theorem rowEval19084 (x : Key → ℝ) : Integer.Sparse.eval row19084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19084, Integer.Sparse.eval_collectBalanced, rawRowCheck19084]

theorem rawRowCheck19085 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19085 := by decide +kernel

theorem rowCheck19085 : row19085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19085 := by decide +kernel

theorem rowEval19085 (x : Key → ℝ) : Integer.Sparse.eval row19085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19085, Integer.Sparse.eval_collectBalanced, rawRowCheck19085]

theorem rawRowCheck19086 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19086 := by decide +kernel

theorem rowCheck19086 : row19086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19086 := by decide +kernel

theorem rowEval19086 (x : Key → ℝ) : Integer.Sparse.eval row19086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19086, Integer.Sparse.eval_collectBalanced, rawRowCheck19086]

theorem rawRowCheck19087 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19087 := by decide +kernel

theorem rowCheck19087 : row19087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19087 := by decide +kernel

theorem rowEval19087 (x : Key → ℝ) : Integer.Sparse.eval row19087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19087, Integer.Sparse.eval_collectBalanced, rawRowCheck19087]

theorem rawRowCheck19088 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19088 := by decide +kernel

theorem rowCheck19088 : row19088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19088 := by decide +kernel

theorem rowEval19088 (x : Key → ℝ) : Integer.Sparse.eval row19088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19088, Integer.Sparse.eval_collectBalanced, rawRowCheck19088]

theorem rawRowCheck19089 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19089 := by decide +kernel

theorem rowCheck19089 : row19089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19089 := by decide +kernel

theorem rowEval19089 (x : Key → ℝ) : Integer.Sparse.eval row19089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19089, Integer.Sparse.eval_collectBalanced, rawRowCheck19089]

theorem rawRowCheck19090 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19090 := by decide +kernel

theorem rowCheck19090 : row19090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19090 := by decide +kernel

theorem rowEval19090 (x : Key → ℝ) : Integer.Sparse.eval row19090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19090, Integer.Sparse.eval_collectBalanced, rawRowCheck19090]

theorem rawRowCheck19091 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19091 := by decide +kernel

theorem rowCheck19091 : row19091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19091 := by decide +kernel

theorem rowEval19091 (x : Key → ℝ) : Integer.Sparse.eval row19091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19091, Integer.Sparse.eval_collectBalanced, rawRowCheck19091]

theorem rawRowCheck19092 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19092 := by decide +kernel

theorem rowCheck19092 : row19092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19092 := by decide +kernel

theorem rowEval19092 (x : Key → ℝ) : Integer.Sparse.eval row19092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19092, Integer.Sparse.eval_collectBalanced, rawRowCheck19092]

theorem rawRowCheck19093 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19093 := by decide +kernel

theorem rowCheck19093 : row19093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19093 := by decide +kernel

theorem rowEval19093 (x : Key → ℝ) : Integer.Sparse.eval row19093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19093, Integer.Sparse.eval_collectBalanced, rawRowCheck19093]

theorem rawRowCheck19094 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19094 := by decide +kernel

theorem rowCheck19094 : row19094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19094 := by decide +kernel

theorem rowEval19094 (x : Key → ℝ) : Integer.Sparse.eval row19094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19094, Integer.Sparse.eval_collectBalanced, rawRowCheck19094]

theorem rawRowCheck19095 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19095 := by decide +kernel

theorem rowCheck19095 : row19095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19095 := by decide +kernel

theorem rowEval19095 (x : Key → ℝ) : Integer.Sparse.eval row19095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19095, Integer.Sparse.eval_collectBalanced, rawRowCheck19095]

theorem rawRowCheck19096 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19096 := by decide +kernel

theorem rowCheck19096 : row19096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19096 := by decide +kernel

theorem rowEval19096 (x : Key → ℝ) : Integer.Sparse.eval row19096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19096, Integer.Sparse.eval_collectBalanced, rawRowCheck19096]

theorem rawRowCheck19097 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19097 := by decide +kernel

theorem rowCheck19097 : row19097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19097 := by decide +kernel

theorem rowEval19097 (x : Key → ℝ) : Integer.Sparse.eval row19097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19097, Integer.Sparse.eval_collectBalanced, rawRowCheck19097]

theorem rawRowCheck19098 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19098 := by decide +kernel

theorem rowCheck19098 : row19098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19098 := by decide +kernel

theorem rowEval19098 (x : Key → ℝ) : Integer.Sparse.eval row19098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19098, Integer.Sparse.eval_collectBalanced, rawRowCheck19098]

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

theorem rawRowCheck19119 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19119 := by decide +kernel

theorem rowCheck19119 : row19119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19119 := by decide +kernel

theorem rowEval19119 (x : Key → ℝ) : Integer.Sparse.eval row19119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19119, Integer.Sparse.eval_collectBalanced, rawRowCheck19119]

theorem rawRowCheck19120 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form2 = rawRow19120 := by decide +kernel

theorem rowCheck19120 : row19120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19120 := by decide +kernel

theorem rowEval19120 (x : Key → ℝ) : Integer.Sparse.eval row19120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19120, Integer.Sparse.eval_collectBalanced, rawRowCheck19120]

theorem rawRowCheck19121 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form2 = rawRow19121 := by decide +kernel

theorem rowCheck19121 : row19121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19121 := by decide +kernel

theorem rowEval19121 (x : Key → ℝ) : Integer.Sparse.eval row19121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19121, Integer.Sparse.eval_collectBalanced, rawRowCheck19121]

theorem rawRowCheck19122 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form2 = rawRow19122 := by decide +kernel

theorem rowCheck19122 : row19122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19122 := by decide +kernel

theorem rowEval19122 (x : Key → ℝ) : Integer.Sparse.eval row19122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19122, Integer.Sparse.eval_collectBalanced, rawRowCheck19122]

theorem rawRowCheck19123 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19123 := by decide +kernel

theorem rowCheck19123 : row19123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19123 := by decide +kernel

theorem rowEval19123 (x : Key → ℝ) : Integer.Sparse.eval row19123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19123, Integer.Sparse.eval_collectBalanced, rawRowCheck19123]

theorem rawRowCheck19124 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19124 := by decide +kernel

theorem rowCheck19124 : row19124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19124 := by decide +kernel

theorem rowEval19124 (x : Key → ℝ) : Integer.Sparse.eval row19124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19124, Integer.Sparse.eval_collectBalanced, rawRowCheck19124]

theorem rawRowCheck19125 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19125 := by decide +kernel

theorem rowCheck19125 : row19125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19125 := by decide +kernel

theorem rowEval19125 (x : Key → ℝ) : Integer.Sparse.eval row19125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19125, Integer.Sparse.eval_collectBalanced, rawRowCheck19125]

theorem rawRowCheck19126 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19126 := by decide +kernel

theorem rowCheck19126 : row19126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19126 := by decide +kernel

theorem rowEval19126 (x : Key → ℝ) : Integer.Sparse.eval row19126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19126, Integer.Sparse.eval_collectBalanced, rawRowCheck19126]

theorem rawRowCheck19127 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form2 = rawRow19127 := by decide +kernel

theorem rowCheck19127 : row19127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19127 := by decide +kernel

theorem rowEval19127 (x : Key → ℝ) : Integer.Sparse.eval row19127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19127, Integer.Sparse.eval_collectBalanced, rawRowCheck19127]

theorem rawRowCheck19128 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form2 = rawRow19128 := by decide +kernel

theorem rowCheck19128 : row19128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19128 := by decide +kernel

theorem rowEval19128 (x : Key → ℝ) : Integer.Sparse.eval row19128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19128, Integer.Sparse.eval_collectBalanced, rawRowCheck19128]

theorem rawRowCheck19129 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form2 = rawRow19129 := by decide +kernel

theorem rowCheck19129 : row19129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19129 := by decide +kernel

theorem rowEval19129 (x : Key → ℝ) : Integer.Sparse.eval row19129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19129, Integer.Sparse.eval_collectBalanced, rawRowCheck19129]

theorem rawRowCheck19130 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19130 := by decide +kernel

theorem rowCheck19130 : row19130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19130 := by decide +kernel

theorem rowEval19130 (x : Key → ℝ) : Integer.Sparse.eval row19130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19130, Integer.Sparse.eval_collectBalanced, rawRowCheck19130]

theorem rawRowCheck19131 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19131 := by decide +kernel

theorem rowCheck19131 : row19131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19131 := by decide +kernel

theorem rowEval19131 (x : Key → ℝ) : Integer.Sparse.eval row19131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19131, Integer.Sparse.eval_collectBalanced, rawRowCheck19131]

theorem rawRowCheck19132 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19132 := by decide +kernel

theorem rowCheck19132 : row19132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19132 := by decide +kernel

theorem rowEval19132 (x : Key → ℝ) : Integer.Sparse.eval row19132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19132, Integer.Sparse.eval_collectBalanced, rawRowCheck19132]

theorem rawRowCheck19133 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form2 = rawRow19133 := by decide +kernel

theorem rowCheck19133 : row19133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19133 := by decide +kernel

theorem rowEval19133 (x : Key → ℝ) : Integer.Sparse.eval row19133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19133, Integer.Sparse.eval_collectBalanced, rawRowCheck19133]

theorem rawRowCheck19134 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form2 = rawRow19134 := by decide +kernel

theorem rowCheck19134 : row19134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19134 := by decide +kernel

theorem rowEval19134 (x : Key → ℝ) : Integer.Sparse.eval row19134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19134, Integer.Sparse.eval_collectBalanced, rawRowCheck19134]

theorem rawRowCheck19135 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form2 = rawRow19135 := by decide +kernel

theorem rowCheck19135 : row19135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19135 := by decide +kernel

theorem rowEval19135 (x : Key → ℝ) : Integer.Sparse.eval row19135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19135, Integer.Sparse.eval_collectBalanced, rawRowCheck19135]

theorem rawRowCheck19136 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form2 = rawRow19136 := by decide +kernel

theorem rowCheck19136 : row19136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19136 := by decide +kernel

theorem rowEval19136 (x : Key → ℝ) : Integer.Sparse.eval row19136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19136, Integer.Sparse.eval_collectBalanced, rawRowCheck19136]

theorem rawRowCheck19137 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form2 = rawRow19137 := by decide +kernel

theorem rowCheck19137 : row19137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19137 := by decide +kernel

theorem rowEval19137 (x : Key → ℝ) : Integer.Sparse.eval row19137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19137, Integer.Sparse.eval_collectBalanced, rawRowCheck19137]

theorem rawRowCheck19138 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form2 = rawRow19138 := by decide +kernel

theorem rowCheck19138 : row19138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19138 := by decide +kernel

theorem rowEval19138 (x : Key → ℝ) : Integer.Sparse.eval row19138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19138, Integer.Sparse.eval_collectBalanced, rawRowCheck19138]

theorem rawRowCheck19139 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19139 := by decide +kernel

theorem rowCheck19139 : row19139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19139 := by decide +kernel

theorem rowEval19139 (x : Key → ℝ) : Integer.Sparse.eval row19139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19139, Integer.Sparse.eval_collectBalanced, rawRowCheck19139]

theorem rawRowCheck19140 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19140 := by decide +kernel

theorem rowCheck19140 : row19140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19140 := by decide +kernel

theorem rowEval19140 (x : Key → ℝ) : Integer.Sparse.eval row19140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19140, Integer.Sparse.eval_collectBalanced, rawRowCheck19140]

theorem rawRowCheck19141 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19141 := by decide +kernel

theorem rowCheck19141 : row19141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19141 := by decide +kernel

theorem rowEval19141 (x : Key → ℝ) : Integer.Sparse.eval row19141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19141, Integer.Sparse.eval_collectBalanced, rawRowCheck19141]

theorem rawRowCheck19142 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19142 := by decide +kernel

theorem rowCheck19142 : row19142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19142 := by decide +kernel

theorem rowEval19142 (x : Key → ℝ) : Integer.Sparse.eval row19142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19142, Integer.Sparse.eval_collectBalanced, rawRowCheck19142]

theorem rawRowCheck19143 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19143 := by decide +kernel

theorem rowCheck19143 : row19143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19143 := by decide +kernel

theorem rowEval19143 (x : Key → ℝ) : Integer.Sparse.eval row19143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19143, Integer.Sparse.eval_collectBalanced, rawRowCheck19143]

theorem rawRowCheck19144 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19144 := by decide +kernel

theorem rowCheck19144 : row19144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19144 := by decide +kernel

theorem rowEval19144 (x : Key → ℝ) : Integer.Sparse.eval row19144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19144, Integer.Sparse.eval_collectBalanced, rawRowCheck19144]

theorem rawRowCheck19145 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19145 := by decide +kernel

theorem rowCheck19145 : row19145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19145 := by decide +kernel

theorem rowEval19145 (x : Key → ℝ) : Integer.Sparse.eval row19145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19145, Integer.Sparse.eval_collectBalanced, rawRowCheck19145]

theorem rawRowCheck19146 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19146 := by decide +kernel

theorem rowCheck19146 : row19146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19146 := by decide +kernel

theorem rowEval19146 (x : Key → ℝ) : Integer.Sparse.eval row19146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19146, Integer.Sparse.eval_collectBalanced, rawRowCheck19146]

theorem rawRowCheck19147 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19147 := by decide +kernel

theorem rowCheck19147 : row19147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19147 := by decide +kernel

theorem rowEval19147 (x : Key → ℝ) : Integer.Sparse.eval row19147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19147, Integer.Sparse.eval_collectBalanced, rawRowCheck19147]

theorem rawRowCheck19148 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19148 := by decide +kernel

theorem rowCheck19148 : row19148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19148 := by decide +kernel

theorem rowEval19148 (x : Key → ℝ) : Integer.Sparse.eval row19148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19148, Integer.Sparse.eval_collectBalanced, rawRowCheck19148]

theorem rawRowCheck19149 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19149 := by decide +kernel

theorem rowCheck19149 : row19149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19149 := by decide +kernel

theorem rowEval19149 (x : Key → ℝ) : Integer.Sparse.eval row19149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19149, Integer.Sparse.eval_collectBalanced, rawRowCheck19149]

theorem rawRowCheck19150 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19150 := by decide +kernel

theorem rowCheck19150 : row19150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19150 := by decide +kernel

theorem rowEval19150 (x : Key → ℝ) : Integer.Sparse.eval row19150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19150, Integer.Sparse.eval_collectBalanced, rawRowCheck19150]

theorem rawRowCheck19151 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19151 := by decide +kernel

theorem rowCheck19151 : row19151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19151 := by decide +kernel

theorem rowEval19151 (x : Key → ℝ) : Integer.Sparse.eval row19151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19151, Integer.Sparse.eval_collectBalanced, rawRowCheck19151]

theorem rawRowCheck19152 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19152 := by decide +kernel

theorem rowCheck19152 : row19152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19152 := by decide +kernel

theorem rowEval19152 (x : Key → ℝ) : Integer.Sparse.eval row19152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19152, Integer.Sparse.eval_collectBalanced, rawRowCheck19152]

theorem rawRowCheck19153 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form3 = rawRow19153 := by decide +kernel

theorem rowCheck19153 : row19153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19153 := by decide +kernel

theorem rowEval19153 (x : Key → ℝ) : Integer.Sparse.eval row19153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19153, Integer.Sparse.eval_collectBalanced, rawRowCheck19153]

theorem rawRowCheck19154 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form3 = rawRow19154 := by decide +kernel

theorem rowCheck19154 : row19154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19154 := by decide +kernel

theorem rowEval19154 (x : Key → ℝ) : Integer.Sparse.eval row19154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19154, Integer.Sparse.eval_collectBalanced, rawRowCheck19154]

theorem rawRowCheck19155 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form3 = rawRow19155 := by decide +kernel

theorem rowCheck19155 : row19155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19155 := by decide +kernel

theorem rowEval19155 (x : Key → ℝ) : Integer.Sparse.eval row19155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19155, Integer.Sparse.eval_collectBalanced, rawRowCheck19155]

theorem rawRowCheck19156 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form3 = rawRow19156 := by decide +kernel

theorem rowCheck19156 : row19156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19156 := by decide +kernel

theorem rowEval19156 (x : Key → ℝ) : Integer.Sparse.eval row19156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19156, Integer.Sparse.eval_collectBalanced, rawRowCheck19156]

theorem rawRowCheck19157 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form3 = rawRow19157 := by decide +kernel

theorem rowCheck19157 : row19157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19157 := by decide +kernel

theorem rowEval19157 (x : Key → ℝ) : Integer.Sparse.eval row19157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19157, Integer.Sparse.eval_collectBalanced, rawRowCheck19157]

theorem rawRowCheck19158 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form3 = rawRow19158 := by decide +kernel

theorem rowCheck19158 : row19158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19158 := by decide +kernel

theorem rowEval19158 (x : Key → ℝ) : Integer.Sparse.eval row19158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19158, Integer.Sparse.eval_collectBalanced, rawRowCheck19158]

theorem rawRowCheck19159 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19159 := by decide +kernel

theorem rowCheck19159 : row19159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19159 := by decide +kernel

theorem rowEval19159 (x : Key → ℝ) : Integer.Sparse.eval row19159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19159, Integer.Sparse.eval_collectBalanced, rawRowCheck19159]

theorem rawRowCheck19160 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19160 := by decide +kernel

theorem rowCheck19160 : row19160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19160 := by decide +kernel

theorem rowEval19160 (x : Key → ℝ) : Integer.Sparse.eval row19160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19160, Integer.Sparse.eval_collectBalanced, rawRowCheck19160]

theorem rawRowCheck19161 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19161 := by decide +kernel

theorem rowCheck19161 : row19161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19161 := by decide +kernel

theorem rowEval19161 (x : Key → ℝ) : Integer.Sparse.eval row19161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19161, Integer.Sparse.eval_collectBalanced, rawRowCheck19161]

theorem rawRowCheck19162 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19162 := by decide +kernel

theorem rowCheck19162 : row19162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19162 := by decide +kernel

theorem rowEval19162 (x : Key → ℝ) : Integer.Sparse.eval row19162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19162, Integer.Sparse.eval_collectBalanced, rawRowCheck19162]

theorem rawRowCheck19163 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19163 := by decide +kernel

theorem rowCheck19163 : row19163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19163 := by decide +kernel

theorem rowEval19163 (x : Key → ℝ) : Integer.Sparse.eval row19163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19163, Integer.Sparse.eval_collectBalanced, rawRowCheck19163]

theorem rawRowCheck19164 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19164 := by decide +kernel

theorem rowCheck19164 : row19164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19164 := by decide +kernel

theorem rowEval19164 (x : Key → ℝ) : Integer.Sparse.eval row19164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19164, Integer.Sparse.eval_collectBalanced, rawRowCheck19164]

theorem rawRowCheck19165 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19165 := by decide +kernel

theorem rowCheck19165 : row19165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19165 := by decide +kernel

theorem rowEval19165 (x : Key → ℝ) : Integer.Sparse.eval row19165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19165, Integer.Sparse.eval_collectBalanced, rawRowCheck19165]

theorem rawRowCheck19166 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19166 := by decide +kernel

theorem rowCheck19166 : row19166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19166 := by decide +kernel

theorem rowEval19166 (x : Key → ℝ) : Integer.Sparse.eval row19166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19166, Integer.Sparse.eval_collectBalanced, rawRowCheck19166]

theorem rawRowCheck19167 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19167 := by decide +kernel

theorem rowCheck19167 : row19167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19167 := by decide +kernel

theorem rowEval19167 (x : Key → ℝ) : Integer.Sparse.eval row19167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19167, Integer.Sparse.eval_collectBalanced, rawRowCheck19167]

theorem rawRowCheck19168 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19168 := by decide +kernel

theorem rowCheck19168 : row19168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19168 := by decide +kernel

theorem rowEval19168 (x : Key → ℝ) : Integer.Sparse.eval row19168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19168, Integer.Sparse.eval_collectBalanced, rawRowCheck19168]

theorem rawRowCheck19169 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19169 := by decide +kernel

theorem rowCheck19169 : row19169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19169 := by decide +kernel

theorem rowEval19169 (x : Key → ℝ) : Integer.Sparse.eval row19169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19169, Integer.Sparse.eval_collectBalanced, rawRowCheck19169]

theorem rawRowCheck19170 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19170 := by decide +kernel

theorem rowCheck19170 : row19170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19170 := by decide +kernel

theorem rowEval19170 (x : Key → ℝ) : Integer.Sparse.eval row19170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19170, Integer.Sparse.eval_collectBalanced, rawRowCheck19170]

theorem rawRowCheck19171 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19171 := by decide +kernel

theorem rowCheck19171 : row19171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19171 := by decide +kernel

theorem rowEval19171 (x : Key → ℝ) : Integer.Sparse.eval row19171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19171, Integer.Sparse.eval_collectBalanced, rawRowCheck19171]

theorem rawRowCheck19172 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19172 := by decide +kernel

theorem rowCheck19172 : row19172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19172 := by decide +kernel

theorem rowEval19172 (x : Key → ℝ) : Integer.Sparse.eval row19172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19172, Integer.Sparse.eval_collectBalanced, rawRowCheck19172]

theorem rawRowCheck19173 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form4 = rawRow19173 := by decide +kernel

theorem rowCheck19173 : row19173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19173 := by decide +kernel

theorem rowEval19173 (x : Key → ℝ) : Integer.Sparse.eval row19173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19173, Integer.Sparse.eval_collectBalanced, rawRowCheck19173]

theorem rawRowCheck19174 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form4 = rawRow19174 := by decide +kernel

theorem rowCheck19174 : row19174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19174 := by decide +kernel

theorem rowEval19174 (x : Key → ℝ) : Integer.Sparse.eval row19174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19174, Integer.Sparse.eval_collectBalanced, rawRowCheck19174]

theorem rawRowCheck19175 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form4 = rawRow19175 := by decide +kernel

theorem rowCheck19175 : row19175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19175 := by decide +kernel

theorem rowEval19175 (x : Key → ℝ) : Integer.Sparse.eval row19175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19175, Integer.Sparse.eval_collectBalanced, rawRowCheck19175]

theorem rawRowCheck19176 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form4 = rawRow19176 := by decide +kernel

theorem rowCheck19176 : row19176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19176 := by decide +kernel

theorem rowEval19176 (x : Key → ℝ) : Integer.Sparse.eval row19176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19176, Integer.Sparse.eval_collectBalanced, rawRowCheck19176]

theorem rawRowCheck19177 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form4 = rawRow19177 := by decide +kernel

theorem rowCheck19177 : row19177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19177 := by decide +kernel

theorem rowEval19177 (x : Key → ℝ) : Integer.Sparse.eval row19177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19177, Integer.Sparse.eval_collectBalanced, rawRowCheck19177]

theorem rawRowCheck19178 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form4 = rawRow19178 := by decide +kernel

theorem rowCheck19178 : row19178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19178 := by decide +kernel

theorem rowEval19178 (x : Key → ℝ) : Integer.Sparse.eval row19178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19178, Integer.Sparse.eval_collectBalanced, rawRowCheck19178]

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

theorem rawRowCheck19199 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19199 := by decide +kernel

theorem rowCheck19199 : row19199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19199 := by decide +kernel

theorem rowEval19199 (x : Key → ℝ) : Integer.Sparse.eval row19199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19199, Integer.Sparse.eval_collectBalanced, rawRowCheck19199]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck19200 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19200 := by decide +kernel

theorem rowCheck19200 : row19200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19200 := by decide +kernel

theorem rowEval19200 (x : Key → ℝ) : Integer.Sparse.eval row19200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19200, Integer.Sparse.eval_collectBalanced, rawRowCheck19200]

theorem rawRowCheck19201 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19201 := by decide +kernel

theorem rowCheck19201 : row19201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19201 := by decide +kernel

theorem rowEval19201 (x : Key → ℝ) : Integer.Sparse.eval row19201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19201, Integer.Sparse.eval_collectBalanced, rawRowCheck19201]

theorem rawRowCheck19202 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19202 := by decide +kernel

theorem rowCheck19202 : row19202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19202 := by decide +kernel

theorem rowEval19202 (x : Key → ℝ) : Integer.Sparse.eval row19202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19202, Integer.Sparse.eval_collectBalanced, rawRowCheck19202]

theorem rawRowCheck19203 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19203 := by decide +kernel

theorem rowCheck19203 : row19203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19203 := by decide +kernel

theorem rowEval19203 (x : Key → ℝ) : Integer.Sparse.eval row19203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19203, Integer.Sparse.eval_collectBalanced, rawRowCheck19203]

theorem rawRowCheck19204 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19204 := by decide +kernel

theorem rowCheck19204 : row19204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19204 := by decide +kernel

theorem rowEval19204 (x : Key → ℝ) : Integer.Sparse.eval row19204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19204, Integer.Sparse.eval_collectBalanced, rawRowCheck19204]

theorem rawRowCheck19205 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19205 := by decide +kernel

theorem rowCheck19205 : row19205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19205 := by decide +kernel

theorem rowEval19205 (x : Key → ℝ) : Integer.Sparse.eval row19205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19205, Integer.Sparse.eval_collectBalanced, rawRowCheck19205]

theorem rawRowCheck19206 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19206 := by decide +kernel

theorem rowCheck19206 : row19206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19206 := by decide +kernel

theorem rowEval19206 (x : Key → ℝ) : Integer.Sparse.eval row19206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19206, Integer.Sparse.eval_collectBalanced, rawRowCheck19206]

theorem rawRowCheck19207 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19207 := by decide +kernel

theorem rowCheck19207 : row19207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19207 := by decide +kernel

theorem rowEval19207 (x : Key → ℝ) : Integer.Sparse.eval row19207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19207, Integer.Sparse.eval_collectBalanced, rawRowCheck19207]

theorem rawRowCheck19208 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19208 := by decide +kernel

theorem rowCheck19208 : row19208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19208 := by decide +kernel

theorem rowEval19208 (x : Key → ℝ) : Integer.Sparse.eval row19208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19208, Integer.Sparse.eval_collectBalanced, rawRowCheck19208]

theorem rawRowCheck19209 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19209 := by decide +kernel

theorem rowCheck19209 : row19209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19209 := by decide +kernel

theorem rowEval19209 (x : Key → ℝ) : Integer.Sparse.eval row19209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19209, Integer.Sparse.eval_collectBalanced, rawRowCheck19209]

theorem rawRowCheck19210 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19210 := by decide +kernel

theorem rowCheck19210 : row19210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19210 := by decide +kernel

theorem rowEval19210 (x : Key → ℝ) : Integer.Sparse.eval row19210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19210, Integer.Sparse.eval_collectBalanced, rawRowCheck19210]

theorem rawRowCheck19211 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19211 := by decide +kernel

theorem rowCheck19211 : row19211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19211 := by decide +kernel

theorem rowEval19211 (x : Key → ℝ) : Integer.Sparse.eval row19211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19211, Integer.Sparse.eval_collectBalanced, rawRowCheck19211]

theorem rawRowCheck19212 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19212 := by decide +kernel

theorem rowCheck19212 : row19212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19212 := by decide +kernel

theorem rowEval19212 (x : Key → ℝ) : Integer.Sparse.eval row19212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19212, Integer.Sparse.eval_collectBalanced, rawRowCheck19212]

theorem rawRowCheck19213 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form6 = rawRow19213 := by decide +kernel

theorem rowCheck19213 : row19213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19213 := by decide +kernel

theorem rowEval19213 (x : Key → ℝ) : Integer.Sparse.eval row19213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19213, Integer.Sparse.eval_collectBalanced, rawRowCheck19213]

theorem rawRowCheck19214 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form6 = rawRow19214 := by decide +kernel

theorem rowCheck19214 : row19214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19214 := by decide +kernel

theorem rowEval19214 (x : Key → ℝ) : Integer.Sparse.eval row19214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19214, Integer.Sparse.eval_collectBalanced, rawRowCheck19214]

theorem rawRowCheck19215 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form6 = rawRow19215 := by decide +kernel

theorem rowCheck19215 : row19215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19215 := by decide +kernel

theorem rowEval19215 (x : Key → ℝ) : Integer.Sparse.eval row19215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19215, Integer.Sparse.eval_collectBalanced, rawRowCheck19215]

theorem rawRowCheck19216 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form6 = rawRow19216 := by decide +kernel

theorem rowCheck19216 : row19216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19216 := by decide +kernel

theorem rowEval19216 (x : Key → ℝ) : Integer.Sparse.eval row19216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19216, Integer.Sparse.eval_collectBalanced, rawRowCheck19216]

theorem rawRowCheck19217 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form6 = rawRow19217 := by decide +kernel

theorem rowCheck19217 : row19217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19217 := by decide +kernel

theorem rowEval19217 (x : Key → ℝ) : Integer.Sparse.eval row19217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19217, Integer.Sparse.eval_collectBalanced, rawRowCheck19217]

theorem rawRowCheck19218 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form6 = rawRow19218 := by decide +kernel

theorem rowCheck19218 : row19218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19218 := by decide +kernel

theorem rowEval19218 (x : Key → ℝ) : Integer.Sparse.eval row19218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19218, Integer.Sparse.eval_collectBalanced, rawRowCheck19218]

theorem rawRowCheck19219 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19219 := by decide +kernel

theorem rowCheck19219 : row19219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19219 := by decide +kernel

theorem rowEval19219 (x : Key → ℝ) : Integer.Sparse.eval row19219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19219, Integer.Sparse.eval_collectBalanced, rawRowCheck19219]

theorem rawRowCheck19220 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form7 = rawRow19220 := by decide +kernel

theorem rowCheck19220 : row19220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19220 := by decide +kernel

theorem rowEval19220 (x : Key → ℝ) : Integer.Sparse.eval row19220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19220, Integer.Sparse.eval_collectBalanced, rawRowCheck19220]

theorem rawRowCheck19221 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form7 = rawRow19221 := by decide +kernel

theorem rowCheck19221 : row19221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19221 := by decide +kernel

theorem rowEval19221 (x : Key → ℝ) : Integer.Sparse.eval row19221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19221, Integer.Sparse.eval_collectBalanced, rawRowCheck19221]

theorem rawRowCheck19222 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form7 = rawRow19222 := by decide +kernel

theorem rowCheck19222 : row19222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19222 := by decide +kernel

theorem rowEval19222 (x : Key → ℝ) : Integer.Sparse.eval row19222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19222, Integer.Sparse.eval_collectBalanced, rawRowCheck19222]

theorem rawRowCheck19223 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19223 := by decide +kernel

theorem rowCheck19223 : row19223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19223 := by decide +kernel

theorem rowEval19223 (x : Key → ℝ) : Integer.Sparse.eval row19223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19223, Integer.Sparse.eval_collectBalanced, rawRowCheck19223]

theorem rawRowCheck19224 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form7 = rawRow19224 := by decide +kernel

theorem rowCheck19224 : row19224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19224 := by decide +kernel

theorem rowEval19224 (x : Key → ℝ) : Integer.Sparse.eval row19224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19224, Integer.Sparse.eval_collectBalanced, rawRowCheck19224]

theorem rawRowCheck19225 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form7 = rawRow19225 := by decide +kernel

theorem rowCheck19225 : row19225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19225 := by decide +kernel

theorem rowEval19225 (x : Key → ℝ) : Integer.Sparse.eval row19225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19225, Integer.Sparse.eval_collectBalanced, rawRowCheck19225]

theorem rawRowCheck19226 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form7 = rawRow19226 := by decide +kernel

theorem rowCheck19226 : row19226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19226 := by decide +kernel

theorem rowEval19226 (x : Key → ℝ) : Integer.Sparse.eval row19226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19226, Integer.Sparse.eval_collectBalanced, rawRowCheck19226]

theorem rawRowCheck19227 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form7 = rawRow19227 := by decide +kernel

theorem rowCheck19227 : row19227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19227 := by decide +kernel

theorem rowEval19227 (x : Key → ℝ) : Integer.Sparse.eval row19227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19227, Integer.Sparse.eval_collectBalanced, rawRowCheck19227]

theorem rawRowCheck19228 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form7 = rawRow19228 := by decide +kernel

theorem rowCheck19228 : row19228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19228 := by decide +kernel

theorem rowEval19228 (x : Key → ℝ) : Integer.Sparse.eval row19228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19228, Integer.Sparse.eval_collectBalanced, rawRowCheck19228]

theorem rawRowCheck19229 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form7 = rawRow19229 := by decide +kernel

theorem rowCheck19229 : row19229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19229 := by decide +kernel

theorem rowEval19229 (x : Key → ℝ) : Integer.Sparse.eval row19229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19229, Integer.Sparse.eval_collectBalanced, rawRowCheck19229]

theorem rawRowCheck19230 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form7 = rawRow19230 := by decide +kernel

theorem rowCheck19230 : row19230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19230 := by decide +kernel

theorem rowEval19230 (x : Key → ℝ) : Integer.Sparse.eval row19230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19230, Integer.Sparse.eval_collectBalanced, rawRowCheck19230]

theorem rawRowCheck19231 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form7 = rawRow19231 := by decide +kernel

theorem rowCheck19231 : row19231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19231 := by decide +kernel

theorem rowEval19231 (x : Key → ℝ) : Integer.Sparse.eval row19231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19231, Integer.Sparse.eval_collectBalanced, rawRowCheck19231]

theorem rawRowCheck19232 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form7 = rawRow19232 := by decide +kernel

theorem rowCheck19232 : row19232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19232 := by decide +kernel

theorem rowEval19232 (x : Key → ℝ) : Integer.Sparse.eval row19232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19232, Integer.Sparse.eval_collectBalanced, rawRowCheck19232]

theorem rawRowCheck19233 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form7 = rawRow19233 := by decide +kernel

theorem rowCheck19233 : row19233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19233 := by decide +kernel

theorem rowEval19233 (x : Key → ℝ) : Integer.Sparse.eval row19233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19233, Integer.Sparse.eval_collectBalanced, rawRowCheck19233]

theorem rawRowCheck19234 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form7 = rawRow19234 := by decide +kernel

theorem rowCheck19234 : row19234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19234 := by decide +kernel

theorem rowEval19234 (x : Key → ℝ) : Integer.Sparse.eval row19234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19234, Integer.Sparse.eval_collectBalanced, rawRowCheck19234]

theorem rawRowCheck19235 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form7 = rawRow19235 := by decide +kernel

theorem rowCheck19235 : row19235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19235 := by decide +kernel

theorem rowEval19235 (x : Key → ℝ) : Integer.Sparse.eval row19235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19235, Integer.Sparse.eval_collectBalanced, rawRowCheck19235]

theorem rawRowCheck19236 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form7 = rawRow19236 := by decide +kernel

theorem rowCheck19236 : row19236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19236 := by decide +kernel

theorem rowEval19236 (x : Key → ℝ) : Integer.Sparse.eval row19236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19236, Integer.Sparse.eval_collectBalanced, rawRowCheck19236]

theorem rawRowCheck19237 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form7 = rawRow19237 := by decide +kernel

theorem rowCheck19237 : row19237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19237 := by decide +kernel

theorem rowEval19237 (x : Key → ℝ) : Integer.Sparse.eval row19237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19237, Integer.Sparse.eval_collectBalanced, rawRowCheck19237]

theorem rawRowCheck19238 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form7 = rawRow19238 := by decide +kernel

theorem rowCheck19238 : row19238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19238 := by decide +kernel

theorem rowEval19238 (x : Key → ℝ) : Integer.Sparse.eval row19238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19238, Integer.Sparse.eval_collectBalanced, rawRowCheck19238]

theorem rawRowCheck19274 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form7 = rawRow19274 := by decide +kernel

theorem rowCheck19274 : row19274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19274 := by decide +kernel

theorem rowEval19274 (x : Key → ℝ) : Integer.Sparse.eval row19274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19274, Integer.Sparse.eval_collectBalanced, rawRowCheck19274]

theorem rawRowCheck19275 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form7 = rawRow19275 := by decide +kernel

theorem rowCheck19275 : row19275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19275 := by decide +kernel

theorem rowEval19275 (x : Key → ℝ) : Integer.Sparse.eval row19275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19275, Integer.Sparse.eval_collectBalanced, rawRowCheck19275]

theorem rawRowCheck19276 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form7 = rawRow19276 := by decide +kernel

theorem rowCheck19276 : row19276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19276 := by decide +kernel

theorem rowEval19276 (x : Key → ℝ) : Integer.Sparse.eval row19276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19276, Integer.Sparse.eval_collectBalanced, rawRowCheck19276]

theorem rawRowCheck19277 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19277 := by decide +kernel

theorem rowCheck19277 : row19277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19277 := by decide +kernel

theorem rowEval19277 (x : Key → ℝ) : Integer.Sparse.eval row19277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19277, Integer.Sparse.eval_collectBalanced, rawRowCheck19277]

theorem rawRowCheck19278 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19278 := by decide +kernel

theorem rowCheck19278 : row19278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19278 := by decide +kernel

theorem rowEval19278 (x : Key → ℝ) : Integer.Sparse.eval row19278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19278, Integer.Sparse.eval_collectBalanced, rawRowCheck19278]

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

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19079 x
  · exact rowEval19080 x
  · exact rowEval19081 x
  · exact rowEval19082 x
  · exact rowEval19083 x
  · exact rowEval19084 x
  · exact rowEval19085 x
  · exact rowEval19086 x
  · exact rowEval19087 x
  · exact rowEval19088 x
  · exact rowEval19089 x
  · exact rowEval19090 x
  · exact rowEval19091 x
  · exact rowEval19092 x
  · exact rowEval19093 x
  · exact rowEval19094 x
  · exact rowEval19095 x
  · exact rowEval19096 x
  · exact rowEval19097 x
  · exact rowEval19098 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

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

theorem entryCheck7_2 : entry7_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_2 k)) := by decide +kernel

theorem rowsSound7_2 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval19119 x
  · exact rowEval19120 x
  · exact rowEval19121 x
  · exact rowEval19122 x
  · exact rowEval19123 x
  · exact rowEval19124 x
  · exact rowEval19125 x
  · exact rowEval19126 x
  · exact rowEval19127 x
  · exact rowEval19128 x
  · exact rowEval19129 x
  · exact rowEval19130 x
  · exact rowEval19131 x
  · exact rowEval19132 x
  · exact rowEval19133 x
  · exact rowEval19134 x
  · exact rowEval19135 x
  · exact rowEval19136 x
  · exact rowEval19137 x
  · exact rowEval19138 x

theorem entryEval7_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_2 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck7_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_2]

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19139 x
  · exact rowEval19140 x
  · exact rowEval19141 x
  · exact rowEval19142 x
  · exact rowEval19143 x
  · exact rowEval19144 x
  · exact rowEval19145 x
  · exact rowEval19146 x
  · exact rowEval19147 x
  · exact rowEval19148 x
  · exact rowEval19149 x
  · exact rowEval19150 x
  · exact rowEval19151 x
  · exact rowEval19152 x
  · exact rowEval19153 x
  · exact rowEval19154 x
  · exact rowEval19155 x
  · exact rowEval19156 x
  · exact rowEval19157 x
  · exact rowEval19158 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19159 x
  · exact rowEval19160 x
  · exact rowEval19161 x
  · exact rowEval19162 x
  · exact rowEval19163 x
  · exact rowEval19164 x
  · exact rowEval19165 x
  · exact rowEval19166 x
  · exact rowEval19167 x
  · exact rowEval19168 x
  · exact rowEval19169 x
  · exact rowEval19170 x
  · exact rowEval19171 x
  · exact rowEval19172 x
  · exact rowEval19173 x
  · exact rowEval19174 x
  · exact rowEval19175 x
  · exact rowEval19176 x
  · exact rowEval19177 x
  · exact rowEval19178 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

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

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19199 x
  · exact rowEval19200 x
  · exact rowEval19201 x
  · exact rowEval19202 x
  · exact rowEval19203 x
  · exact rowEval19204 x
  · exact rowEval19205 x
  · exact rowEval19206 x
  · exact rowEval19207 x
  · exact rowEval19208 x
  · exact rowEval19209 x
  · exact rowEval19210 x
  · exact rowEval19211 x
  · exact rowEval19212 x
  · exact rowEval19213 x
  · exact rowEval19214 x
  · exact rowEval19215 x
  · exact rowEval19216 x
  · exact rowEval19217 x
  · exact rowEval19218 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval19219 x
  · exact rowEval19220 x
  · exact rowEval19221 x
  · exact rowEval19222 x
  · exact rowEval19223 x
  · exact rowEval19224 x
  · exact rowEval19225 x
  · exact rowEval19226 x
  · exact rowEval19227 x
  · exact rowEval19228 x
  · exact rowEval19229 x
  · exact rowEval19230 x
  · exact rowEval19231 x
  · exact rowEval19232 x
  · exact rowEval19233 x
  · exact rowEval19234 x
  · exact rowEval19235 x
  · exact rowEval19236 x
  · exact rowEval19237 x
  · exact rowEval19238 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

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

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval19274 x
  · exact rowEval19275 x
  · exact rowEval19276 x
  · exact rowEval19277 x
  · exact rowEval19278 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

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

theorem entryCheck9_7 : entry9_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_7 k)) := by decide +kernel

theorem rowsSound9_7 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval19354 x
  · exact rowEval19355 x
  · exact rowEval19356 x
  · exact rowEval19357 x
  · exact rowEval19358 x
  · exact rowEval19359 x
  · exact rowEval19360 x
  · exact rowEval19361 x
  · exact rowEval19362 x
  · exact rowEval19363 x

theorem entryEval9_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_7 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck9_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_7]

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

theorem entryEvalRow7_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 7 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 7).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval7_0 B hB
  · exact entryEval7_1 B hB
  · exact entryEval7_2 B hB
  · exact entryEval7_3 B hB
  · exact entryEval7_4 B hB
  · exact entryEval7_5 B hB
  · exact entryEval7_6 B hB
  · exact entryEval7_7 B hB
  · exact (entryEval8_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e_oai
