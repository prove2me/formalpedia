-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:45:33.556905+00:00
-- url     : https://prove2.me/submissions/bce07194-4163-43e1-b964-7044f2395999

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17411 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form0 = rawRow17411 := by decide +kernel

theorem rowCheck17411 : row17411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17411 := by decide +kernel

theorem rowEval17411 (x : Key → ℝ) : Integer.Sparse.eval row17411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17411, Integer.Sparse.eval_collectBalanced, rawRowCheck17411]

theorem rawRowCheck17412 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form0 = rawRow17412 := by decide +kernel

theorem rowCheck17412 : row17412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17412 := by decide +kernel

theorem rowEval17412 (x : Key → ℝ) : Integer.Sparse.eval row17412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17412, Integer.Sparse.eval_collectBalanced, rawRowCheck17412]

theorem rawRowCheck17413 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form0 = rawRow17413 := by decide +kernel

theorem rowCheck17413 : row17413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17413 := by decide +kernel

theorem rowEval17413 (x : Key → ℝ) : Integer.Sparse.eval row17413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17413, Integer.Sparse.eval_collectBalanced, rawRowCheck17413]

theorem rawRowCheck17414 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form0 = rawRow17414 := by decide +kernel

theorem rowCheck17414 : row17414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17414 := by decide +kernel

theorem rowEval17414 (x : Key → ℝ) : Integer.Sparse.eval row17414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17414, Integer.Sparse.eval_collectBalanced, rawRowCheck17414]

theorem rawRowCheck17415 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form0 = rawRow17415 := by decide +kernel

theorem rowCheck17415 : row17415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17415 := by decide +kernel

theorem rowEval17415 (x : Key → ℝ) : Integer.Sparse.eval row17415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17415, Integer.Sparse.eval_collectBalanced, rawRowCheck17415]

theorem rawRowCheck17416 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form0 = rawRow17416 := by decide +kernel

theorem rowCheck17416 : row17416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17416 := by decide +kernel

theorem rowEval17416 (x : Key → ℝ) : Integer.Sparse.eval row17416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17416, Integer.Sparse.eval_collectBalanced, rawRowCheck17416]

theorem rawRowCheck17417 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form0 = rawRow17417 := by decide +kernel

theorem rowCheck17417 : row17417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17417 := by decide +kernel

theorem rowEval17417 (x : Key → ℝ) : Integer.Sparse.eval row17417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17417, Integer.Sparse.eval_collectBalanced, rawRowCheck17417]

theorem rawRowCheck17418 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form0 = rawRow17418 := by decide +kernel

theorem rowCheck17418 : row17418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17418 := by decide +kernel

theorem rowEval17418 (x : Key → ℝ) : Integer.Sparse.eval row17418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17418, Integer.Sparse.eval_collectBalanced, rawRowCheck17418]

theorem rawRowCheck17419 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form0 = rawRow17419 := by decide +kernel

theorem rowCheck17419 : row17419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17419 := by decide +kernel

theorem rowEval17419 (x : Key → ℝ) : Integer.Sparse.eval row17419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17419, Integer.Sparse.eval_collectBalanced, rawRowCheck17419]

theorem rawRowCheck17420 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow17420 := by decide +kernel

theorem rowCheck17420 : row17420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17420 := by decide +kernel

theorem rowEval17420 (x : Key → ℝ) : Integer.Sparse.eval row17420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17420, Integer.Sparse.eval_collectBalanced, rawRowCheck17420]

theorem rawRowCheck17421 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form1 = rawRow17421 := by decide +kernel

theorem rowCheck17421 : row17421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17421 := by decide +kernel

theorem rowEval17421 (x : Key → ℝ) : Integer.Sparse.eval row17421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17421, Integer.Sparse.eval_collectBalanced, rawRowCheck17421]

theorem rawRowCheck17422 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form1 = rawRow17422 := by decide +kernel

theorem rowCheck17422 : row17422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17422 := by decide +kernel

theorem rowEval17422 (x : Key → ℝ) : Integer.Sparse.eval row17422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17422, Integer.Sparse.eval_collectBalanced, rawRowCheck17422]

theorem rawRowCheck17423 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form1 = rawRow17423 := by decide +kernel

theorem rowCheck17423 : row17423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17423 := by decide +kernel

theorem rowEval17423 (x : Key → ℝ) : Integer.Sparse.eval row17423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17423, Integer.Sparse.eval_collectBalanced, rawRowCheck17423]

theorem rawRowCheck17424 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form1 = rawRow17424 := by decide +kernel

theorem rowCheck17424 : row17424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17424 := by decide +kernel

theorem rowEval17424 (x : Key → ℝ) : Integer.Sparse.eval row17424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17424, Integer.Sparse.eval_collectBalanced, rawRowCheck17424]

theorem rawRowCheck17425 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form1 = rawRow17425 := by decide +kernel

theorem rowCheck17425 : row17425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17425 := by decide +kernel

theorem rowEval17425 (x : Key → ℝ) : Integer.Sparse.eval row17425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17425, Integer.Sparse.eval_collectBalanced, rawRowCheck17425]

theorem rawRowCheck17426 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form1 = rawRow17426 := by decide +kernel

theorem rowCheck17426 : row17426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17426 := by decide +kernel

theorem rowEval17426 (x : Key → ℝ) : Integer.Sparse.eval row17426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17426, Integer.Sparse.eval_collectBalanced, rawRowCheck17426]

theorem rawRowCheck17427 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form1 = rawRow17427 := by decide +kernel

theorem rowCheck17427 : row17427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17427 := by decide +kernel

theorem rowEval17427 (x : Key → ℝ) : Integer.Sparse.eval row17427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17427, Integer.Sparse.eval_collectBalanced, rawRowCheck17427]

theorem rawRowCheck17428 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form1 = rawRow17428 := by decide +kernel

theorem rowCheck17428 : row17428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17428 := by decide +kernel

theorem rowEval17428 (x : Key → ℝ) : Integer.Sparse.eval row17428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17428, Integer.Sparse.eval_collectBalanced, rawRowCheck17428]

theorem rawRowCheck17429 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form1 = rawRow17429 := by decide +kernel

theorem rowCheck17429 : row17429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17429 := by decide +kernel

theorem rowEval17429 (x : Key → ℝ) : Integer.Sparse.eval row17429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17429, Integer.Sparse.eval_collectBalanced, rawRowCheck17429]

theorem rawRowCheck17430 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow17430 := by decide +kernel

theorem rowCheck17430 : row17430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17430 := by decide +kernel

theorem rowEval17430 (x : Key → ℝ) : Integer.Sparse.eval row17430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17430, Integer.Sparse.eval_collectBalanced, rawRowCheck17430]

theorem rawRowCheck17431 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form2 = rawRow17431 := by decide +kernel

theorem rowCheck17431 : row17431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17431 := by decide +kernel

theorem rowEval17431 (x : Key → ℝ) : Integer.Sparse.eval row17431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17431, Integer.Sparse.eval_collectBalanced, rawRowCheck17431]

theorem rawRowCheck17432 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form2 = rawRow17432 := by decide +kernel

theorem rowCheck17432 : row17432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17432 := by decide +kernel

theorem rowEval17432 (x : Key → ℝ) : Integer.Sparse.eval row17432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17432, Integer.Sparse.eval_collectBalanced, rawRowCheck17432]

theorem rawRowCheck17433 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form2 = rawRow17433 := by decide +kernel

theorem rowCheck17433 : row17433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17433 := by decide +kernel

theorem rowEval17433 (x : Key → ℝ) : Integer.Sparse.eval row17433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17433, Integer.Sparse.eval_collectBalanced, rawRowCheck17433]

theorem rawRowCheck17434 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form2 = rawRow17434 := by decide +kernel

theorem rowCheck17434 : row17434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17434 := by decide +kernel

theorem rowEval17434 (x : Key → ℝ) : Integer.Sparse.eval row17434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17434, Integer.Sparse.eval_collectBalanced, rawRowCheck17434]

theorem rawRowCheck17435 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form2 = rawRow17435 := by decide +kernel

theorem rowCheck17435 : row17435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17435 := by decide +kernel

theorem rowEval17435 (x : Key → ℝ) : Integer.Sparse.eval row17435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17435, Integer.Sparse.eval_collectBalanced, rawRowCheck17435]

theorem rawRowCheck17436 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form2 = rawRow17436 := by decide +kernel

theorem rowCheck17436 : row17436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17436 := by decide +kernel

theorem rowEval17436 (x : Key → ℝ) : Integer.Sparse.eval row17436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17436, Integer.Sparse.eval_collectBalanced, rawRowCheck17436]

theorem rawRowCheck17437 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form2 = rawRow17437 := by decide +kernel

theorem rowCheck17437 : row17437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17437 := by decide +kernel

theorem rowEval17437 (x : Key → ℝ) : Integer.Sparse.eval row17437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17437, Integer.Sparse.eval_collectBalanced, rawRowCheck17437]

theorem rawRowCheck17438 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form2 = rawRow17438 := by decide +kernel

theorem rowCheck17438 : row17438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17438 := by decide +kernel

theorem rowEval17438 (x : Key → ℝ) : Integer.Sparse.eval row17438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17438, Integer.Sparse.eval_collectBalanced, rawRowCheck17438]

theorem rawRowCheck17439 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form2 = rawRow17439 := by decide +kernel

theorem rowCheck17439 : row17439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17439 := by decide +kernel

theorem rowEval17439 (x : Key → ℝ) : Integer.Sparse.eval row17439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17439, Integer.Sparse.eval_collectBalanced, rawRowCheck17439]

theorem rawRowCheck17440 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow17440 := by decide +kernel

theorem rowCheck17440 : row17440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17440 := by decide +kernel

theorem rowEval17440 (x : Key → ℝ) : Integer.Sparse.eval row17440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17440, Integer.Sparse.eval_collectBalanced, rawRowCheck17440]

theorem rawRowCheck17441 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form3 = rawRow17441 := by decide +kernel

theorem rowCheck17441 : row17441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17441 := by decide +kernel

theorem rowEval17441 (x : Key → ℝ) : Integer.Sparse.eval row17441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17441, Integer.Sparse.eval_collectBalanced, rawRowCheck17441]

theorem rawRowCheck17442 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form3 = rawRow17442 := by decide +kernel

theorem rowCheck17442 : row17442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17442 := by decide +kernel

theorem rowEval17442 (x : Key → ℝ) : Integer.Sparse.eval row17442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17442, Integer.Sparse.eval_collectBalanced, rawRowCheck17442]

theorem rawRowCheck17443 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form3 = rawRow17443 := by decide +kernel

theorem rowCheck17443 : row17443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17443 := by decide +kernel

theorem rowEval17443 (x : Key → ℝ) : Integer.Sparse.eval row17443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17443, Integer.Sparse.eval_collectBalanced, rawRowCheck17443]

theorem rawRowCheck17444 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form3 = rawRow17444 := by decide +kernel

theorem rowCheck17444 : row17444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17444 := by decide +kernel

theorem rowEval17444 (x : Key → ℝ) : Integer.Sparse.eval row17444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17444, Integer.Sparse.eval_collectBalanced, rawRowCheck17444]

theorem rawRowCheck17445 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form3 = rawRow17445 := by decide +kernel

theorem rowCheck17445 : row17445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17445 := by decide +kernel

theorem rowEval17445 (x : Key → ℝ) : Integer.Sparse.eval row17445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17445, Integer.Sparse.eval_collectBalanced, rawRowCheck17445]

theorem rawRowCheck17446 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form3 = rawRow17446 := by decide +kernel

theorem rowCheck17446 : row17446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17446 := by decide +kernel

theorem rowEval17446 (x : Key → ℝ) : Integer.Sparse.eval row17446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17446, Integer.Sparse.eval_collectBalanced, rawRowCheck17446]

theorem rawRowCheck17447 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form3 = rawRow17447 := by decide +kernel

theorem rowCheck17447 : row17447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17447 := by decide +kernel

theorem rowEval17447 (x : Key → ℝ) : Integer.Sparse.eval row17447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17447, Integer.Sparse.eval_collectBalanced, rawRowCheck17447]

theorem rawRowCheck17448 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form3 = rawRow17448 := by decide +kernel

theorem rowCheck17448 : row17448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17448 := by decide +kernel

theorem rowEval17448 (x : Key → ℝ) : Integer.Sparse.eval row17448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17448, Integer.Sparse.eval_collectBalanced, rawRowCheck17448]

theorem rawRowCheck17449 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form3 = rawRow17449 := by decide +kernel

theorem rowCheck17449 : row17449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17449 := by decide +kernel

theorem rowEval17449 (x : Key → ℝ) : Integer.Sparse.eval row17449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17449, Integer.Sparse.eval_collectBalanced, rawRowCheck17449]

theorem rawRowCheck17450 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow17450 := by decide +kernel

theorem rowCheck17450 : row17450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17450 := by decide +kernel

theorem rowEval17450 (x : Key → ℝ) : Integer.Sparse.eval row17450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17450, Integer.Sparse.eval_collectBalanced, rawRowCheck17450]

theorem rawRowCheck17451 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form4 = rawRow17451 := by decide +kernel

theorem rowCheck17451 : row17451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17451 := by decide +kernel

theorem rowEval17451 (x : Key → ℝ) : Integer.Sparse.eval row17451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17451, Integer.Sparse.eval_collectBalanced, rawRowCheck17451]

theorem rawRowCheck17452 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form4 = rawRow17452 := by decide +kernel

theorem rowCheck17452 : row17452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17452 := by decide +kernel

theorem rowEval17452 (x : Key → ℝ) : Integer.Sparse.eval row17452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17452, Integer.Sparse.eval_collectBalanced, rawRowCheck17452]

theorem rawRowCheck17453 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form4 = rawRow17453 := by decide +kernel

theorem rowCheck17453 : row17453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17453 := by decide +kernel

theorem rowEval17453 (x : Key → ℝ) : Integer.Sparse.eval row17453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17453, Integer.Sparse.eval_collectBalanced, rawRowCheck17453]

theorem rawRowCheck17454 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17454 := by decide +kernel

theorem rowCheck17454 : row17454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17454 := by decide +kernel

theorem rowEval17454 (x : Key → ℝ) : Integer.Sparse.eval row17454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17454, Integer.Sparse.eval_collectBalanced, rawRowCheck17454]

theorem rawRowCheck17455 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17455 := by decide +kernel

theorem rowCheck17455 : row17455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17455 := by decide +kernel

theorem rowEval17455 (x : Key → ℝ) : Integer.Sparse.eval row17455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17455, Integer.Sparse.eval_collectBalanced, rawRowCheck17455]

theorem rawRowCheck17456 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17456 := by decide +kernel

theorem rowCheck17456 : row17456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17456 := by decide +kernel

theorem rowEval17456 (x : Key → ℝ) : Integer.Sparse.eval row17456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17456, Integer.Sparse.eval_collectBalanced, rawRowCheck17456]

theorem rawRowCheck17457 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17457 := by decide +kernel

theorem rowCheck17457 : row17457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17457 := by decide +kernel

theorem rowEval17457 (x : Key → ℝ) : Integer.Sparse.eval row17457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17457, Integer.Sparse.eval_collectBalanced, rawRowCheck17457]

theorem rawRowCheck17458 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17458 := by decide +kernel

theorem rowCheck17458 : row17458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17458 := by decide +kernel

theorem rowEval17458 (x : Key → ℝ) : Integer.Sparse.eval row17458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17458, Integer.Sparse.eval_collectBalanced, rawRowCheck17458]

theorem rawRowCheck17459 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17459 := by decide +kernel

theorem rowCheck17459 : row17459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17459 := by decide +kernel

theorem rowEval17459 (x : Key → ℝ) : Integer.Sparse.eval row17459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17459, Integer.Sparse.eval_collectBalanced, rawRowCheck17459]

theorem rawRowCheck17460 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form4 = rawRow17460 := by decide +kernel

theorem rowCheck17460 : row17460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17460 := by decide +kernel

theorem rowEval17460 (x : Key → ℝ) : Integer.Sparse.eval row17460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17460, Integer.Sparse.eval_collectBalanced, rawRowCheck17460]

theorem rawRowCheck17461 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form5 = rawRow17461 := by decide +kernel

theorem rowCheck17461 : row17461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17461 := by decide +kernel

theorem rowEval17461 (x : Key → ℝ) : Integer.Sparse.eval row17461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17461, Integer.Sparse.eval_collectBalanced, rawRowCheck17461]

theorem rawRowCheck17462 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form5 = rawRow17462 := by decide +kernel

theorem rowCheck17462 : row17462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17462 := by decide +kernel

theorem rowEval17462 (x : Key → ℝ) : Integer.Sparse.eval row17462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17462, Integer.Sparse.eval_collectBalanced, rawRowCheck17462]

theorem rawRowCheck17463 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form5 = rawRow17463 := by decide +kernel

theorem rowCheck17463 : row17463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17463 := by decide +kernel

theorem rowEval17463 (x : Key → ℝ) : Integer.Sparse.eval row17463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17463, Integer.Sparse.eval_collectBalanced, rawRowCheck17463]

theorem rawRowCheck17464 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17464 := by decide +kernel

theorem rowCheck17464 : row17464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17464 := by decide +kernel

theorem rowEval17464 (x : Key → ℝ) : Integer.Sparse.eval row17464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17464, Integer.Sparse.eval_collectBalanced, rawRowCheck17464]

theorem rawRowCheck17465 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17465 := by decide +kernel

theorem rowCheck17465 : row17465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17465 := by decide +kernel

theorem rowEval17465 (x : Key → ℝ) : Integer.Sparse.eval row17465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17465, Integer.Sparse.eval_collectBalanced, rawRowCheck17465]

theorem rawRowCheck17466 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17466 := by decide +kernel

theorem rowCheck17466 : row17466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17466 := by decide +kernel

theorem rowEval17466 (x : Key → ℝ) : Integer.Sparse.eval row17466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17466, Integer.Sparse.eval_collectBalanced, rawRowCheck17466]

theorem rawRowCheck17467 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17467 := by decide +kernel

theorem rowCheck17467 : row17467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17467 := by decide +kernel

theorem rowEval17467 (x : Key → ℝ) : Integer.Sparse.eval row17467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17467, Integer.Sparse.eval_collectBalanced, rawRowCheck17467]

theorem rawRowCheck17468 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17468 := by decide +kernel

theorem rowCheck17468 : row17468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17468 := by decide +kernel

theorem rowEval17468 (x : Key → ℝ) : Integer.Sparse.eval row17468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17468, Integer.Sparse.eval_collectBalanced, rawRowCheck17468]

theorem rawRowCheck17469 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17469 := by decide +kernel

theorem rowCheck17469 : row17469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17469 := by decide +kernel

theorem rowEval17469 (x : Key → ℝ) : Integer.Sparse.eval row17469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17469, Integer.Sparse.eval_collectBalanced, rawRowCheck17469]

theorem rawRowCheck17470 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form5 = rawRow17470 := by decide +kernel

theorem rowCheck17470 : row17470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17470 := by decide +kernel

theorem rowEval17470 (x : Key → ℝ) : Integer.Sparse.eval row17470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17470, Integer.Sparse.eval_collectBalanced, rawRowCheck17470]

theorem rawRowCheck17471 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form6 = rawRow17471 := by decide +kernel

theorem rowCheck17471 : row17471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17471 := by decide +kernel

theorem rowEval17471 (x : Key → ℝ) : Integer.Sparse.eval row17471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17471, Integer.Sparse.eval_collectBalanced, rawRowCheck17471]

theorem rawRowCheck17472 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form6 = rawRow17472 := by decide +kernel

theorem rowCheck17472 : row17472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17472 := by decide +kernel

theorem rowEval17472 (x : Key → ℝ) : Integer.Sparse.eval row17472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17472, Integer.Sparse.eval_collectBalanced, rawRowCheck17472]

theorem rawRowCheck17473 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form6 = rawRow17473 := by decide +kernel

theorem rowCheck17473 : row17473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17473 := by decide +kernel

theorem rowEval17473 (x : Key → ℝ) : Integer.Sparse.eval row17473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17473, Integer.Sparse.eval_collectBalanced, rawRowCheck17473]

theorem rawRowCheck17474 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form6 = rawRow17474 := by decide +kernel

theorem rowCheck17474 : row17474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17474 := by decide +kernel

theorem rowEval17474 (x : Key → ℝ) : Integer.Sparse.eval row17474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17474, Integer.Sparse.eval_collectBalanced, rawRowCheck17474]

theorem rawRowCheck17475 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form6 = rawRow17475 := by decide +kernel

theorem rowCheck17475 : row17475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17475 := by decide +kernel

theorem rowEval17475 (x : Key → ℝ) : Integer.Sparse.eval row17475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17475, Integer.Sparse.eval_collectBalanced, rawRowCheck17475]

theorem rawRowCheck17476 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form6 = rawRow17476 := by decide +kernel

theorem rowCheck17476 : row17476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17476 := by decide +kernel

theorem rowEval17476 (x : Key → ℝ) : Integer.Sparse.eval row17476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17476, Integer.Sparse.eval_collectBalanced, rawRowCheck17476]

theorem rawRowCheck17477 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form6 = rawRow17477 := by decide +kernel

theorem rowCheck17477 : row17477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17477 := by decide +kernel

theorem rowEval17477 (x : Key → ℝ) : Integer.Sparse.eval row17477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17477, Integer.Sparse.eval_collectBalanced, rawRowCheck17477]

theorem rawRowCheck17478 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form6 = rawRow17478 := by decide +kernel

theorem rowCheck17478 : row17478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17478 := by decide +kernel

theorem rowEval17478 (x : Key → ℝ) : Integer.Sparse.eval row17478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17478, Integer.Sparse.eval_collectBalanced, rawRowCheck17478]

theorem rawRowCheck17479 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form6 = rawRow17479 := by decide +kernel

theorem rowCheck17479 : row17479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17479 := by decide +kernel

theorem rowEval17479 (x : Key → ℝ) : Integer.Sparse.eval row17479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17479, Integer.Sparse.eval_collectBalanced, rawRowCheck17479]

theorem rawRowCheck17480 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form6 = rawRow17480 := by decide +kernel

theorem rowCheck17480 : row17480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17480 := by decide +kernel

theorem rowEval17480 (x : Key → ℝ) : Integer.Sparse.eval row17480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17480, Integer.Sparse.eval_collectBalanced, rawRowCheck17480]

theorem rawRowCheck17481 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form7 = rawRow17481 := by decide +kernel

theorem rowCheck17481 : row17481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17481 := by decide +kernel

theorem rowEval17481 (x : Key → ℝ) : Integer.Sparse.eval row17481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17481, Integer.Sparse.eval_collectBalanced, rawRowCheck17481]

theorem rawRowCheck17482 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form7 = rawRow17482 := by decide +kernel

theorem rowCheck17482 : row17482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17482 := by decide +kernel

theorem rowEval17482 (x : Key → ℝ) : Integer.Sparse.eval row17482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17482, Integer.Sparse.eval_collectBalanced, rawRowCheck17482]

theorem rawRowCheck17483 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form7 = rawRow17483 := by decide +kernel

theorem rowCheck17483 : row17483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17483 := by decide +kernel

theorem rowEval17483 (x : Key → ℝ) : Integer.Sparse.eval row17483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17483, Integer.Sparse.eval_collectBalanced, rawRowCheck17483]

theorem rawRowCheck17484 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17484 := by decide +kernel

theorem rowCheck17484 : row17484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17484 := by decide +kernel

theorem rowEval17484 (x : Key → ℝ) : Integer.Sparse.eval row17484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17484, Integer.Sparse.eval_collectBalanced, rawRowCheck17484]

theorem rawRowCheck17485 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17485 := by decide +kernel

theorem rowCheck17485 : row17485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17485 := by decide +kernel

theorem rowEval17485 (x : Key → ℝ) : Integer.Sparse.eval row17485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17485, Integer.Sparse.eval_collectBalanced, rawRowCheck17485]

theorem rawRowCheck17486 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17486 := by decide +kernel

theorem rowCheck17486 : row17486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17486 := by decide +kernel

theorem rowEval17486 (x : Key → ℝ) : Integer.Sparse.eval row17486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17486, Integer.Sparse.eval_collectBalanced, rawRowCheck17486]

theorem rawRowCheck17487 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17487 := by decide +kernel

theorem rowCheck17487 : row17487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17487 := by decide +kernel

theorem rowEval17487 (x : Key → ℝ) : Integer.Sparse.eval row17487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17487, Integer.Sparse.eval_collectBalanced, rawRowCheck17487]

theorem rawRowCheck17488 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17488 := by decide +kernel

theorem rowCheck17488 : row17488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17488 := by decide +kernel

theorem rowEval17488 (x : Key → ℝ) : Integer.Sparse.eval row17488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17488, Integer.Sparse.eval_collectBalanced, rawRowCheck17488]

theorem rawRowCheck17489 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17489 := by decide +kernel

theorem rowCheck17489 : row17489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17489 := by decide +kernel

theorem rowEval17489 (x : Key → ℝ) : Integer.Sparse.eval row17489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17489, Integer.Sparse.eval_collectBalanced, rawRowCheck17489]

theorem rawRowCheck17490 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form7 = rawRow17490 := by decide +kernel

theorem rowCheck17490 : row17490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17490 := by decide +kernel

theorem rowEval17490 (x : Key → ℝ) : Integer.Sparse.eval row17490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17490, Integer.Sparse.eval_collectBalanced, rawRowCheck17490]

theorem rawRowCheck17491 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form8 = rawRow17491 := by decide +kernel

theorem rowCheck17491 : row17491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17491 := by decide +kernel

theorem rowEval17491 (x : Key → ℝ) : Integer.Sparse.eval row17491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17491, Integer.Sparse.eval_collectBalanced, rawRowCheck17491]

theorem rawRowCheck17492 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form8 = rawRow17492 := by decide +kernel

theorem rowCheck17492 : row17492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17492 := by decide +kernel

theorem rowEval17492 (x : Key → ℝ) : Integer.Sparse.eval row17492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17492, Integer.Sparse.eval_collectBalanced, rawRowCheck17492]

theorem rawRowCheck17493 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form8 = rawRow17493 := by decide +kernel

theorem rowCheck17493 : row17493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17493 := by decide +kernel

theorem rowEval17493 (x : Key → ℝ) : Integer.Sparse.eval row17493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17493, Integer.Sparse.eval_collectBalanced, rawRowCheck17493]

theorem rawRowCheck17494 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form8 = rawRow17494 := by decide +kernel

theorem rowCheck17494 : row17494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17494 := by decide +kernel

theorem rowEval17494 (x : Key → ℝ) : Integer.Sparse.eval row17494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17494, Integer.Sparse.eval_collectBalanced, rawRowCheck17494]

theorem rawRowCheck17495 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form8 = rawRow17495 := by decide +kernel

theorem rowCheck17495 : row17495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17495 := by decide +kernel

theorem rowEval17495 (x : Key → ℝ) : Integer.Sparse.eval row17495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17495, Integer.Sparse.eval_collectBalanced, rawRowCheck17495]

theorem rawRowCheck17496 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form8 = rawRow17496 := by decide +kernel

theorem rowCheck17496 : row17496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17496 := by decide +kernel

theorem rowEval17496 (x : Key → ℝ) : Integer.Sparse.eval row17496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17496, Integer.Sparse.eval_collectBalanced, rawRowCheck17496]

theorem rawRowCheck17497 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form8 = rawRow17497 := by decide +kernel

theorem rowCheck17497 : row17497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17497 := by decide +kernel

theorem rowEval17497 (x : Key → ℝ) : Integer.Sparse.eval row17497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17497, Integer.Sparse.eval_collectBalanced, rawRowCheck17497]

theorem rawRowCheck17498 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form8 = rawRow17498 := by decide +kernel

theorem rowCheck17498 : row17498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17498 := by decide +kernel

theorem rowEval17498 (x : Key → ℝ) : Integer.Sparse.eval row17498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17498, Integer.Sparse.eval_collectBalanced, rawRowCheck17498]

theorem rawRowCheck17499 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form8 = rawRow17499 := by decide +kernel

theorem rowCheck17499 : row17499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17499 := by decide +kernel

theorem rowEval17499 (x : Key → ℝ) : Integer.Sparse.eval row17499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17499, Integer.Sparse.eval_collectBalanced, rawRowCheck17499]

theorem rawRowCheck17500 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form8 = rawRow17500 := by decide +kernel

theorem rowCheck17500 : row17500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17500 := by decide +kernel

theorem rowEval17500 (x : Key → ℝ) : Integer.Sparse.eval row17500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17500, Integer.Sparse.eval_collectBalanced, rawRowCheck17500]

theorem rawRowCheck17501 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form9 = rawRow17501 := by decide +kernel

theorem rowCheck17501 : row17501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17501 := by decide +kernel

theorem rowEval17501 (x : Key → ℝ) : Integer.Sparse.eval row17501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17501, Integer.Sparse.eval_collectBalanced, rawRowCheck17501]

theorem rawRowCheck17502 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form9 = rawRow17502 := by decide +kernel

theorem rowCheck17502 : row17502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17502 := by decide +kernel

theorem rowEval17502 (x : Key → ℝ) : Integer.Sparse.eval row17502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17502, Integer.Sparse.eval_collectBalanced, rawRowCheck17502]

theorem rawRowCheck17503 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form9 = rawRow17503 := by decide +kernel

theorem rowCheck17503 : row17503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17503 := by decide +kernel

theorem rowEval17503 (x : Key → ℝ) : Integer.Sparse.eval row17503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17503, Integer.Sparse.eval_collectBalanced, rawRowCheck17503]

theorem rawRowCheck17504 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17504 := by decide +kernel

theorem rowCheck17504 : row17504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17504 := by decide +kernel

theorem rowEval17504 (x : Key → ℝ) : Integer.Sparse.eval row17504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17504, Integer.Sparse.eval_collectBalanced, rawRowCheck17504]

theorem rawRowCheck17505 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17505 := by decide +kernel

theorem rowCheck17505 : row17505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17505 := by decide +kernel

theorem rowEval17505 (x : Key → ℝ) : Integer.Sparse.eval row17505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17505, Integer.Sparse.eval_collectBalanced, rawRowCheck17505]

theorem rawRowCheck17506 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17506 := by decide +kernel

theorem rowCheck17506 : row17506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17506 := by decide +kernel

theorem rowEval17506 (x : Key → ℝ) : Integer.Sparse.eval row17506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17506, Integer.Sparse.eval_collectBalanced, rawRowCheck17506]

theorem rawRowCheck17507 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17507 := by decide +kernel

theorem rowCheck17507 : row17507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17507 := by decide +kernel

theorem rowEval17507 (x : Key → ℝ) : Integer.Sparse.eval row17507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17507, Integer.Sparse.eval_collectBalanced, rawRowCheck17507]

theorem rawRowCheck17508 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17508 := by decide +kernel

theorem rowCheck17508 : row17508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17508 := by decide +kernel

theorem rowEval17508 (x : Key → ℝ) : Integer.Sparse.eval row17508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17508, Integer.Sparse.eval_collectBalanced, rawRowCheck17508]

theorem rawRowCheck17509 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17509 := by decide +kernel

theorem rowCheck17509 : row17509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17509 := by decide +kernel

theorem rowEval17509 (x : Key → ℝ) : Integer.Sparse.eval row17509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17509, Integer.Sparse.eval_collectBalanced, rawRowCheck17509]

theorem rawRowCheck17510 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form9 = rawRow17510 := by decide +kernel

theorem rowCheck17510 : row17510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17510 := by decide +kernel

theorem rowEval17510 (x : Key → ℝ) : Integer.Sparse.eval row17510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17510, Integer.Sparse.eval_collectBalanced, rawRowCheck17510]

theorem rawRowCheck17511 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form10 = rawRow17511 := by decide +kernel

theorem rowCheck17511 : row17511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17511 := by decide +kernel

theorem rowEval17511 (x : Key → ℝ) : Integer.Sparse.eval row17511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17511, Integer.Sparse.eval_collectBalanced, rawRowCheck17511]

theorem rawRowCheck17512 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form10 = rawRow17512 := by decide +kernel

theorem rowCheck17512 : row17512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17512 := by decide +kernel

theorem rowEval17512 (x : Key → ℝ) : Integer.Sparse.eval row17512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17512, Integer.Sparse.eval_collectBalanced, rawRowCheck17512]

theorem rawRowCheck17513 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form10 = rawRow17513 := by decide +kernel

theorem rowCheck17513 : row17513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17513 := by decide +kernel

theorem rowEval17513 (x : Key → ℝ) : Integer.Sparse.eval row17513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17513, Integer.Sparse.eval_collectBalanced, rawRowCheck17513]

theorem rawRowCheck17514 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form10 = rawRow17514 := by decide +kernel

theorem rowCheck17514 : row17514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17514 := by decide +kernel

theorem rowEval17514 (x : Key → ℝ) : Integer.Sparse.eval row17514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17514, Integer.Sparse.eval_collectBalanced, rawRowCheck17514]

theorem rawRowCheck17515 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form10 = rawRow17515 := by decide +kernel

theorem rowCheck17515 : row17515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17515 := by decide +kernel

theorem rowEval17515 (x : Key → ℝ) : Integer.Sparse.eval row17515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17515, Integer.Sparse.eval_collectBalanced, rawRowCheck17515]

theorem rawRowCheck17516 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form10 = rawRow17516 := by decide +kernel

theorem rowCheck17516 : row17516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17516 := by decide +kernel

theorem rowEval17516 (x : Key → ℝ) : Integer.Sparse.eval row17516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17516, Integer.Sparse.eval_collectBalanced, rawRowCheck17516]

theorem rawRowCheck17517 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form10 = rawRow17517 := by decide +kernel

theorem rowCheck17517 : row17517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17517 := by decide +kernel

theorem rowEval17517 (x : Key → ℝ) : Integer.Sparse.eval row17517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17517, Integer.Sparse.eval_collectBalanced, rawRowCheck17517]

theorem rawRowCheck17518 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form10 = rawRow17518 := by decide +kernel

theorem rowCheck17518 : row17518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17518 := by decide +kernel

theorem rowEval17518 (x : Key → ℝ) : Integer.Sparse.eval row17518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17518, Integer.Sparse.eval_collectBalanced, rawRowCheck17518]

theorem rawRowCheck17519 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form10 = rawRow17519 := by decide +kernel

theorem rowCheck17519 : row17519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17519 := by decide +kernel

theorem rowEval17519 (x : Key → ℝ) : Integer.Sparse.eval row17519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17519, Integer.Sparse.eval_collectBalanced, rawRowCheck17519]

theorem rawRowCheck17520 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form10 = rawRow17520 := by decide +kernel

theorem rowCheck17520 : row17520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17520 := by decide +kernel

theorem rowEval17520 (x : Key → ℝ) : Integer.Sparse.eval row17520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17520, Integer.Sparse.eval_collectBalanced, rawRowCheck17520]

theorem rawRowCheck17521 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form11 = rawRow17521 := by decide +kernel

theorem rowCheck17521 : row17521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17521 := by decide +kernel

theorem rowEval17521 (x : Key → ℝ) : Integer.Sparse.eval row17521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17521, Integer.Sparse.eval_collectBalanced, rawRowCheck17521]

theorem rawRowCheck17522 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form11 = rawRow17522 := by decide +kernel

theorem rowCheck17522 : row17522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17522 := by decide +kernel

theorem rowEval17522 (x : Key → ℝ) : Integer.Sparse.eval row17522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17522, Integer.Sparse.eval_collectBalanced, rawRowCheck17522]

theorem rawRowCheck17523 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form11 = rawRow17523 := by decide +kernel

theorem rowCheck17523 : row17523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17523 := by decide +kernel

theorem rowEval17523 (x : Key → ℝ) : Integer.Sparse.eval row17523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17523, Integer.Sparse.eval_collectBalanced, rawRowCheck17523]

theorem rawRowCheck17524 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form11 = rawRow17524 := by decide +kernel

theorem rowCheck17524 : row17524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17524 := by decide +kernel

theorem rowEval17524 (x : Key → ℝ) : Integer.Sparse.eval row17524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17524, Integer.Sparse.eval_collectBalanced, rawRowCheck17524]

theorem rawRowCheck17525 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form11 = rawRow17525 := by decide +kernel

theorem rowCheck17525 : row17525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17525 := by decide +kernel

theorem rowEval17525 (x : Key → ℝ) : Integer.Sparse.eval row17525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17525, Integer.Sparse.eval_collectBalanced, rawRowCheck17525]

theorem rawRowCheck17526 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form11 = rawRow17526 := by decide +kernel

theorem rowCheck17526 : row17526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17526 := by decide +kernel

theorem rowEval17526 (x : Key → ℝ) : Integer.Sparse.eval row17526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17526, Integer.Sparse.eval_collectBalanced, rawRowCheck17526]

theorem rawRowCheck17527 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form11 = rawRow17527 := by decide +kernel

theorem rowCheck17527 : row17527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17527 := by decide +kernel

theorem rowEval17527 (x : Key → ℝ) : Integer.Sparse.eval row17527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17527, Integer.Sparse.eval_collectBalanced, rawRowCheck17527]

theorem rawRowCheck17528 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form11 = rawRow17528 := by decide +kernel

theorem rowCheck17528 : row17528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17528 := by decide +kernel

theorem rowEval17528 (x : Key → ℝ) : Integer.Sparse.eval row17528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17528, Integer.Sparse.eval_collectBalanced, rawRowCheck17528]

theorem rawRowCheck17529 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form11 = rawRow17529 := by decide +kernel

theorem rowCheck17529 : row17529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17529 := by decide +kernel

theorem rowEval17529 (x : Key → ℝ) : Integer.Sparse.eval row17529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17529, Integer.Sparse.eval_collectBalanced, rawRowCheck17529]

theorem rawRowCheck17530 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form11 = rawRow17530 := by decide +kernel

theorem rowCheck17530 : row17530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17530 := by decide +kernel

theorem rowEval17530 (x : Key → ℝ) : Integer.Sparse.eval row17530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17530, Integer.Sparse.eval_collectBalanced, rawRowCheck17530]

theorem rawRowCheck17531 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form12 = rawRow17531 := by decide +kernel

theorem rowCheck17531 : row17531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17531 := by decide +kernel

theorem rowEval17531 (x : Key → ℝ) : Integer.Sparse.eval row17531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17531, Integer.Sparse.eval_collectBalanced, rawRowCheck17531]

theorem rawRowCheck17532 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form12 = rawRow17532 := by decide +kernel

theorem rowCheck17532 : row17532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17532 := by decide +kernel

theorem rowEval17532 (x : Key → ℝ) : Integer.Sparse.eval row17532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17532, Integer.Sparse.eval_collectBalanced, rawRowCheck17532]

theorem rawRowCheck17533 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form12 = rawRow17533 := by decide +kernel

theorem rowCheck17533 : row17533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17533 := by decide +kernel

theorem rowEval17533 (x : Key → ℝ) : Integer.Sparse.eval row17533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17533, Integer.Sparse.eval_collectBalanced, rawRowCheck17533]

theorem rawRowCheck17534 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form12 = rawRow17534 := by decide +kernel

theorem rowCheck17534 : row17534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17534 := by decide +kernel

theorem rowEval17534 (x : Key → ℝ) : Integer.Sparse.eval row17534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17534, Integer.Sparse.eval_collectBalanced, rawRowCheck17534]

theorem rawRowCheck17535 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form12 = rawRow17535 := by decide +kernel

theorem rowCheck17535 : row17535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17535 := by decide +kernel

theorem rowEval17535 (x : Key → ℝ) : Integer.Sparse.eval row17535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17535, Integer.Sparse.eval_collectBalanced, rawRowCheck17535]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17536 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form12 = rawRow17536 := by decide +kernel

theorem rowCheck17536 : row17536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17536 := by decide +kernel

theorem rowEval17536 (x : Key → ℝ) : Integer.Sparse.eval row17536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17536, Integer.Sparse.eval_collectBalanced, rawRowCheck17536]

theorem rawRowCheck17537 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form12 = rawRow17537 := by decide +kernel

theorem rowCheck17537 : row17537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17537 := by decide +kernel

theorem rowEval17537 (x : Key → ℝ) : Integer.Sparse.eval row17537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17537, Integer.Sparse.eval_collectBalanced, rawRowCheck17537]

theorem rawRowCheck17538 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form12 = rawRow17538 := by decide +kernel

theorem rowCheck17538 : row17538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17538 := by decide +kernel

theorem rowEval17538 (x : Key → ℝ) : Integer.Sparse.eval row17538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17538, Integer.Sparse.eval_collectBalanced, rawRowCheck17538]

theorem rawRowCheck17539 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form12 = rawRow17539 := by decide +kernel

theorem rowCheck17539 : row17539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17539 := by decide +kernel

theorem rowEval17539 (x : Key → ℝ) : Integer.Sparse.eval row17539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17539, Integer.Sparse.eval_collectBalanced, rawRowCheck17539]

theorem rawRowCheck17540 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form12 = rawRow17540 := by decide +kernel

theorem rowCheck17540 : row17540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17540 := by decide +kernel

theorem rowEval17540 (x : Key → ℝ) : Integer.Sparse.eval row17540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17540, Integer.Sparse.eval_collectBalanced, rawRowCheck17540]

theorem rawRowCheck17541 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form13 = rawRow17541 := by decide +kernel

theorem rowCheck17541 : row17541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17541 := by decide +kernel

theorem rowEval17541 (x : Key → ℝ) : Integer.Sparse.eval row17541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17541, Integer.Sparse.eval_collectBalanced, rawRowCheck17541]

theorem rawRowCheck17542 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form13 = rawRow17542 := by decide +kernel

theorem rowCheck17542 : row17542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17542 := by decide +kernel

theorem rowEval17542 (x : Key → ℝ) : Integer.Sparse.eval row17542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17542, Integer.Sparse.eval_collectBalanced, rawRowCheck17542]

theorem rawRowCheck17543 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form13 = rawRow17543 := by decide +kernel

theorem rowCheck17543 : row17543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17543 := by decide +kernel

theorem rowEval17543 (x : Key → ℝ) : Integer.Sparse.eval row17543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17543, Integer.Sparse.eval_collectBalanced, rawRowCheck17543]

theorem rawRowCheck17544 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form13 = rawRow17544 := by decide +kernel

theorem rowCheck17544 : row17544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17544 := by decide +kernel

theorem rowEval17544 (x : Key → ℝ) : Integer.Sparse.eval row17544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17544, Integer.Sparse.eval_collectBalanced, rawRowCheck17544]

theorem rawRowCheck17545 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form13 = rawRow17545 := by decide +kernel

theorem rowCheck17545 : row17545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17545 := by decide +kernel

theorem rowEval17545 (x : Key → ℝ) : Integer.Sparse.eval row17545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17545, Integer.Sparse.eval_collectBalanced, rawRowCheck17545]

theorem rawRowCheck17546 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form13 = rawRow17546 := by decide +kernel

theorem rowCheck17546 : row17546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17546 := by decide +kernel

theorem rowEval17546 (x : Key → ℝ) : Integer.Sparse.eval row17546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17546, Integer.Sparse.eval_collectBalanced, rawRowCheck17546]

theorem rawRowCheck17547 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form13 = rawRow17547 := by decide +kernel

theorem rowCheck17547 : row17547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17547 := by decide +kernel

theorem rowEval17547 (x : Key → ℝ) : Integer.Sparse.eval row17547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17547, Integer.Sparse.eval_collectBalanced, rawRowCheck17547]

theorem rawRowCheck17548 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form13 = rawRow17548 := by decide +kernel

theorem rowCheck17548 : row17548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17548 := by decide +kernel

theorem rowEval17548 (x : Key → ℝ) : Integer.Sparse.eval row17548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17548, Integer.Sparse.eval_collectBalanced, rawRowCheck17548]

theorem rawRowCheck17549 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form13 = rawRow17549 := by decide +kernel

theorem rowCheck17549 : row17549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17549 := by decide +kernel

theorem rowEval17549 (x : Key → ℝ) : Integer.Sparse.eval row17549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17549, Integer.Sparse.eval_collectBalanced, rawRowCheck17549]

theorem rawRowCheck17550 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form13 = rawRow17550 := by decide +kernel

theorem rowCheck17550 : row17550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17550 := by decide +kernel

theorem rowEval17550 (x : Key → ℝ) : Integer.Sparse.eval row17550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17550, Integer.Sparse.eval_collectBalanced, rawRowCheck17550]

theorem rawRowCheck17551 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form14 = rawRow17551 := by decide +kernel

theorem rowCheck17551 : row17551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17551 := by decide +kernel

theorem rowEval17551 (x : Key → ℝ) : Integer.Sparse.eval row17551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17551, Integer.Sparse.eval_collectBalanced, rawRowCheck17551]

theorem rawRowCheck17552 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form14 = rawRow17552 := by decide +kernel

theorem rowCheck17552 : row17552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17552 := by decide +kernel

theorem rowEval17552 (x : Key → ℝ) : Integer.Sparse.eval row17552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17552, Integer.Sparse.eval_collectBalanced, rawRowCheck17552]

theorem rawRowCheck17553 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form14 = rawRow17553 := by decide +kernel

theorem rowCheck17553 : row17553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17553 := by decide +kernel

theorem rowEval17553 (x : Key → ℝ) : Integer.Sparse.eval row17553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17553, Integer.Sparse.eval_collectBalanced, rawRowCheck17553]

theorem rawRowCheck17554 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form14 = rawRow17554 := by decide +kernel

theorem rowCheck17554 : row17554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17554 := by decide +kernel

theorem rowEval17554 (x : Key → ℝ) : Integer.Sparse.eval row17554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17554, Integer.Sparse.eval_collectBalanced, rawRowCheck17554]

theorem rawRowCheck17555 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form14 = rawRow17555 := by decide +kernel

theorem rowCheck17555 : row17555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17555 := by decide +kernel

theorem rowEval17555 (x : Key → ℝ) : Integer.Sparse.eval row17555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17555, Integer.Sparse.eval_collectBalanced, rawRowCheck17555]

theorem rawRowCheck17556 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form14 = rawRow17556 := by decide +kernel

theorem rowCheck17556 : row17556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17556 := by decide +kernel

theorem rowEval17556 (x : Key → ℝ) : Integer.Sparse.eval row17556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17556, Integer.Sparse.eval_collectBalanced, rawRowCheck17556]

theorem rawRowCheck17557 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form14 = rawRow17557 := by decide +kernel

theorem rowCheck17557 : row17557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17557 := by decide +kernel

theorem rowEval17557 (x : Key → ℝ) : Integer.Sparse.eval row17557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17557, Integer.Sparse.eval_collectBalanced, rawRowCheck17557]

theorem rawRowCheck17558 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form14 = rawRow17558 := by decide +kernel

theorem rowCheck17558 : row17558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17558 := by decide +kernel

theorem rowEval17558 (x : Key → ℝ) : Integer.Sparse.eval row17558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17558, Integer.Sparse.eval_collectBalanced, rawRowCheck17558]

theorem rawRowCheck17559 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form14 = rawRow17559 := by decide +kernel

theorem rowCheck17559 : row17559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17559 := by decide +kernel

theorem rowEval17559 (x : Key → ℝ) : Integer.Sparse.eval row17559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17559, Integer.Sparse.eval_collectBalanced, rawRowCheck17559]

theorem rawRowCheck17560 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form14 = rawRow17560 := by decide +kernel

theorem rowCheck17560 : row17560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17560 := by decide +kernel

theorem rowEval17560 (x : Key → ℝ) : Integer.Sparse.eval row17560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17560, Integer.Sparse.eval_collectBalanced, rawRowCheck17560]

theorem rawRowCheck17561 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form15 = rawRow17561 := by decide +kernel

theorem rowCheck17561 : row17561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17561 := by decide +kernel

theorem rowEval17561 (x : Key → ℝ) : Integer.Sparse.eval row17561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17561, Integer.Sparse.eval_collectBalanced, rawRowCheck17561]

theorem rawRowCheck17562 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form15 = rawRow17562 := by decide +kernel

theorem rowCheck17562 : row17562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17562 := by decide +kernel

theorem rowEval17562 (x : Key → ℝ) : Integer.Sparse.eval row17562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17562, Integer.Sparse.eval_collectBalanced, rawRowCheck17562]

theorem rawRowCheck17563 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form15 = rawRow17563 := by decide +kernel

theorem rowCheck17563 : row17563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17563 := by decide +kernel

theorem rowEval17563 (x : Key → ℝ) : Integer.Sparse.eval row17563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17563, Integer.Sparse.eval_collectBalanced, rawRowCheck17563]

theorem rawRowCheck17564 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form15 = rawRow17564 := by decide +kernel

theorem rowCheck17564 : row17564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17564 := by decide +kernel

theorem rowEval17564 (x : Key → ℝ) : Integer.Sparse.eval row17564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17564, Integer.Sparse.eval_collectBalanced, rawRowCheck17564]

theorem rawRowCheck17565 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form15 = rawRow17565 := by decide +kernel

theorem rowCheck17565 : row17565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17565 := by decide +kernel

theorem rowEval17565 (x : Key → ℝ) : Integer.Sparse.eval row17565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17565, Integer.Sparse.eval_collectBalanced, rawRowCheck17565]

theorem rawRowCheck17566 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form15 = rawRow17566 := by decide +kernel

theorem rowCheck17566 : row17566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17566 := by decide +kernel

theorem rowEval17566 (x : Key → ℝ) : Integer.Sparse.eval row17566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17566, Integer.Sparse.eval_collectBalanced, rawRowCheck17566]

theorem rawRowCheck17567 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form15 = rawRow17567 := by decide +kernel

theorem rowCheck17567 : row17567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17567 := by decide +kernel

theorem rowEval17567 (x : Key → ℝ) : Integer.Sparse.eval row17567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17567, Integer.Sparse.eval_collectBalanced, rawRowCheck17567]

theorem rawRowCheck17568 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form15 = rawRow17568 := by decide +kernel

theorem rowCheck17568 : row17568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17568 := by decide +kernel

theorem rowEval17568 (x : Key → ℝ) : Integer.Sparse.eval row17568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17568, Integer.Sparse.eval_collectBalanced, rawRowCheck17568]

theorem rawRowCheck17569 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form15 = rawRow17569 := by decide +kernel

theorem rowCheck17569 : row17569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17569 := by decide +kernel

theorem rowEval17569 (x : Key → ℝ) : Integer.Sparse.eval row17569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17569, Integer.Sparse.eval_collectBalanced, rawRowCheck17569]

theorem rawRowCheck17570 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form15 = rawRow17570 := by decide +kernel

theorem rowCheck17570 : row17570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17570 := by decide +kernel

theorem rowEval17570 (x : Key → ℝ) : Integer.Sparse.eval row17570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17570, Integer.Sparse.eval_collectBalanced, rawRowCheck17570]

theorem rawRowCheck17571 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form16 = rawRow17571 := by decide +kernel

theorem rowCheck17571 : row17571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17571 := by decide +kernel

theorem rowEval17571 (x : Key → ℝ) : Integer.Sparse.eval row17571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17571, Integer.Sparse.eval_collectBalanced, rawRowCheck17571]

theorem rawRowCheck17572 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form16 = rawRow17572 := by decide +kernel

theorem rowCheck17572 : row17572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17572 := by decide +kernel

theorem rowEval17572 (x : Key → ℝ) : Integer.Sparse.eval row17572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17572, Integer.Sparse.eval_collectBalanced, rawRowCheck17572]

theorem rawRowCheck17573 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form16 = rawRow17573 := by decide +kernel

theorem rowCheck17573 : row17573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17573 := by decide +kernel

theorem rowEval17573 (x : Key → ℝ) : Integer.Sparse.eval row17573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17573, Integer.Sparse.eval_collectBalanced, rawRowCheck17573]

theorem rawRowCheck17574 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form16 = rawRow17574 := by decide +kernel

theorem rowCheck17574 : row17574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17574 := by decide +kernel

theorem rowEval17574 (x : Key → ℝ) : Integer.Sparse.eval row17574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17574, Integer.Sparse.eval_collectBalanced, rawRowCheck17574]

theorem rawRowCheck17575 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form16 = rawRow17575 := by decide +kernel

theorem rowCheck17575 : row17575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17575 := by decide +kernel

theorem rowEval17575 (x : Key → ℝ) : Integer.Sparse.eval row17575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17575, Integer.Sparse.eval_collectBalanced, rawRowCheck17575]

theorem rawRowCheck17576 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form16 = rawRow17576 := by decide +kernel

theorem rowCheck17576 : row17576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17576 := by decide +kernel

theorem rowEval17576 (x : Key → ℝ) : Integer.Sparse.eval row17576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17576, Integer.Sparse.eval_collectBalanced, rawRowCheck17576]

theorem rawRowCheck17577 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form16 = rawRow17577 := by decide +kernel

theorem rowCheck17577 : row17577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17577 := by decide +kernel

theorem rowEval17577 (x : Key → ℝ) : Integer.Sparse.eval row17577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17577, Integer.Sparse.eval_collectBalanced, rawRowCheck17577]

theorem rawRowCheck17578 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form16 = rawRow17578 := by decide +kernel

theorem rowCheck17578 : row17578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17578 := by decide +kernel

theorem rowEval17578 (x : Key → ℝ) : Integer.Sparse.eval row17578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17578, Integer.Sparse.eval_collectBalanced, rawRowCheck17578]

theorem rawRowCheck17579 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form16 = rawRow17579 := by decide +kernel

theorem rowCheck17579 : row17579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17579 := by decide +kernel

theorem rowEval17579 (x : Key → ℝ) : Integer.Sparse.eval row17579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17579, Integer.Sparse.eval_collectBalanced, rawRowCheck17579]

theorem rawRowCheck17580 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form16 = rawRow17580 := by decide +kernel

theorem rowCheck17580 : row17580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17580 := by decide +kernel

theorem rowEval17580 (x : Key → ℝ) : Integer.Sparse.eval row17580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17580, Integer.Sparse.eval_collectBalanced, rawRowCheck17580]

theorem rawRowCheck17581 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form17 = rawRow17581 := by decide +kernel

theorem rowCheck17581 : row17581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17581 := by decide +kernel

theorem rowEval17581 (x : Key → ℝ) : Integer.Sparse.eval row17581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17581, Integer.Sparse.eval_collectBalanced, rawRowCheck17581]

theorem rawRowCheck17582 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form17 = rawRow17582 := by decide +kernel

theorem rowCheck17582 : row17582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17582 := by decide +kernel

theorem rowEval17582 (x : Key → ℝ) : Integer.Sparse.eval row17582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17582, Integer.Sparse.eval_collectBalanced, rawRowCheck17582]

theorem rawRowCheck17583 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form17 = rawRow17583 := by decide +kernel

theorem rowCheck17583 : row17583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17583 := by decide +kernel

theorem rowEval17583 (x : Key → ℝ) : Integer.Sparse.eval row17583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17583, Integer.Sparse.eval_collectBalanced, rawRowCheck17583]

theorem rawRowCheck17584 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form17 = rawRow17584 := by decide +kernel

theorem rowCheck17584 : row17584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17584 := by decide +kernel

theorem rowEval17584 (x : Key → ℝ) : Integer.Sparse.eval row17584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17584, Integer.Sparse.eval_collectBalanced, rawRowCheck17584]

theorem rawRowCheck17585 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form17 = rawRow17585 := by decide +kernel

theorem rowCheck17585 : row17585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17585 := by decide +kernel

theorem rowEval17585 (x : Key → ℝ) : Integer.Sparse.eval row17585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17585, Integer.Sparse.eval_collectBalanced, rawRowCheck17585]

theorem rawRowCheck17586 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form17 = rawRow17586 := by decide +kernel

theorem rowCheck17586 : row17586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17586 := by decide +kernel

theorem rowEval17586 (x : Key → ℝ) : Integer.Sparse.eval row17586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17586, Integer.Sparse.eval_collectBalanced, rawRowCheck17586]

theorem rawRowCheck17587 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form17 = rawRow17587 := by decide +kernel

theorem rowCheck17587 : row17587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17587 := by decide +kernel

theorem rowEval17587 (x : Key → ℝ) : Integer.Sparse.eval row17587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17587, Integer.Sparse.eval_collectBalanced, rawRowCheck17587]

theorem rawRowCheck17588 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form17 = rawRow17588 := by decide +kernel

theorem rowCheck17588 : row17588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17588 := by decide +kernel

theorem rowEval17588 (x : Key → ℝ) : Integer.Sparse.eval row17588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17588, Integer.Sparse.eval_collectBalanced, rawRowCheck17588]

theorem rawRowCheck17589 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form17 = rawRow17589 := by decide +kernel

theorem rowCheck17589 : row17589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17589 := by decide +kernel

theorem rowEval17589 (x : Key → ℝ) : Integer.Sparse.eval row17589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17589, Integer.Sparse.eval_collectBalanced, rawRowCheck17589]

theorem rawRowCheck17590 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form17 = rawRow17590 := by decide +kernel

theorem rowCheck17590 : row17590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17590 := by decide +kernel

theorem rowEval17590 (x : Key → ℝ) : Integer.Sparse.eval row17590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17590, Integer.Sparse.eval_collectBalanced, rawRowCheck17590]

theorem rawRowCheck17591 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form18 = rawRow17591 := by decide +kernel

theorem rowCheck17591 : row17591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17591 := by decide +kernel

theorem rowEval17591 (x : Key → ℝ) : Integer.Sparse.eval row17591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17591, Integer.Sparse.eval_collectBalanced, rawRowCheck17591]

theorem rawRowCheck17592 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form18 = rawRow17592 := by decide +kernel

theorem rowCheck17592 : row17592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17592 := by decide +kernel

theorem rowEval17592 (x : Key → ℝ) : Integer.Sparse.eval row17592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17592, Integer.Sparse.eval_collectBalanced, rawRowCheck17592]

theorem rawRowCheck17593 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form18 = rawRow17593 := by decide +kernel

theorem rowCheck17593 : row17593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17593 := by decide +kernel

theorem rowEval17593 (x : Key → ℝ) : Integer.Sparse.eval row17593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17593, Integer.Sparse.eval_collectBalanced, rawRowCheck17593]

theorem rawRowCheck17594 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form18 = rawRow17594 := by decide +kernel

theorem rowCheck17594 : row17594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17594 := by decide +kernel

theorem rowEval17594 (x : Key → ℝ) : Integer.Sparse.eval row17594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17594, Integer.Sparse.eval_collectBalanced, rawRowCheck17594]

theorem rawRowCheck17595 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form18 = rawRow17595 := by decide +kernel

theorem rowCheck17595 : row17595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17595 := by decide +kernel

theorem rowEval17595 (x : Key → ℝ) : Integer.Sparse.eval row17595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17595, Integer.Sparse.eval_collectBalanced, rawRowCheck17595]

theorem rawRowCheck17596 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form18 = rawRow17596 := by decide +kernel

theorem rowCheck17596 : row17596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17596 := by decide +kernel

theorem rowEval17596 (x : Key → ℝ) : Integer.Sparse.eval row17596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17596, Integer.Sparse.eval_collectBalanced, rawRowCheck17596]

theorem rawRowCheck17597 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form18 = rawRow17597 := by decide +kernel

theorem rowCheck17597 : row17597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17597 := by decide +kernel

theorem rowEval17597 (x : Key → ℝ) : Integer.Sparse.eval row17597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17597, Integer.Sparse.eval_collectBalanced, rawRowCheck17597]

theorem rawRowCheck17598 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form18 = rawRow17598 := by decide +kernel

theorem rowCheck17598 : row17598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17598 := by decide +kernel

theorem rowEval17598 (x : Key → ℝ) : Integer.Sparse.eval row17598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17598, Integer.Sparse.eval_collectBalanced, rawRowCheck17598]

theorem rawRowCheck17599 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form18 = rawRow17599 := by decide +kernel

theorem rowCheck17599 : row17599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17599 := by decide +kernel

theorem rowEval17599 (x : Key → ℝ) : Integer.Sparse.eval row17599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17599, Integer.Sparse.eval_collectBalanced, rawRowCheck17599]

theorem rawRowCheck17600 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form18 = rawRow17600 := by decide +kernel

theorem rowCheck17600 : row17600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17600 := by decide +kernel

theorem rowEval17600 (x : Key → ℝ) : Integer.Sparse.eval row17600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17600, Integer.Sparse.eval_collectBalanced, rawRowCheck17600]

theorem rawRowCheck17601 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form19 = rawRow17601 := by decide +kernel

theorem rowCheck17601 : row17601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17601 := by decide +kernel

theorem rowEval17601 (x : Key → ℝ) : Integer.Sparse.eval row17601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17601, Integer.Sparse.eval_collectBalanced, rawRowCheck17601]

theorem rawRowCheck17602 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form19 = rawRow17602 := by decide +kernel

theorem rowCheck17602 : row17602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17602 := by decide +kernel

theorem rowEval17602 (x : Key → ℝ) : Integer.Sparse.eval row17602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17602, Integer.Sparse.eval_collectBalanced, rawRowCheck17602]

theorem rawRowCheck17603 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form19 = rawRow17603 := by decide +kernel

theorem rowCheck17603 : row17603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17603 := by decide +kernel

theorem rowEval17603 (x : Key → ℝ) : Integer.Sparse.eval row17603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17603, Integer.Sparse.eval_collectBalanced, rawRowCheck17603]

theorem rawRowCheck17604 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form19 = rawRow17604 := by decide +kernel

theorem rowCheck17604 : row17604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17604 := by decide +kernel

theorem rowEval17604 (x : Key → ℝ) : Integer.Sparse.eval row17604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17604, Integer.Sparse.eval_collectBalanced, rawRowCheck17604]

theorem rawRowCheck17605 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form19 = rawRow17605 := by decide +kernel

theorem rowCheck17605 : row17605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17605 := by decide +kernel

theorem rowEval17605 (x : Key → ℝ) : Integer.Sparse.eval row17605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17605, Integer.Sparse.eval_collectBalanced, rawRowCheck17605]

theorem rawRowCheck17606 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form19 = rawRow17606 := by decide +kernel

theorem rowCheck17606 : row17606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17606 := by decide +kernel

theorem rowEval17606 (x : Key → ℝ) : Integer.Sparse.eval row17606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17606, Integer.Sparse.eval_collectBalanced, rawRowCheck17606]

theorem rawRowCheck17607 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form19 = rawRow17607 := by decide +kernel

theorem rowCheck17607 : row17607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17607 := by decide +kernel

theorem rowEval17607 (x : Key → ℝ) : Integer.Sparse.eval row17607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17607, Integer.Sparse.eval_collectBalanced, rawRowCheck17607]

theorem rawRowCheck17608 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form19 = rawRow17608 := by decide +kernel

theorem rowCheck17608 : row17608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17608 := by decide +kernel

theorem rowEval17608 (x : Key → ℝ) : Integer.Sparse.eval row17608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17608, Integer.Sparse.eval_collectBalanced, rawRowCheck17608]

theorem rawRowCheck17609 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form19 = rawRow17609 := by decide +kernel

theorem rowCheck17609 : row17609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17609 := by decide +kernel

theorem rowEval17609 (x : Key → ℝ) : Integer.Sparse.eval row17609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17609, Integer.Sparse.eval_collectBalanced, rawRowCheck17609]

theorem rawRowCheck17610 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form19 = rawRow17610 := by decide +kernel

theorem rowCheck17610 : row17610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17610 := by decide +kernel

theorem rowEval17610 (x : Key → ℝ) : Integer.Sparse.eval row17610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17610, Integer.Sparse.eval_collectBalanced, rawRowCheck17610]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck19_0 : entry19_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_0 k)) := by decide +kernel

theorem rowsSound19_0 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17411 x
  · exact rowEval17412 x
  · exact rowEval17413 x
  · exact rowEval17414 x
  · exact rowEval17415 x
  · exact rowEval17416 x
  · exact rowEval17417 x
  · exact rowEval17418 x
  · exact rowEval17419 x
  · exact rowEval17420 x

theorem entryEval19_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_0 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck19_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_0]

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval17421 x
  · exact rowEval17422 x
  · exact rowEval17423 x
  · exact rowEval17424 x
  · exact rowEval17425 x
  · exact rowEval17426 x
  · exact rowEval17427 x
  · exact rowEval17428 x
  · exact rowEval17429 x
  · exact rowEval17430 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

theorem entryCheck19_2 : entry19_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_2 k)) := by decide +kernel

theorem rowsSound19_2 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval17431 x
  · exact rowEval17432 x
  · exact rowEval17433 x
  · exact rowEval17434 x
  · exact rowEval17435 x
  · exact rowEval17436 x
  · exact rowEval17437 x
  · exact rowEval17438 x
  · exact rowEval17439 x
  · exact rowEval17440 x

theorem entryEval19_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_2 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck19_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_2]

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval17441 x
  · exact rowEval17442 x
  · exact rowEval17443 x
  · exact rowEval17444 x
  · exact rowEval17445 x
  · exact rowEval17446 x
  · exact rowEval17447 x
  · exact rowEval17448 x
  · exact rowEval17449 x
  · exact rowEval17450 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17451 x
  · exact rowEval17452 x
  · exact rowEval17453 x
  · exact rowEval17454 x
  · exact rowEval17455 x
  · exact rowEval17456 x
  · exact rowEval17457 x
  · exact rowEval17458 x
  · exact rowEval17459 x
  · exact rowEval17460 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

theorem entryCheck19_5 : entry19_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_5 k)) := by decide +kernel

theorem rowsSound19_5 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17461 x
  · exact rowEval17462 x
  · exact rowEval17463 x
  · exact rowEval17464 x
  · exact rowEval17465 x
  · exact rowEval17466 x
  · exact rowEval17467 x
  · exact rowEval17468 x
  · exact rowEval17469 x
  · exact rowEval17470 x

theorem entryEval19_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_5 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck19_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_5]

theorem entryCheck19_6 : entry19_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_6 k)) := by decide +kernel

theorem rowsSound19_6 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval17471 x
  · exact rowEval17472 x
  · exact rowEval17473 x
  · exact rowEval17474 x
  · exact rowEval17475 x
  · exact rowEval17476 x
  · exact rowEval17477 x
  · exact rowEval17478 x
  · exact rowEval17479 x
  · exact rowEval17480 x

theorem entryEval19_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_6 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck19_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_6]

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval17481 x
  · exact rowEval17482 x
  · exact rowEval17483 x
  · exact rowEval17484 x
  · exact rowEval17485 x
  · exact rowEval17486 x
  · exact rowEval17487 x
  · exact rowEval17488 x
  · exact rowEval17489 x
  · exact rowEval17490 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval17491 x
  · exact rowEval17492 x
  · exact rowEval17493 x
  · exact rowEval17494 x
  · exact rowEval17495 x
  · exact rowEval17496 x
  · exact rowEval17497 x
  · exact rowEval17498 x
  · exact rowEval17499 x
  · exact rowEval17500 x

theorem entryEval19_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

theorem entryCheck19_9 : entry19_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_9 k)) := by decide +kernel

theorem rowsSound19_9 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17501 x
  · exact rowEval17502 x
  · exact rowEval17503 x
  · exact rowEval17504 x
  · exact rowEval17505 x
  · exact rowEval17506 x
  · exact rowEval17507 x
  · exact rowEval17508 x
  · exact rowEval17509 x
  · exact rowEval17510 x

theorem entryEval19_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_9 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck19_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_9]

theorem entryCheck19_10 : entry19_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_10 k)) := by decide +kernel

theorem rowsSound19_10 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval17511 x
  · exact rowEval17512 x
  · exact rowEval17513 x
  · exact rowEval17514 x
  · exact rowEval17515 x
  · exact rowEval17516 x
  · exact rowEval17517 x
  · exact rowEval17518 x
  · exact rowEval17519 x
  · exact rowEval17520 x

theorem entryEval19_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_10 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck19_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_10]

theorem entryCheck19_11 : entry19_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_11 k)) := by decide +kernel

theorem rowsSound19_11 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval17521 x
  · exact rowEval17522 x
  · exact rowEval17523 x
  · exact rowEval17524 x
  · exact rowEval17525 x
  · exact rowEval17526 x
  · exact rowEval17527 x
  · exact rowEval17528 x
  · exact rowEval17529 x
  · exact rowEval17530 x

theorem entryEval19_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_11 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck19_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_11]

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

theorem rowsSound19_12 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval17531 x
  · exact rowEval17532 x
  · exact rowEval17533 x
  · exact rowEval17534 x
  · exact rowEval17535 x
  · exact rowEval17536 x
  · exact rowEval17537 x
  · exact rowEval17538 x
  · exact rowEval17539 x
  · exact rowEval17540 x

theorem entryEval19_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_12 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck19_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_12]

theorem entryCheck19_13 : entry19_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_13 k)) := by decide +kernel

theorem rowsSound19_13 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval17541 x
  · exact rowEval17542 x
  · exact rowEval17543 x
  · exact rowEval17544 x
  · exact rowEval17545 x
  · exact rowEval17546 x
  · exact rowEval17547 x
  · exact rowEval17548 x
  · exact rowEval17549 x
  · exact rowEval17550 x

theorem entryEval19_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_13 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck19_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_13]

theorem entryCheck19_14 : entry19_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_14 k)) := by decide +kernel

theorem rowsSound19_14 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval17551 x
  · exact rowEval17552 x
  · exact rowEval17553 x
  · exact rowEval17554 x
  · exact rowEval17555 x
  · exact rowEval17556 x
  · exact rowEval17557 x
  · exact rowEval17558 x
  · exact rowEval17559 x
  · exact rowEval17560 x

theorem entryEval19_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_14 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck19_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_14]

theorem entryCheck19_15 : entry19_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_15 k)) := by decide +kernel

theorem rowsSound19_15 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form15) x := by
  fin_cases k
  · exact rowEval17561 x
  · exact rowEval17562 x
  · exact rowEval17563 x
  · exact rowEval17564 x
  · exact rowEval17565 x
  · exact rowEval17566 x
  · exact rowEval17567 x
  · exact rowEval17568 x
  · exact rowEval17569 x
  · exact rowEval17570 x

theorem entryEval19_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_15 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form15 B := by
  rw [entryCheck19_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_15]

theorem entryCheck19_16 : entry19_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_16 k)) := by decide +kernel

theorem rowsSound19_16 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form16) x := by
  fin_cases k
  · exact rowEval17571 x
  · exact rowEval17572 x
  · exact rowEval17573 x
  · exact rowEval17574 x
  · exact rowEval17575 x
  · exact rowEval17576 x
  · exact rowEval17577 x
  · exact rowEval17578 x
  · exact rowEval17579 x
  · exact rowEval17580 x

theorem entryEval19_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_16 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form16 B := by
  rw [entryCheck19_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_16]

theorem entryCheck19_17 : entry19_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_17 k)) := by decide +kernel

theorem rowsSound19_17 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval17581 x
  · exact rowEval17582 x
  · exact rowEval17583 x
  · exact rowEval17584 x
  · exact rowEval17585 x
  · exact rowEval17586 x
  · exact rowEval17587 x
  · exact rowEval17588 x
  · exact rowEval17589 x
  · exact rowEval17590 x

theorem entryEval19_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_17 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck19_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_17]

theorem entryCheck19_18 : entry19_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_18 k)) := by decide +kernel

theorem rowsSound19_18 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form18) x := by
  fin_cases k
  · exact rowEval17591 x
  · exact rowEval17592 x
  · exact rowEval17593 x
  · exact rowEval17594 x
  · exact rowEval17595 x
  · exact rowEval17596 x
  · exact rowEval17597 x
  · exact rowEval17598 x
  · exact rowEval17599 x
  · exact rowEval17600 x

theorem entryEval19_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_18 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form18 B := by
  rw [entryCheck19_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_18]

theorem entryCheck19_19 : entry19_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_19 k)) := by decide +kernel

theorem rowsSound19_19 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form19) x := by
  fin_cases k
  · exact rowEval17601 x
  · exact rowEval17602 x
  · exact rowEval17603 x
  · exact rowEval17604 x
  · exact rowEval17605 x
  · exact rowEval17606 x
  · exact rowEval17607 x
  · exact rowEval17608 x
  · exact rowEval17609 x
  · exact rowEval17610 x

theorem entryEval19_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_19 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form19 B := by
  rw [entryCheck19_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_19]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17953 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form19 = rawRow17953 := by decide +kernel

theorem rowCheck17953 : row17953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17953 := by decide +kernel

theorem rowEval17953 (x : Key → ℝ) : Integer.Sparse.eval row17953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17953, Integer.Sparse.eval_collectBalanced, rawRowCheck17953]

theorem rawRowCheck17954 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form19 = rawRow17954 := by decide +kernel

theorem rowCheck17954 : row17954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17954 := by decide +kernel

theorem rowEval17954 (x : Key → ℝ) : Integer.Sparse.eval row17954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17954, Integer.Sparse.eval_collectBalanced, rawRowCheck17954]

theorem rawRowCheck17955 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form19 = rawRow17955 := by decide +kernel

theorem rowCheck17955 : row17955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17955 := by decide +kernel

theorem rowEval17955 (x : Key → ℝ) : Integer.Sparse.eval row17955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17955, Integer.Sparse.eval_collectBalanced, rawRowCheck17955]

theorem rawRowCheck17956 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form19 = rawRow17956 := by decide +kernel

theorem rowCheck17956 : row17956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17956 := by decide +kernel

theorem rowEval17956 (x : Key → ℝ) : Integer.Sparse.eval row17956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17956, Integer.Sparse.eval_collectBalanced, rawRowCheck17956]

theorem rawRowCheck17957 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form19 = rawRow17957 := by decide +kernel

theorem rowCheck17957 : row17957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17957 := by decide +kernel

theorem rowEval17957 (x : Key → ℝ) : Integer.Sparse.eval row17957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17957, Integer.Sparse.eval_collectBalanced, rawRowCheck17957]

theorem rawRowCheck17958 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form19 = rawRow17958 := by decide +kernel

theorem rowCheck17958 : row17958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17958 := by decide +kernel

theorem rowEval17958 (x : Key → ℝ) : Integer.Sparse.eval row17958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17958, Integer.Sparse.eval_collectBalanced, rawRowCheck17958]

theorem rawRowCheck17959 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form19 = rawRow17959 := by decide +kernel

theorem rowCheck17959 : row17959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17959 := by decide +kernel

theorem rowEval17959 (x : Key → ℝ) : Integer.Sparse.eval row17959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17959, Integer.Sparse.eval_collectBalanced, rawRowCheck17959]

theorem rawRowCheck17960 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form19 = rawRow17960 := by decide +kernel

theorem rowCheck17960 : row17960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17960 := by decide +kernel

theorem rowEval17960 (x : Key → ℝ) : Integer.Sparse.eval row17960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17960, Integer.Sparse.eval_collectBalanced, rawRowCheck17960]

theorem rawRowCheck17961 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form19 = rawRow17961 := by decide +kernel

theorem rowCheck17961 : row17961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17961 := by decide +kernel

theorem rowEval17961 (x : Key → ℝ) : Integer.Sparse.eval row17961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17961, Integer.Sparse.eval_collectBalanced, rawRowCheck17961]

theorem rawRowCheck17962 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form19 = rawRow17962 := by decide +kernel

theorem rowCheck17962 : row17962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17962 := by decide +kernel

theorem rowEval17962 (x : Key → ℝ) : Integer.Sparse.eval row17962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17962, Integer.Sparse.eval_collectBalanced, rawRowCheck17962]

theorem rawRowCheck17963 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form19 = rawRow17963 := by decide +kernel

theorem rowCheck17963 : row17963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17963 := by decide +kernel

theorem rowEval17963 (x : Key → ℝ) : Integer.Sparse.eval row17963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17963, Integer.Sparse.eval_collectBalanced, rawRowCheck17963]

theorem rawRowCheck17964 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form19 = rawRow17964 := by decide +kernel

theorem rowCheck17964 : row17964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17964 := by decide +kernel

theorem rowEval17964 (x : Key → ℝ) : Integer.Sparse.eval row17964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17964, Integer.Sparse.eval_collectBalanced, rawRowCheck17964]

theorem rawRowCheck17965 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form19 = rawRow17965 := by decide +kernel

theorem rowCheck17965 : row17965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17965 := by decide +kernel

theorem rowEval17965 (x : Key → ℝ) : Integer.Sparse.eval row17965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17965, Integer.Sparse.eval_collectBalanced, rawRowCheck17965]

theorem rawRowCheck17966 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form19 = rawRow17966 := by decide +kernel

theorem rowCheck17966 : row17966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17966 := by decide +kernel

theorem rowEval17966 (x : Key → ℝ) : Integer.Sparse.eval row17966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17966, Integer.Sparse.eval_collectBalanced, rawRowCheck17966]

theorem rawRowCheck17967 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form19 = rawRow17967 := by decide +kernel

theorem rowCheck17967 : row17967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17967 := by decide +kernel

theorem rowEval17967 (x : Key → ℝ) : Integer.Sparse.eval row17967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17967, Integer.Sparse.eval_collectBalanced, rawRowCheck17967]

theorem rawRowCheck17968 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form19 = rawRow17968 := by decide +kernel

theorem rowCheck17968 : row17968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17968 := by decide +kernel

theorem rowEval17968 (x : Key → ℝ) : Integer.Sparse.eval row17968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17968, Integer.Sparse.eval_collectBalanced, rawRowCheck17968]

theorem rawRowCheck17969 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form19 = rawRow17969 := by decide +kernel

theorem rowCheck17969 : row17969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17969 := by decide +kernel

theorem rowEval17969 (x : Key → ℝ) : Integer.Sparse.eval row17969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17969, Integer.Sparse.eval_collectBalanced, rawRowCheck17969]

theorem rawRowCheck17970 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form19 = rawRow17970 := by decide +kernel

theorem rowCheck17970 : row17970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17970 := by decide +kernel

theorem rowEval17970 (x : Key → ℝ) : Integer.Sparse.eval row17970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17970, Integer.Sparse.eval_collectBalanced, rawRowCheck17970]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck20_19 : entry20_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_19 k)) := by decide +kernel

theorem rowsSound20_19 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form19) x := by
  fin_cases k
  · exact rowEval17953 x
  · exact rowEval17954 x
  · exact rowEval17955 x
  · exact rowEval17956 x
  · exact rowEval17957 x
  · exact rowEval17958 x
  · exact rowEval17959 x
  · exact rowEval17960 x
  · exact rowEval17961 x
  · exact rowEval17962 x
  · exact rowEval17963 x
  · exact rowEval17964 x
  · exact rowEval17965 x
  · exact rowEval17966 x
  · exact rowEval17967 x
  · exact rowEval17968 x
  · exact rowEval17969 x
  · exact rowEval17970 x

theorem entryEval20_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_19 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form19 B := by
  rw [entryCheck20_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_19]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18369 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form19 = rawRow18369 := by decide +kernel

theorem rowCheck18369 : row18369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18369 := by decide +kernel

theorem rowEval18369 (x : Key → ℝ) : Integer.Sparse.eval row18369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18369, Integer.Sparse.eval_collectBalanced, rawRowCheck18369]

theorem rawRowCheck18370 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form19 = rawRow18370 := by decide +kernel

theorem rowCheck18370 : row18370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18370 := by decide +kernel

theorem rowEval18370 (x : Key → ℝ) : Integer.Sparse.eval row18370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck18370, Integer.Sparse.eval_collectBalanced, rawRowCheck18370]

theorem rawRowCheck18371 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form19 = rawRow18371 := by decide +kernel

theorem rowCheck18371 : row18371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18371 := by decide +kernel

theorem rowEval18371 (x : Key → ℝ) : Integer.Sparse.eval row18371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18371, Integer.Sparse.eval_collectBalanced, rawRowCheck18371]

theorem rawRowCheck18372 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form19 = rawRow18372 := by decide +kernel

theorem rowCheck18372 : row18372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18372 := by decide +kernel

theorem rowEval18372 (x : Key → ℝ) : Integer.Sparse.eval row18372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18372, Integer.Sparse.eval_collectBalanced, rawRowCheck18372]

theorem rawRowCheck18373 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form19 = rawRow18373 := by decide +kernel

theorem rowCheck18373 : row18373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18373 := by decide +kernel

theorem rowEval18373 (x : Key → ℝ) : Integer.Sparse.eval row18373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck18373, Integer.Sparse.eval_collectBalanced, rawRowCheck18373]

theorem rawRowCheck18374 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form19 = rawRow18374 := by decide +kernel

theorem rowCheck18374 : row18374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18374 := by decide +kernel

theorem rowEval18374 (x : Key → ℝ) : Integer.Sparse.eval row18374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18374, Integer.Sparse.eval_collectBalanced, rawRowCheck18374]

theorem rawRowCheck18375 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form19 = rawRow18375 := by decide +kernel

theorem rowCheck18375 : row18375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18375 := by decide +kernel

theorem rowEval18375 (x : Key → ℝ) : Integer.Sparse.eval row18375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18375, Integer.Sparse.eval_collectBalanced, rawRowCheck18375]

theorem rawRowCheck18376 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form19 = rawRow18376 := by decide +kernel

theorem rowCheck18376 : row18376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18376 := by decide +kernel

theorem rowEval18376 (x : Key → ℝ) : Integer.Sparse.eval row18376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18376, Integer.Sparse.eval_collectBalanced, rawRowCheck18376]

theorem rawRowCheck18377 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form19 = rawRow18377 := by decide +kernel

theorem rowCheck18377 : row18377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18377 := by decide +kernel

theorem rowEval18377 (x : Key → ℝ) : Integer.Sparse.eval row18377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18377, Integer.Sparse.eval_collectBalanced, rawRowCheck18377]

theorem rawRowCheck18378 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form19 = rawRow18378 := by decide +kernel

theorem rowCheck18378 : row18378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18378 := by decide +kernel

theorem rowEval18378 (x : Key → ℝ) : Integer.Sparse.eval row18378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck18378, Integer.Sparse.eval_collectBalanced, rawRowCheck18378]

theorem rawRowCheck18379 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form19 = rawRow18379 := by decide +kernel

theorem rowCheck18379 : row18379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18379 := by decide +kernel

theorem rowEval18379 (x : Key → ℝ) : Integer.Sparse.eval row18379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18379, Integer.Sparse.eval_collectBalanced, rawRowCheck18379]

theorem rawRowCheck18380 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form19 = rawRow18380 := by decide +kernel

theorem rowCheck18380 : row18380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18380 := by decide +kernel

theorem rowEval18380 (x : Key → ℝ) : Integer.Sparse.eval row18380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18380, Integer.Sparse.eval_collectBalanced, rawRowCheck18380]

theorem rawRowCheck18381 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form19 = rawRow18381 := by decide +kernel

theorem rowCheck18381 : row18381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18381 := by decide +kernel

theorem rowEval18381 (x : Key → ℝ) : Integer.Sparse.eval row18381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18381, Integer.Sparse.eval_collectBalanced, rawRowCheck18381]

theorem rawRowCheck18382 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form19 = rawRow18382 := by decide +kernel

theorem rowCheck18382 : row18382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18382 := by decide +kernel

theorem rowEval18382 (x : Key → ℝ) : Integer.Sparse.eval row18382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18382, Integer.Sparse.eval_collectBalanced, rawRowCheck18382]

theorem rawRowCheck18383 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form19 = rawRow18383 := by decide +kernel

theorem rowCheck18383 : row18383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18383 := by decide +kernel

theorem rowEval18383 (x : Key → ℝ) : Integer.Sparse.eval row18383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18383, Integer.Sparse.eval_collectBalanced, rawRowCheck18383]

theorem rawRowCheck18384 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form19 = rawRow18384 := by decide +kernel

theorem rowCheck18384 : row18384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18384 := by decide +kernel

theorem rowEval18384 (x : Key → ℝ) : Integer.Sparse.eval row18384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18384, Integer.Sparse.eval_collectBalanced, rawRowCheck18384]

theorem rawRowCheck18385 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form19 = rawRow18385 := by decide +kernel

theorem rowCheck18385 : row18385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18385 := by decide +kernel

theorem rowEval18385 (x : Key → ℝ) : Integer.Sparse.eval row18385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck18385, Integer.Sparse.eval_collectBalanced, rawRowCheck18385]

theorem rawRowCheck18386 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form19 = rawRow18386 := by decide +kernel

theorem rowCheck18386 : row18386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18386 := by decide +kernel

theorem rowEval18386 (x : Key → ℝ) : Integer.Sparse.eval row18386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18386, Integer.Sparse.eval_collectBalanced, rawRowCheck18386]

theorem rawRowCheck18387 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form19 = rawRow18387 := by decide +kernel

theorem rowCheck18387 : row18387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18387 := by decide +kernel

theorem rowEval18387 (x : Key → ℝ) : Integer.Sparse.eval row18387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18387, Integer.Sparse.eval_collectBalanced, rawRowCheck18387]

theorem rawRowCheck18388 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form19 = rawRow18388 := by decide +kernel

theorem rowCheck18388 : row18388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18388 := by decide +kernel

theorem rowEval18388 (x : Key → ℝ) : Integer.Sparse.eval row18388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18388, Integer.Sparse.eval_collectBalanced, rawRowCheck18388]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck21_19 : entry21_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_19 k)) := by decide +kernel

theorem rowsSound21_19 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form19) x := by
  fin_cases k
  · exact rowEval18369 x
  · exact rowEval18370 x
  · exact rowEval18371 x
  · exact rowEval18372 x
  · exact rowEval18373 x
  · exact rowEval18374 x
  · exact rowEval18375 x
  · exact rowEval18376 x
  · exact rowEval18377 x
  · exact rowEval18378 x
  · exact rowEval18379 x
  · exact rowEval18380 x
  · exact rowEval18381 x
  · exact rowEval18382 x
  · exact rowEval18383 x
  · exact rowEval18384 x
  · exact rowEval18385 x
  · exact rowEval18386 x
  · exact rowEval18387 x
  · exact rowEval18388 x

theorem entryEval21_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_19 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form19 B := by
  rw [entryCheck21_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_19]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

theorem entryEvalRow19_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 19 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 19).mixedGram (GramFunctions.Block4.forms j) B := by
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

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e_oai
