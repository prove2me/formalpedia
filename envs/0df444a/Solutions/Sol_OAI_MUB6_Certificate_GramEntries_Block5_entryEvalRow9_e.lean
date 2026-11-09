-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:52:27.022722+00:00
-- url     : https://prove2.me/submissions/84e88550-dfbb-4736-9e1f-1ace4eaac36d

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

theorem rawRowCheck19328 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form4 = rawRow19328 := by decide +kernel

theorem rowCheck19328 : row19328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19328 := by decide +kernel

theorem rowEval19328 (x : Key → ℝ) : Integer.Sparse.eval row19328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19328, Integer.Sparse.eval_collectBalanced, rawRowCheck19328]

theorem rawRowCheck19329 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form4 = rawRow19329 := by decide +kernel

theorem rowCheck19329 : row19329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19329 := by decide +kernel

theorem rowEval19329 (x : Key → ℝ) : Integer.Sparse.eval row19329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19329, Integer.Sparse.eval_collectBalanced, rawRowCheck19329]

theorem rawRowCheck19330 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form4 = rawRow19330 := by decide +kernel

theorem rowCheck19330 : row19330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19330 := by decide +kernel

theorem rowEval19330 (x : Key → ℝ) : Integer.Sparse.eval row19330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19330, Integer.Sparse.eval_collectBalanced, rawRowCheck19330]

theorem rawRowCheck19331 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form4 = rawRow19331 := by decide +kernel

theorem rowCheck19331 : row19331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19331 := by decide +kernel

theorem rowEval19331 (x : Key → ℝ) : Integer.Sparse.eval row19331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19331, Integer.Sparse.eval_collectBalanced, rawRowCheck19331]

theorem rawRowCheck19332 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form4 = rawRow19332 := by decide +kernel

theorem rowCheck19332 : row19332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19332 := by decide +kernel

theorem rowEval19332 (x : Key → ℝ) : Integer.Sparse.eval row19332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19332, Integer.Sparse.eval_collectBalanced, rawRowCheck19332]

theorem rawRowCheck19333 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form4 = rawRow19333 := by decide +kernel

theorem rowCheck19333 : row19333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19333 := by decide +kernel

theorem rowEval19333 (x : Key → ℝ) : Integer.Sparse.eval row19333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19333, Integer.Sparse.eval_collectBalanced, rawRowCheck19333]

theorem rawRowCheck19334 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19334 := by decide +kernel

theorem rowCheck19334 : row19334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19334 := by decide +kernel

theorem rowEval19334 (x : Key → ℝ) : Integer.Sparse.eval row19334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19334, Integer.Sparse.eval_collectBalanced, rawRowCheck19334]

theorem rawRowCheck19335 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19335 := by decide +kernel

theorem rowCheck19335 : row19335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19335 := by decide +kernel

theorem rowEval19335 (x : Key → ℝ) : Integer.Sparse.eval row19335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19335, Integer.Sparse.eval_collectBalanced, rawRowCheck19335]

theorem rawRowCheck19336 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19336 := by decide +kernel

theorem rowCheck19336 : row19336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19336 := by decide +kernel

theorem rowEval19336 (x : Key → ℝ) : Integer.Sparse.eval row19336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19336, Integer.Sparse.eval_collectBalanced, rawRowCheck19336]

theorem rawRowCheck19337 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form5 = rawRow19337 := by decide +kernel

theorem rowCheck19337 : row19337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19337 := by decide +kernel

theorem rowEval19337 (x : Key → ℝ) : Integer.Sparse.eval row19337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19337, Integer.Sparse.eval_collectBalanced, rawRowCheck19337]

theorem rawRowCheck19338 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form5 = rawRow19338 := by decide +kernel

theorem rowCheck19338 : row19338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19338 := by decide +kernel

theorem rowEval19338 (x : Key → ℝ) : Integer.Sparse.eval row19338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19338, Integer.Sparse.eval_collectBalanced, rawRowCheck19338]

theorem rawRowCheck19339 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form5 = rawRow19339 := by decide +kernel

theorem rowCheck19339 : row19339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19339 := by decide +kernel

theorem rowEval19339 (x : Key → ℝ) : Integer.Sparse.eval row19339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19339, Integer.Sparse.eval_collectBalanced, rawRowCheck19339]

theorem rawRowCheck19340 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form5 = rawRow19340 := by decide +kernel

theorem rowCheck19340 : row19340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19340 := by decide +kernel

theorem rowEval19340 (x : Key → ℝ) : Integer.Sparse.eval row19340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19340, Integer.Sparse.eval_collectBalanced, rawRowCheck19340]

theorem rawRowCheck19341 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form5 = rawRow19341 := by decide +kernel

theorem rowCheck19341 : row19341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19341 := by decide +kernel

theorem rowEval19341 (x : Key → ℝ) : Integer.Sparse.eval row19341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19341, Integer.Sparse.eval_collectBalanced, rawRowCheck19341]

theorem rawRowCheck19342 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form5 = rawRow19342 := by decide +kernel

theorem rowCheck19342 : row19342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19342 := by decide +kernel

theorem rowEval19342 (x : Key → ℝ) : Integer.Sparse.eval row19342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19342, Integer.Sparse.eval_collectBalanced, rawRowCheck19342]

theorem rawRowCheck19343 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form5 = rawRow19343 := by decide +kernel

theorem rowCheck19343 : row19343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19343 := by decide +kernel

theorem rowEval19343 (x : Key → ℝ) : Integer.Sparse.eval row19343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19343, Integer.Sparse.eval_collectBalanced, rawRowCheck19343]

theorem rawRowCheck19344 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19344 := by decide +kernel

theorem rowCheck19344 : row19344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19344 := by decide +kernel

theorem rowEval19344 (x : Key → ℝ) : Integer.Sparse.eval row19344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19344, Integer.Sparse.eval_collectBalanced, rawRowCheck19344]

theorem rawRowCheck19345 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19345 := by decide +kernel

theorem rowCheck19345 : row19345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19345 := by decide +kernel

theorem rowEval19345 (x : Key → ℝ) : Integer.Sparse.eval row19345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19345, Integer.Sparse.eval_collectBalanced, rawRowCheck19345]

theorem rawRowCheck19346 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19346 := by decide +kernel

theorem rowCheck19346 : row19346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19346 := by decide +kernel

theorem rowEval19346 (x : Key → ℝ) : Integer.Sparse.eval row19346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19346, Integer.Sparse.eval_collectBalanced, rawRowCheck19346]

theorem rawRowCheck19347 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form6 = rawRow19347 := by decide +kernel

theorem rowCheck19347 : row19347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19347 := by decide +kernel

theorem rowEval19347 (x : Key → ℝ) : Integer.Sparse.eval row19347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19347, Integer.Sparse.eval_collectBalanced, rawRowCheck19347]

theorem rawRowCheck19348 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form6 = rawRow19348 := by decide +kernel

theorem rowCheck19348 : row19348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19348 := by decide +kernel

theorem rowEval19348 (x : Key → ℝ) : Integer.Sparse.eval row19348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19348, Integer.Sparse.eval_collectBalanced, rawRowCheck19348]

theorem rawRowCheck19349 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form6 = rawRow19349 := by decide +kernel

theorem rowCheck19349 : row19349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19349 := by decide +kernel

theorem rowEval19349 (x : Key → ℝ) : Integer.Sparse.eval row19349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19349, Integer.Sparse.eval_collectBalanced, rawRowCheck19349]

theorem rawRowCheck19350 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form6 = rawRow19350 := by decide +kernel

theorem rowCheck19350 : row19350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19350 := by decide +kernel

theorem rowEval19350 (x : Key → ℝ) : Integer.Sparse.eval row19350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19350, Integer.Sparse.eval_collectBalanced, rawRowCheck19350]

theorem rawRowCheck19351 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form6 = rawRow19351 := by decide +kernel

theorem rowCheck19351 : row19351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19351 := by decide +kernel

theorem rowEval19351 (x : Key → ℝ) : Integer.Sparse.eval row19351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19351, Integer.Sparse.eval_collectBalanced, rawRowCheck19351]

theorem rawRowCheck19352 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form6 = rawRow19352 := by decide +kernel

theorem rowCheck19352 : row19352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19352 := by decide +kernel

theorem rowEval19352 (x : Key → ℝ) : Integer.Sparse.eval row19352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19352, Integer.Sparse.eval_collectBalanced, rawRowCheck19352]

theorem rawRowCheck19353 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form6 = rawRow19353 := by decide +kernel

theorem rowCheck19353 : row19353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19353 := by decide +kernel

theorem rowEval19353 (x : Key → ℝ) : Integer.Sparse.eval row19353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19353, Integer.Sparse.eval_collectBalanced, rawRowCheck19353]

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

theorem rawRowCheck19364 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form8 = rawRow19364 := by decide +kernel

theorem rowCheck19364 : row19364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19364 := by decide +kernel

theorem rowEval19364 (x : Key → ℝ) : Integer.Sparse.eval row19364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19364, Integer.Sparse.eval_collectBalanced, rawRowCheck19364]

theorem rawRowCheck19365 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form8 = rawRow19365 := by decide +kernel

theorem rowCheck19365 : row19365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19365 := by decide +kernel

theorem rowEval19365 (x : Key → ℝ) : Integer.Sparse.eval row19365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19365, Integer.Sparse.eval_collectBalanced, rawRowCheck19365]

theorem rawRowCheck19366 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form8 = rawRow19366 := by decide +kernel

theorem rowCheck19366 : row19366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19366 := by decide +kernel

theorem rowEval19366 (x : Key → ℝ) : Integer.Sparse.eval row19366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19366, Integer.Sparse.eval_collectBalanced, rawRowCheck19366]

theorem rawRowCheck19367 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form8 = rawRow19367 := by decide +kernel

theorem rowCheck19367 : row19367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19367 := by decide +kernel

theorem rowEval19367 (x : Key → ℝ) : Integer.Sparse.eval row19367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19367, Integer.Sparse.eval_collectBalanced, rawRowCheck19367]

theorem rawRowCheck19368 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form8 = rawRow19368 := by decide +kernel

theorem rowCheck19368 : row19368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19368 := by decide +kernel

theorem rowEval19368 (x : Key → ℝ) : Integer.Sparse.eval row19368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19368, Integer.Sparse.eval_collectBalanced, rawRowCheck19368]

theorem rawRowCheck19369 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form8 = rawRow19369 := by decide +kernel

theorem rowCheck19369 : row19369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19369 := by decide +kernel

theorem rowEval19369 (x : Key → ℝ) : Integer.Sparse.eval row19369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19369, Integer.Sparse.eval_collectBalanced, rawRowCheck19369]

theorem rawRowCheck19370 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form8 = rawRow19370 := by decide +kernel

theorem rowCheck19370 : row19370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19370 := by decide +kernel

theorem rowEval19370 (x : Key → ℝ) : Integer.Sparse.eval row19370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19370, Integer.Sparse.eval_collectBalanced, rawRowCheck19370]

theorem rawRowCheck19371 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form8 = rawRow19371 := by decide +kernel

theorem rowCheck19371 : row19371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19371 := by decide +kernel

theorem rowEval19371 (x : Key → ℝ) : Integer.Sparse.eval row19371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19371, Integer.Sparse.eval_collectBalanced, rawRowCheck19371]

theorem rawRowCheck19372 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form8 = rawRow19372 := by decide +kernel

theorem rowCheck19372 : row19372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19372 := by decide +kernel

theorem rowEval19372 (x : Key → ℝ) : Integer.Sparse.eval row19372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19372, Integer.Sparse.eval_collectBalanced, rawRowCheck19372]

theorem rawRowCheck19373 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form8 = rawRow19373 := by decide +kernel

theorem rowCheck19373 : row19373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19373 := by decide +kernel

theorem rowEval19373 (x : Key → ℝ) : Integer.Sparse.eval row19373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19373, Integer.Sparse.eval_collectBalanced, rawRowCheck19373]

theorem rawRowCheck19374 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form9 = rawRow19374 := by decide +kernel

theorem rowCheck19374 : row19374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19374 := by decide +kernel

theorem rowEval19374 (x : Key → ℝ) : Integer.Sparse.eval row19374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19374, Integer.Sparse.eval_collectBalanced, rawRowCheck19374]

theorem rawRowCheck19375 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form9 = rawRow19375 := by decide +kernel

theorem rowCheck19375 : row19375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19375 := by decide +kernel

theorem rowEval19375 (x : Key → ℝ) : Integer.Sparse.eval row19375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19375, Integer.Sparse.eval_collectBalanced, rawRowCheck19375]

theorem rawRowCheck19376 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form9 = rawRow19376 := by decide +kernel

theorem rowCheck19376 : row19376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19376 := by decide +kernel

theorem rowEval19376 (x : Key → ℝ) : Integer.Sparse.eval row19376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19376, Integer.Sparse.eval_collectBalanced, rawRowCheck19376]

theorem rawRowCheck19377 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form9 = rawRow19377 := by decide +kernel

theorem rowCheck19377 : row19377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19377 := by decide +kernel

theorem rowEval19377 (x : Key → ℝ) : Integer.Sparse.eval row19377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19377, Integer.Sparse.eval_collectBalanced, rawRowCheck19377]

theorem rawRowCheck19378 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form9 = rawRow19378 := by decide +kernel

theorem rowCheck19378 : row19378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19378 := by decide +kernel

theorem rowEval19378 (x : Key → ℝ) : Integer.Sparse.eval row19378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19378, Integer.Sparse.eval_collectBalanced, rawRowCheck19378]

theorem rawRowCheck19379 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form9 = rawRow19379 := by decide +kernel

theorem rowCheck19379 : row19379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19379 := by decide +kernel

theorem rowEval19379 (x : Key → ℝ) : Integer.Sparse.eval row19379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19379, Integer.Sparse.eval_collectBalanced, rawRowCheck19379]

theorem rawRowCheck19380 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form9 = rawRow19380 := by decide +kernel

theorem rowCheck19380 : row19380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19380 := by decide +kernel

theorem rowEval19380 (x : Key → ℝ) : Integer.Sparse.eval row19380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19380, Integer.Sparse.eval_collectBalanced, rawRowCheck19380]

theorem rawRowCheck19381 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form9 = rawRow19381 := by decide +kernel

theorem rowCheck19381 : row19381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19381 := by decide +kernel

theorem rowEval19381 (x : Key → ℝ) : Integer.Sparse.eval row19381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19381, Integer.Sparse.eval_collectBalanced, rawRowCheck19381]

theorem rawRowCheck19382 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form9 = rawRow19382 := by decide +kernel

theorem rowCheck19382 : row19382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19382 := by decide +kernel

theorem rowEval19382 (x : Key → ℝ) : Integer.Sparse.eval row19382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19382, Integer.Sparse.eval_collectBalanced, rawRowCheck19382]

theorem rawRowCheck19383 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form9 = rawRow19383 := by decide +kernel

theorem rowCheck19383 : row19383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19383 := by decide +kernel

theorem rowEval19383 (x : Key → ℝ) : Integer.Sparse.eval row19383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck19383, Integer.Sparse.eval_collectBalanced, rawRowCheck19383]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

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

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck20144 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form9 = rawRow20144 := by decide +kernel

theorem rowCheck20144 : row20144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20144 := by decide +kernel

theorem rowEval20144 (x : Key → ℝ) : Integer.Sparse.eval row20144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20144, Integer.Sparse.eval_collectBalanced, rawRowCheck20144]

theorem rawRowCheck20145 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form9 = rawRow20145 := by decide +kernel

theorem rowCheck20145 : row20145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20145 := by decide +kernel

theorem rowEval20145 (x : Key → ℝ) : Integer.Sparse.eval row20145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20145, Integer.Sparse.eval_collectBalanced, rawRowCheck20145]

theorem rawRowCheck20146 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form9 = rawRow20146 := by decide +kernel

theorem rowCheck20146 : row20146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20146 := by decide +kernel

theorem rowEval20146 (x : Key → ℝ) : Integer.Sparse.eval row20146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20146, Integer.Sparse.eval_collectBalanced, rawRowCheck20146]

theorem rawRowCheck20147 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form9 = rawRow20147 := by decide +kernel

theorem rowCheck20147 : row20147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20147 := by decide +kernel

theorem rowEval20147 (x : Key → ℝ) : Integer.Sparse.eval row20147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20147, Integer.Sparse.eval_collectBalanced, rawRowCheck20147]

theorem rawRowCheck20148 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form9 = rawRow20148 := by decide +kernel

theorem rowCheck20148 : row20148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20148 := by decide +kernel

theorem rowEval20148 (x : Key → ℝ) : Integer.Sparse.eval row20148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20148, Integer.Sparse.eval_collectBalanced, rawRowCheck20148]

theorem rawRowCheck20149 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form9 = rawRow20149 := by decide +kernel

theorem rowCheck20149 : row20149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20149 := by decide +kernel

theorem rowEval20149 (x : Key → ℝ) : Integer.Sparse.eval row20149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20149, Integer.Sparse.eval_collectBalanced, rawRowCheck20149]

theorem rawRowCheck20150 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form9 = rawRow20150 := by decide +kernel

theorem rowCheck20150 : row20150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20150 := by decide +kernel

theorem rowEval20150 (x : Key → ℝ) : Integer.Sparse.eval row20150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20150, Integer.Sparse.eval_collectBalanced, rawRowCheck20150]

theorem rawRowCheck20151 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form9 = rawRow20151 := by decide +kernel

theorem rowCheck20151 : row20151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20151 := by decide +kernel

theorem rowEval20151 (x : Key → ℝ) : Integer.Sparse.eval row20151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20151, Integer.Sparse.eval_collectBalanced, rawRowCheck20151]

theorem rawRowCheck20152 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form9 = rawRow20152 := by decide +kernel

theorem rowCheck20152 : row20152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20152 := by decide +kernel

theorem rowEval20152 (x : Key → ℝ) : Integer.Sparse.eval row20152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20152, Integer.Sparse.eval_collectBalanced, rawRowCheck20152]

theorem rawRowCheck20153 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form9 = rawRow20153 := by decide +kernel

theorem rowCheck20153 : row20153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20153 := by decide +kernel

theorem rowEval20153 (x : Key → ℝ) : Integer.Sparse.eval row20153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20153, Integer.Sparse.eval_collectBalanced, rawRowCheck20153]

theorem rawRowCheck20154 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form9 = rawRow20154 := by decide +kernel

theorem rowCheck20154 : row20154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20154 := by decide +kernel

theorem rowEval20154 (x : Key → ℝ) : Integer.Sparse.eval row20154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20154, Integer.Sparse.eval_collectBalanced, rawRowCheck20154]

theorem rawRowCheck20155 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form9 = rawRow20155 := by decide +kernel

theorem rowCheck20155 : row20155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20155 := by decide +kernel

theorem rowEval20155 (x : Key → ℝ) : Integer.Sparse.eval row20155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20155, Integer.Sparse.eval_collectBalanced, rawRowCheck20155]

theorem rawRowCheck20156 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form9 = rawRow20156 := by decide +kernel

theorem rowCheck20156 : row20156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20156 := by decide +kernel

theorem rowEval20156 (x : Key → ℝ) : Integer.Sparse.eval row20156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20156, Integer.Sparse.eval_collectBalanced, rawRowCheck20156]

theorem rawRowCheck20157 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form9 = rawRow20157 := by decide +kernel

theorem rowCheck20157 : row20157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20157 := by decide +kernel

theorem rowEval20157 (x : Key → ℝ) : Integer.Sparse.eval row20157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20157, Integer.Sparse.eval_collectBalanced, rawRowCheck20157]

theorem rawRowCheck20158 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form9 = rawRow20158 := by decide +kernel

theorem rowCheck20158 : row20158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20158 := by decide +kernel

theorem rowEval20158 (x : Key → ℝ) : Integer.Sparse.eval row20158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20158, Integer.Sparse.eval_collectBalanced, rawRowCheck20158]

theorem rawRowCheck20159 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form9 = rawRow20159 := by decide +kernel

theorem rowCheck20159 : row20159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20159 := by decide +kernel

theorem rowEval20159 (x : Key → ℝ) : Integer.Sparse.eval row20159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20159, Integer.Sparse.eval_collectBalanced, rawRowCheck20159]

theorem rawRowCheck20160 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form9 = rawRow20160 := by decide +kernel

theorem rowCheck20160 : row20160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20160 := by decide +kernel

theorem rowEval20160 (x : Key → ℝ) : Integer.Sparse.eval row20160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20160, Integer.Sparse.eval_collectBalanced, rawRowCheck20160]

theorem rawRowCheck20161 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form9 = rawRow20161 := by decide +kernel

theorem rowCheck20161 : row20161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20161 := by decide +kernel

theorem rowEval20161 (x : Key → ℝ) : Integer.Sparse.eval row20161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20161, Integer.Sparse.eval_collectBalanced, rawRowCheck20161]

theorem rawRowCheck20162 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form9 = rawRow20162 := by decide +kernel

theorem rowCheck20162 : row20162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20162 := by decide +kernel

theorem rowEval20162 (x : Key → ℝ) : Integer.Sparse.eval row20162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20162, Integer.Sparse.eval_collectBalanced, rawRowCheck20162]

theorem rawRowCheck20163 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form9 = rawRow20163 := by decide +kernel

theorem rowCheck20163 : row20163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20163 := by decide +kernel

theorem rowEval20163 (x : Key → ℝ) : Integer.Sparse.eval row20163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20163, Integer.Sparse.eval_collectBalanced, rawRowCheck20163]

theorem rawRowCheck20164 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form9 = rawRow20164 := by decide +kernel

theorem rowCheck20164 : row20164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20164 := by decide +kernel

theorem rowEval20164 (x : Key → ℝ) : Integer.Sparse.eval row20164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20164, Integer.Sparse.eval_collectBalanced, rawRowCheck20164]

theorem rawRowCheck20165 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form9 = rawRow20165 := by decide +kernel

theorem rowCheck20165 : row20165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20165 := by decide +kernel

theorem rowEval20165 (x : Key → ℝ) : Integer.Sparse.eval row20165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20165, Integer.Sparse.eval_collectBalanced, rawRowCheck20165]

theorem rawRowCheck20166 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form9 = rawRow20166 := by decide +kernel

theorem rowCheck20166 : row20166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20166 := by decide +kernel

theorem rowEval20166 (x : Key → ℝ) : Integer.Sparse.eval row20166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20166, Integer.Sparse.eval_collectBalanced, rawRowCheck20166]

theorem rawRowCheck20167 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form9 = rawRow20167 := by decide +kernel

theorem rowCheck20167 : row20167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20167 := by decide +kernel

theorem rowEval20167 (x : Key → ℝ) : Integer.Sparse.eval row20167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20167, Integer.Sparse.eval_collectBalanced, rawRowCheck20167]

theorem rawRowCheck20168 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form9 = rawRow20168 := by decide +kernel

theorem rowCheck20168 : row20168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20168 := by decide +kernel

theorem rowEval20168 (x : Key → ℝ) : Integer.Sparse.eval row20168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20168, Integer.Sparse.eval_collectBalanced, rawRowCheck20168]

theorem rawRowCheck20169 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form9 = rawRow20169 := by decide +kernel

theorem rowCheck20169 : row20169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20169 := by decide +kernel

theorem rowEval20169 (x : Key → ℝ) : Integer.Sparse.eval row20169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20169, Integer.Sparse.eval_collectBalanced, rawRowCheck20169]

theorem rawRowCheck20170 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form9 = rawRow20170 := by decide +kernel

theorem rowCheck20170 : row20170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20170 := by decide +kernel

theorem rowEval20170 (x : Key → ℝ) : Integer.Sparse.eval row20170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20170, Integer.Sparse.eval_collectBalanced, rawRowCheck20170]

theorem rawRowCheck20171 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form9 = rawRow20171 := by decide +kernel

theorem rowCheck20171 : row20171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20171 := by decide +kernel

theorem rowEval20171 (x : Key → ℝ) : Integer.Sparse.eval row20171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20171, Integer.Sparse.eval_collectBalanced, rawRowCheck20171]

theorem rawRowCheck20172 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form9 = rawRow20172 := by decide +kernel

theorem rowCheck20172 : row20172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20172 := by decide +kernel

theorem rowEval20172 (x : Key → ℝ) : Integer.Sparse.eval row20172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20172, Integer.Sparse.eval_collectBalanced, rawRowCheck20172]

theorem rawRowCheck20173 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form9 = rawRow20173 := by decide +kernel

theorem rowCheck20173 : row20173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20173 := by decide +kernel

theorem rowEval20173 (x : Key → ℝ) : Integer.Sparse.eval row20173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20173, Integer.Sparse.eval_collectBalanced, rawRowCheck20173]

theorem rawRowCheck20174 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form9 = rawRow20174 := by decide +kernel

theorem rowCheck20174 : row20174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20174 := by decide +kernel

theorem rowEval20174 (x : Key → ℝ) : Integer.Sparse.eval row20174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20174, Integer.Sparse.eval_collectBalanced, rawRowCheck20174]

theorem rawRowCheck20175 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form9 = rawRow20175 := by decide +kernel

theorem rowCheck20175 : row20175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20175 := by decide +kernel

theorem rowEval20175 (x : Key → ℝ) : Integer.Sparse.eval row20175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20175, Integer.Sparse.eval_collectBalanced, rawRowCheck20175]

theorem rawRowCheck20176 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form9 = rawRow20176 := by decide +kernel

theorem rowCheck20176 : row20176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20176 := by decide +kernel

theorem rowEval20176 (x : Key → ℝ) : Integer.Sparse.eval row20176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20176, Integer.Sparse.eval_collectBalanced, rawRowCheck20176]

theorem rawRowCheck20177 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form9 = rawRow20177 := by decide +kernel

theorem rowCheck20177 : row20177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20177 := by decide +kernel

theorem rowEval20177 (x : Key → ℝ) : Integer.Sparse.eval row20177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20177, Integer.Sparse.eval_collectBalanced, rawRowCheck20177]

theorem rawRowCheck20178 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form9 = rawRow20178 := by decide +kernel

theorem rowCheck20178 : row20178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20178 := by decide +kernel

theorem rowEval20178 (x : Key → ℝ) : Integer.Sparse.eval row20178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20178, Integer.Sparse.eval_collectBalanced, rawRowCheck20178]

theorem rawRowCheck20179 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form9 = rawRow20179 := by decide +kernel

theorem rowCheck20179 : row20179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20179 := by decide +kernel

theorem rowEval20179 (x : Key → ℝ) : Integer.Sparse.eval row20179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20179, Integer.Sparse.eval_collectBalanced, rawRowCheck20179]

theorem rawRowCheck20180 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form9 = rawRow20180 := by decide +kernel

theorem rowCheck20180 : row20180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20180 := by decide +kernel

theorem rowEval20180 (x : Key → ℝ) : Integer.Sparse.eval row20180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20180, Integer.Sparse.eval_collectBalanced, rawRowCheck20180]

theorem rawRowCheck20181 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form9 = rawRow20181 := by decide +kernel

theorem rowCheck20181 : row20181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20181 := by decide +kernel

theorem rowEval20181 (x : Key → ℝ) : Integer.Sparse.eval row20181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20181, Integer.Sparse.eval_collectBalanced, rawRowCheck20181]

theorem rawRowCheck20182 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form9 = rawRow20182 := by decide +kernel

theorem rowCheck20182 : row20182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20182 := by decide +kernel

theorem rowEval20182 (x : Key → ℝ) : Integer.Sparse.eval row20182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20182, Integer.Sparse.eval_collectBalanced, rawRowCheck20182]

theorem rawRowCheck20183 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form9 = rawRow20183 := by decide +kernel

theorem rowCheck20183 : row20183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20183 := by decide +kernel

theorem rowEval20183 (x : Key → ℝ) : Integer.Sparse.eval row20183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20183, Integer.Sparse.eval_collectBalanced, rawRowCheck20183]

theorem rawRowCheck20184 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form9 = rawRow20184 := by decide +kernel

theorem rowCheck20184 : row20184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20184 := by decide +kernel

theorem rowEval20184 (x : Key → ℝ) : Integer.Sparse.eval row20184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20184, Integer.Sparse.eval_collectBalanced, rawRowCheck20184]

theorem rawRowCheck20185 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form9 = rawRow20185 := by decide +kernel

theorem rowCheck20185 : row20185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20185 := by decide +kernel

theorem rowEval20185 (x : Key → ℝ) : Integer.Sparse.eval row20185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20185, Integer.Sparse.eval_collectBalanced, rawRowCheck20185]

theorem rawRowCheck20186 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form9 = rawRow20186 := by decide +kernel

theorem rowCheck20186 : row20186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20186 := by decide +kernel

theorem rowEval20186 (x : Key → ℝ) : Integer.Sparse.eval row20186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20186, Integer.Sparse.eval_collectBalanced, rawRowCheck20186]

theorem rawRowCheck20187 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form9 = rawRow20187 := by decide +kernel

theorem rowCheck20187 : row20187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20187 := by decide +kernel

theorem rowEval20187 (x : Key → ℝ) : Integer.Sparse.eval row20187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20187, Integer.Sparse.eval_collectBalanced, rawRowCheck20187]

theorem rawRowCheck20188 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form9 = rawRow20188 := by decide +kernel

theorem rowCheck20188 : row20188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20188 := by decide +kernel

theorem rowEval20188 (x : Key → ℝ) : Integer.Sparse.eval row20188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20188, Integer.Sparse.eval_collectBalanced, rawRowCheck20188]

theorem rawRowCheck20189 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form9 = rawRow20189 := by decide +kernel

theorem rowCheck20189 : row20189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20189 := by decide +kernel

theorem rowEval20189 (x : Key → ℝ) : Integer.Sparse.eval row20189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20189, Integer.Sparse.eval_collectBalanced, rawRowCheck20189]

theorem rawRowCheck20190 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form9 = rawRow20190 := by decide +kernel

theorem rowCheck20190 : row20190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20190 := by decide +kernel

theorem rowEval20190 (x : Key → ℝ) : Integer.Sparse.eval row20190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20190, Integer.Sparse.eval_collectBalanced, rawRowCheck20190]

theorem rawRowCheck20191 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form9 = rawRow20191 := by decide +kernel

theorem rowCheck20191 : row20191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20191 := by decide +kernel

theorem rowEval20191 (x : Key → ℝ) : Integer.Sparse.eval row20191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20191, Integer.Sparse.eval_collectBalanced, rawRowCheck20191]

theorem rawRowCheck20192 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form9 = rawRow20192 := by decide +kernel

theorem rowCheck20192 : row20192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20192 := by decide +kernel

theorem rowEval20192 (x : Key → ℝ) : Integer.Sparse.eval row20192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20192, Integer.Sparse.eval_collectBalanced, rawRowCheck20192]

theorem rawRowCheck20193 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form9 = rawRow20193 := by decide +kernel

theorem rowCheck20193 : row20193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20193 := by decide +kernel

theorem rowEval20193 (x : Key → ℝ) : Integer.Sparse.eval row20193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20193, Integer.Sparse.eval_collectBalanced, rawRowCheck20193]

theorem rawRowCheck20194 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form9 = rawRow20194 := by decide +kernel

theorem rowCheck20194 : row20194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20194 := by decide +kernel

theorem rowEval20194 (x : Key → ℝ) : Integer.Sparse.eval row20194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20194, Integer.Sparse.eval_collectBalanced, rawRowCheck20194]

theorem rawRowCheck20195 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form9 = rawRow20195 := by decide +kernel

theorem rowCheck20195 : row20195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20195 := by decide +kernel

theorem rowEval20195 (x : Key → ℝ) : Integer.Sparse.eval row20195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20195, Integer.Sparse.eval_collectBalanced, rawRowCheck20195]

theorem rawRowCheck20196 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form9 = rawRow20196 := by decide +kernel

theorem rowCheck20196 : row20196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20196 := by decide +kernel

theorem rowEval20196 (x : Key → ℝ) : Integer.Sparse.eval row20196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20196, Integer.Sparse.eval_collectBalanced, rawRowCheck20196]

theorem rawRowCheck20197 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form9 = rawRow20197 := by decide +kernel

theorem rowCheck20197 : row20197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20197 := by decide +kernel

theorem rowEval20197 (x : Key → ℝ) : Integer.Sparse.eval row20197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20197, Integer.Sparse.eval_collectBalanced, rawRowCheck20197]

theorem rawRowCheck20198 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form9 = rawRow20198 := by decide +kernel

theorem rowCheck20198 : row20198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20198 := by decide +kernel

theorem rowEval20198 (x : Key → ℝ) : Integer.Sparse.eval row20198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20198, Integer.Sparse.eval_collectBalanced, rawRowCheck20198]

theorem rawRowCheck20199 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form9 = rawRow20199 := by decide +kernel

theorem rowCheck20199 : row20199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20199 := by decide +kernel

theorem rowEval20199 (x : Key → ℝ) : Integer.Sparse.eval row20199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20199, Integer.Sparse.eval_collectBalanced, rawRowCheck20199]

theorem rawRowCheck20200 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form9 = rawRow20200 := by decide +kernel

theorem rowCheck20200 : row20200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20200 := by decide +kernel

theorem rowEval20200 (x : Key → ℝ) : Integer.Sparse.eval row20200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20200, Integer.Sparse.eval_collectBalanced, rawRowCheck20200]

theorem rawRowCheck20201 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form9 = rawRow20201 := by decide +kernel

theorem rowCheck20201 : row20201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20201 := by decide +kernel

theorem rowEval20201 (x : Key → ℝ) : Integer.Sparse.eval row20201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20201, Integer.Sparse.eval_collectBalanced, rawRowCheck20201]

theorem rawRowCheck20202 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form9 = rawRow20202 := by decide +kernel

theorem rowCheck20202 : row20202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20202 := by decide +kernel

theorem rowEval20202 (x : Key → ℝ) : Integer.Sparse.eval row20202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20202, Integer.Sparse.eval_collectBalanced, rawRowCheck20202]

theorem rawRowCheck20203 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form9 = rawRow20203 := by decide +kernel

theorem rowCheck20203 : row20203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20203 := by decide +kernel

theorem rowEval20203 (x : Key → ℝ) : Integer.Sparse.eval row20203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20203, Integer.Sparse.eval_collectBalanced, rawRowCheck20203]

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

theorem entryCheck11_9 : entry11_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_9 k)) := by decide +kernel

theorem rowsSound11_9 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form9) x := by
  fin_cases k
  · exact rowEval20144 x
  · exact rowEval20145 x
  · exact rowEval20146 x
  · exact rowEval20147 x
  · exact rowEval20148 x
  · exact rowEval20149 x
  · exact rowEval20150 x
  · exact rowEval20151 x
  · exact rowEval20152 x
  · exact rowEval20153 x
  · exact rowEval20154 x
  · exact rowEval20155 x
  · exact rowEval20156 x
  · exact rowEval20157 x
  · exact rowEval20158 x
  · exact rowEval20159 x
  · exact rowEval20160 x
  · exact rowEval20161 x
  · exact rowEval20162 x
  · exact rowEval20163 x
  · exact rowEval20164 x
  · exact rowEval20165 x
  · exact rowEval20166 x
  · exact rowEval20167 x
  · exact rowEval20168 x
  · exact rowEval20169 x
  · exact rowEval20170 x
  · exact rowEval20171 x
  · exact rowEval20172 x
  · exact rowEval20173 x
  · exact rowEval20174 x
  · exact rowEval20175 x
  · exact rowEval20176 x
  · exact rowEval20177 x
  · exact rowEval20178 x
  · exact rowEval20179 x
  · exact rowEval20180 x
  · exact rowEval20181 x
  · exact rowEval20182 x
  · exact rowEval20183 x
  · exact rowEval20184 x
  · exact rowEval20185 x
  · exact rowEval20186 x
  · exact rowEval20187 x
  · exact rowEval20188 x
  · exact rowEval20189 x
  · exact rowEval20190 x
  · exact rowEval20191 x
  · exact rowEval20192 x
  · exact rowEval20193 x
  · exact rowEval20194 x
  · exact rowEval20195 x
  · exact rowEval20196 x
  · exact rowEval20197 x
  · exact rowEval20198 x
  · exact rowEval20199 x
  · exact rowEval20200 x
  · exact rowEval20201 x
  · exact rowEval20202 x
  · exact rowEval20203 x

theorem entryEval11_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_9 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form9 B := by
  rw [entryCheck11_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_9]

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

theorem rawRowCheck19284 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19284 := by decide +kernel

theorem rowCheck19284 : row19284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19284 := by decide +kernel

theorem rowEval19284 (x : Key → ℝ) : Integer.Sparse.eval row19284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19284, Integer.Sparse.eval_collectBalanced, rawRowCheck19284]

theorem rawRowCheck19285 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19285 := by decide +kernel

theorem rowCheck19285 : row19285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19285 := by decide +kernel

theorem rowEval19285 (x : Key → ℝ) : Integer.Sparse.eval row19285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19285, Integer.Sparse.eval_collectBalanced, rawRowCheck19285]

theorem rawRowCheck19286 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19286 := by decide +kernel

theorem rowCheck19286 : row19286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19286 := by decide +kernel

theorem rowEval19286 (x : Key → ℝ) : Integer.Sparse.eval row19286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19286, Integer.Sparse.eval_collectBalanced, rawRowCheck19286]

theorem rawRowCheck19287 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form0 = rawRow19287 := by decide +kernel

theorem rowCheck19287 : row19287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19287 := by decide +kernel

theorem rowEval19287 (x : Key → ℝ) : Integer.Sparse.eval row19287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19287, Integer.Sparse.eval_collectBalanced, rawRowCheck19287]

theorem rawRowCheck19288 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form0 = rawRow19288 := by decide +kernel

theorem rowCheck19288 : row19288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19288 := by decide +kernel

theorem rowEval19288 (x : Key → ℝ) : Integer.Sparse.eval row19288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19288, Integer.Sparse.eval_collectBalanced, rawRowCheck19288]

theorem rawRowCheck19289 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form0 = rawRow19289 := by decide +kernel

theorem rowCheck19289 : row19289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19289 := by decide +kernel

theorem rowEval19289 (x : Key → ℝ) : Integer.Sparse.eval row19289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19289, Integer.Sparse.eval_collectBalanced, rawRowCheck19289]

theorem rawRowCheck19290 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form0 = rawRow19290 := by decide +kernel

theorem rowCheck19290 : row19290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19290 := by decide +kernel

theorem rowEval19290 (x : Key → ℝ) : Integer.Sparse.eval row19290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19290, Integer.Sparse.eval_collectBalanced, rawRowCheck19290]

theorem rawRowCheck19291 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form0 = rawRow19291 := by decide +kernel

theorem rowCheck19291 : row19291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19291 := by decide +kernel

theorem rowEval19291 (x : Key → ℝ) : Integer.Sparse.eval row19291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19291, Integer.Sparse.eval_collectBalanced, rawRowCheck19291]

theorem rawRowCheck19292 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form0 = rawRow19292 := by decide +kernel

theorem rowCheck19292 : row19292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19292 := by decide +kernel

theorem rowEval19292 (x : Key → ℝ) : Integer.Sparse.eval row19292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19292, Integer.Sparse.eval_collectBalanced, rawRowCheck19292]

theorem rawRowCheck19293 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form0 = rawRow19293 := by decide +kernel

theorem rowCheck19293 : row19293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19293 := by decide +kernel

theorem rowEval19293 (x : Key → ℝ) : Integer.Sparse.eval row19293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19293, Integer.Sparse.eval_collectBalanced, rawRowCheck19293]

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

theorem rawRowCheck19304 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form2 = rawRow19304 := by decide +kernel

theorem rowCheck19304 : row19304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19304 := by decide +kernel

theorem rowEval19304 (x : Key → ℝ) : Integer.Sparse.eval row19304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19304, Integer.Sparse.eval_collectBalanced, rawRowCheck19304]

theorem rawRowCheck19305 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form2 = rawRow19305 := by decide +kernel

theorem rowCheck19305 : row19305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19305 := by decide +kernel

theorem rowEval19305 (x : Key → ℝ) : Integer.Sparse.eval row19305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19305, Integer.Sparse.eval_collectBalanced, rawRowCheck19305]

theorem rawRowCheck19306 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form2 = rawRow19306 := by decide +kernel

theorem rowCheck19306 : row19306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19306 := by decide +kernel

theorem rowEval19306 (x : Key → ℝ) : Integer.Sparse.eval row19306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19306, Integer.Sparse.eval_collectBalanced, rawRowCheck19306]

theorem rawRowCheck19307 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form2 = rawRow19307 := by decide +kernel

theorem rowCheck19307 : row19307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19307 := by decide +kernel

theorem rowEval19307 (x : Key → ℝ) : Integer.Sparse.eval row19307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19307, Integer.Sparse.eval_collectBalanced, rawRowCheck19307]

theorem rawRowCheck19308 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form2 = rawRow19308 := by decide +kernel

theorem rowCheck19308 : row19308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19308 := by decide +kernel

theorem rowEval19308 (x : Key → ℝ) : Integer.Sparse.eval row19308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19308, Integer.Sparse.eval_collectBalanced, rawRowCheck19308]

theorem rawRowCheck19309 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form2 = rawRow19309 := by decide +kernel

theorem rowCheck19309 : row19309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19309 := by decide +kernel

theorem rowEval19309 (x : Key → ℝ) : Integer.Sparse.eval row19309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19309, Integer.Sparse.eval_collectBalanced, rawRowCheck19309]

theorem rawRowCheck19310 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form2 = rawRow19310 := by decide +kernel

theorem rowCheck19310 : row19310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19310 := by decide +kernel

theorem rowEval19310 (x : Key → ℝ) : Integer.Sparse.eval row19310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19310, Integer.Sparse.eval_collectBalanced, rawRowCheck19310]

theorem rawRowCheck19311 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form2 = rawRow19311 := by decide +kernel

theorem rowCheck19311 : row19311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19311 := by decide +kernel

theorem rowEval19311 (x : Key → ℝ) : Integer.Sparse.eval row19311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19311, Integer.Sparse.eval_collectBalanced, rawRowCheck19311]

theorem rawRowCheck19312 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form2 = rawRow19312 := by decide +kernel

theorem rowCheck19312 : row19312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19312 := by decide +kernel

theorem rowEval19312 (x : Key → ℝ) : Integer.Sparse.eval row19312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19312, Integer.Sparse.eval_collectBalanced, rawRowCheck19312]

theorem rawRowCheck19313 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form2 = rawRow19313 := by decide +kernel

theorem rowCheck19313 : row19313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19313 := by decide +kernel

theorem rowEval19313 (x : Key → ℝ) : Integer.Sparse.eval row19313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19313, Integer.Sparse.eval_collectBalanced, rawRowCheck19313]

theorem rawRowCheck19314 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19314 := by decide +kernel

theorem rowCheck19314 : row19314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19314 := by decide +kernel

theorem rowEval19314 (x : Key → ℝ) : Integer.Sparse.eval row19314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19314, Integer.Sparse.eval_collectBalanced, rawRowCheck19314]

theorem rawRowCheck19315 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19315 := by decide +kernel

theorem rowCheck19315 : row19315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19315 := by decide +kernel

theorem rowEval19315 (x : Key → ℝ) : Integer.Sparse.eval row19315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19315, Integer.Sparse.eval_collectBalanced, rawRowCheck19315]

theorem rawRowCheck19316 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19316 := by decide +kernel

theorem rowCheck19316 : row19316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19316 := by decide +kernel

theorem rowEval19316 (x : Key → ℝ) : Integer.Sparse.eval row19316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19316, Integer.Sparse.eval_collectBalanced, rawRowCheck19316]

theorem rawRowCheck19317 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form3 = rawRow19317 := by decide +kernel

theorem rowCheck19317 : row19317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19317 := by decide +kernel

theorem rowEval19317 (x : Key → ℝ) : Integer.Sparse.eval row19317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19317, Integer.Sparse.eval_collectBalanced, rawRowCheck19317]

theorem rawRowCheck19318 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form3 = rawRow19318 := by decide +kernel

theorem rowCheck19318 : row19318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19318 := by decide +kernel

theorem rowEval19318 (x : Key → ℝ) : Integer.Sparse.eval row19318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19318, Integer.Sparse.eval_collectBalanced, rawRowCheck19318]

theorem rawRowCheck19319 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form3 = rawRow19319 := by decide +kernel

theorem rowCheck19319 : row19319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19319 := by decide +kernel

theorem rowEval19319 (x : Key → ℝ) : Integer.Sparse.eval row19319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19319, Integer.Sparse.eval_collectBalanced, rawRowCheck19319]

theorem rawRowCheck19320 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form3 = rawRow19320 := by decide +kernel

theorem rowCheck19320 : row19320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19320 := by decide +kernel

theorem rowEval19320 (x : Key → ℝ) : Integer.Sparse.eval row19320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19320, Integer.Sparse.eval_collectBalanced, rawRowCheck19320]

theorem rawRowCheck19321 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form3 = rawRow19321 := by decide +kernel

theorem rowCheck19321 : row19321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19321 := by decide +kernel

theorem rowEval19321 (x : Key → ℝ) : Integer.Sparse.eval row19321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19321, Integer.Sparse.eval_collectBalanced, rawRowCheck19321]

theorem rawRowCheck19322 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form3 = rawRow19322 := by decide +kernel

theorem rowCheck19322 : row19322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19322 := by decide +kernel

theorem rowEval19322 (x : Key → ℝ) : Integer.Sparse.eval row19322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19322, Integer.Sparse.eval_collectBalanced, rawRowCheck19322]

theorem rawRowCheck19323 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form3 = rawRow19323 := by decide +kernel

theorem rowCheck19323 : row19323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19323 := by decide +kernel

theorem rowEval19323 (x : Key → ℝ) : Integer.Sparse.eval row19323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19323, Integer.Sparse.eval_collectBalanced, rawRowCheck19323]

theorem rawRowCheck19324 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19324 := by decide +kernel

theorem rowCheck19324 : row19324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19324 := by decide +kernel

theorem rowEval19324 (x : Key → ℝ) : Integer.Sparse.eval row19324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19324, Integer.Sparse.eval_collectBalanced, rawRowCheck19324]

theorem rawRowCheck19325 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19325 := by decide +kernel

theorem rowCheck19325 : row19325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19325 := by decide +kernel

theorem rowEval19325 (x : Key → ℝ) : Integer.Sparse.eval row19325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19325, Integer.Sparse.eval_collectBalanced, rawRowCheck19325]

theorem rawRowCheck19326 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19326 := by decide +kernel

theorem rowCheck19326 : row19326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19326 := by decide +kernel

theorem rowEval19326 (x : Key → ℝ) : Integer.Sparse.eval row19326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19326, Integer.Sparse.eval_collectBalanced, rawRowCheck19326]

theorem rawRowCheck19327 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form4 = rawRow19327 := by decide +kernel

theorem rowCheck19327 : row19327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19327 := by decide +kernel

theorem rowEval19327 (x : Key → ℝ) : Integer.Sparse.eval row19327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19327, Integer.Sparse.eval_collectBalanced, rawRowCheck19327]

end MUB6.Certificate.GramRows

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

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19284 x
  · exact rowEval19285 x
  · exact rowEval19286 x
  · exact rowEval19287 x
  · exact rowEval19288 x
  · exact rowEval19289 x
  · exact rowEval19290 x
  · exact rowEval19291 x
  · exact rowEval19292 x
  · exact rowEval19293 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

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

theorem entryCheck9_2 : entry9_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_2 k)) := by decide +kernel

theorem rowsSound9_2 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval19304 x
  · exact rowEval19305 x
  · exact rowEval19306 x
  · exact rowEval19307 x
  · exact rowEval19308 x
  · exact rowEval19309 x
  · exact rowEval19310 x
  · exact rowEval19311 x
  · exact rowEval19312 x
  · exact rowEval19313 x

theorem entryEval9_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_2 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck9_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_2]

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19314 x
  · exact rowEval19315 x
  · exact rowEval19316 x
  · exact rowEval19317 x
  · exact rowEval19318 x
  · exact rowEval19319 x
  · exact rowEval19320 x
  · exact rowEval19321 x
  · exact rowEval19322 x
  · exact rowEval19323 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19324 x
  · exact rowEval19325 x
  · exact rowEval19326 x
  · exact rowEval19327 x
  · exact rowEval19328 x
  · exact rowEval19329 x
  · exact rowEval19330 x
  · exact rowEval19331 x
  · exact rowEval19332 x
  · exact rowEval19333 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19334 x
  · exact rowEval19335 x
  · exact rowEval19336 x
  · exact rowEval19337 x
  · exact rowEval19338 x
  · exact rowEval19339 x
  · exact rowEval19340 x
  · exact rowEval19341 x
  · exact rowEval19342 x
  · exact rowEval19343 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19344 x
  · exact rowEval19345 x
  · exact rowEval19346 x
  · exact rowEval19347 x
  · exact rowEval19348 x
  · exact rowEval19349 x
  · exact rowEval19350 x
  · exact rowEval19351 x
  · exact rowEval19352 x
  · exact rowEval19353 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

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

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval19364 x
  · exact rowEval19365 x
  · exact rowEval19366 x
  · exact rowEval19367 x
  · exact rowEval19368 x
  · exact rowEval19369 x
  · exact rowEval19370 x
  · exact rowEval19371 x
  · exact rowEval19372 x
  · exact rowEval19373 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

theorem entryCheck9_9 : entry9_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_9 k)) := by decide +kernel

theorem rowsSound9_9 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form9) x := by
  fin_cases k
  · exact rowEval19374 x
  · exact rowEval19375 x
  · exact rowEval19376 x
  · exact rowEval19377 x
  · exact rowEval19378 x
  · exact rowEval19379 x
  · exact rowEval19380 x
  · exact rowEval19381 x
  · exact rowEval19382 x
  · exact rowEval19383 x

theorem entryEval9_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_9 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form9 B := by
  rw [entryCheck9_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_9]

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

theorem entryEvalRow9_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 9 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 9).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval9_0 B hB
  · exact entryEval9_1 B hB
  · exact entryEval9_2 B hB
  · exact entryEval9_3 B hB
  · exact entryEval9_4 B hB
  · exact entryEval9_5 B hB
  · exact entryEval9_6 B hB
  · exact entryEval9_7 B hB
  · exact entryEval9_8 B hB
  · exact entryEval9_9 B hB
  · exact (entryEval10_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e_oai
