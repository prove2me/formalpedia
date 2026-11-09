-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:14:19.733315+00:00
-- url     : https://prove2.me/submissions/32e37bb1-ebeb-489b-9b6f-6086652c7661

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10589 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow10589 := by decide +kernel

theorem rowCheck10589 : row10589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10589 := by decide +kernel

theorem rowEval10589 (x : Key → ℝ) : Integer.Sparse.eval row10589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10589, Integer.Sparse.eval_collectBalanced, rawRowCheck10589]

theorem rawRowCheck10590 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow10590 := by decide +kernel

theorem rowCheck10590 : row10590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10590 := by decide +kernel

theorem rowEval10590 (x : Key → ℝ) : Integer.Sparse.eval row10590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10590, Integer.Sparse.eval_collectBalanced, rawRowCheck10590]

theorem rawRowCheck10591 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow10591 := by decide +kernel

theorem rowCheck10591 : row10591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10591 := by decide +kernel

theorem rowEval10591 (x : Key → ℝ) : Integer.Sparse.eval row10591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10591, Integer.Sparse.eval_collectBalanced, rawRowCheck10591]

theorem rawRowCheck10592 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow10592 := by decide +kernel

theorem rowCheck10592 : row10592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10592 := by decide +kernel

theorem rowEval10592 (x : Key → ℝ) : Integer.Sparse.eval row10592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10592, Integer.Sparse.eval_collectBalanced, rawRowCheck10592]

theorem rawRowCheck10593 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow10593 := by decide +kernel

theorem rowCheck10593 : row10593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10593 := by decide +kernel

theorem rowEval10593 (x : Key → ℝ) : Integer.Sparse.eval row10593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10593, Integer.Sparse.eval_collectBalanced, rawRowCheck10593]

theorem rawRowCheck10594 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow10594 := by decide +kernel

theorem rowCheck10594 : row10594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10594 := by decide +kernel

theorem rowEval10594 (x : Key → ℝ) : Integer.Sparse.eval row10594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10594, Integer.Sparse.eval_collectBalanced, rawRowCheck10594]

theorem rawRowCheck10595 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow10595 := by decide +kernel

theorem rowCheck10595 : row10595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10595 := by decide +kernel

theorem rowEval10595 (x : Key → ℝ) : Integer.Sparse.eval row10595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10595, Integer.Sparse.eval_collectBalanced, rawRowCheck10595]

theorem rawRowCheck10596 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow10596 := by decide +kernel

theorem rowCheck10596 : row10596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10596 := by decide +kernel

theorem rowEval10596 (x : Key → ℝ) : Integer.Sparse.eval row10596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10596, Integer.Sparse.eval_collectBalanced, rawRowCheck10596]

theorem rawRowCheck10597 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow10597 := by decide +kernel

theorem rowCheck10597 : row10597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10597 := by decide +kernel

theorem rowEval10597 (x : Key → ℝ) : Integer.Sparse.eval row10597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10597, Integer.Sparse.eval_collectBalanced, rawRowCheck10597]

theorem rawRowCheck10598 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow10598 := by decide +kernel

theorem rowCheck10598 : row10598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10598 := by decide +kernel

theorem rowEval10598 (x : Key → ℝ) : Integer.Sparse.eval row10598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10598, Integer.Sparse.eval_collectBalanced, rawRowCheck10598]

theorem rawRowCheck10599 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow10599 := by decide +kernel

theorem rowCheck10599 : row10599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10599 := by decide +kernel

theorem rowEval10599 (x : Key → ℝ) : Integer.Sparse.eval row10599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10599, Integer.Sparse.eval_collectBalanced, rawRowCheck10599]

theorem rawRowCheck10600 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow10600 := by decide +kernel

theorem rowCheck10600 : row10600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10600 := by decide +kernel

theorem rowEval10600 (x : Key → ℝ) : Integer.Sparse.eval row10600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10600, Integer.Sparse.eval_collectBalanced, rawRowCheck10600]

theorem rawRowCheck10601 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow10601 := by decide +kernel

theorem rowCheck10601 : row10601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10601 := by decide +kernel

theorem rowEval10601 (x : Key → ℝ) : Integer.Sparse.eval row10601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10601, Integer.Sparse.eval_collectBalanced, rawRowCheck10601]

theorem rawRowCheck10602 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow10602 := by decide +kernel

theorem rowCheck10602 : row10602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10602 := by decide +kernel

theorem rowEval10602 (x : Key → ℝ) : Integer.Sparse.eval row10602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10602, Integer.Sparse.eval_collectBalanced, rawRowCheck10602]

theorem rawRowCheck10603 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow10603 := by decide +kernel

theorem rowCheck10603 : row10603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10603 := by decide +kernel

theorem rowEval10603 (x : Key → ℝ) : Integer.Sparse.eval row10603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10603, Integer.Sparse.eval_collectBalanced, rawRowCheck10603]

theorem rawRowCheck10604 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow10604 := by decide +kernel

theorem rowCheck10604 : row10604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10604 := by decide +kernel

theorem rowEval10604 (x : Key → ℝ) : Integer.Sparse.eval row10604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10604, Integer.Sparse.eval_collectBalanced, rawRowCheck10604]

theorem rawRowCheck10605 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow10605 := by decide +kernel

theorem rowCheck10605 : row10605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10605 := by decide +kernel

theorem rowEval10605 (x : Key → ℝ) : Integer.Sparse.eval row10605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10605, Integer.Sparse.eval_collectBalanced, rawRowCheck10605]

theorem rawRowCheck10606 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow10606 := by decide +kernel

theorem rowCheck10606 : row10606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10606 := by decide +kernel

theorem rowEval10606 (x : Key → ℝ) : Integer.Sparse.eval row10606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10606, Integer.Sparse.eval_collectBalanced, rawRowCheck10606]

theorem rawRowCheck10607 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow10607 := by decide +kernel

theorem rowCheck10607 : row10607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10607 := by decide +kernel

theorem rowEval10607 (x : Key → ℝ) : Integer.Sparse.eval row10607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10607, Integer.Sparse.eval_collectBalanced, rawRowCheck10607]

theorem rawRowCheck10608 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow10608 := by decide +kernel

theorem rowCheck10608 : row10608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10608 := by decide +kernel

theorem rowEval10608 (x : Key → ℝ) : Integer.Sparse.eval row10608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10608, Integer.Sparse.eval_collectBalanced, rawRowCheck10608]

theorem rawRowCheck10609 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow10609 := by decide +kernel

theorem rowCheck10609 : row10609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10609 := by decide +kernel

theorem rowEval10609 (x : Key → ℝ) : Integer.Sparse.eval row10609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10609, Integer.Sparse.eval_collectBalanced, rawRowCheck10609]

theorem rawRowCheck10610 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow10610 := by decide +kernel

theorem rowCheck10610 : row10610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10610 := by decide +kernel

theorem rowEval10610 (x : Key → ℝ) : Integer.Sparse.eval row10610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10610, Integer.Sparse.eval_collectBalanced, rawRowCheck10610]

theorem rawRowCheck10611 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow10611 := by decide +kernel

theorem rowCheck10611 : row10611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10611 := by decide +kernel

theorem rowEval10611 (x : Key → ℝ) : Integer.Sparse.eval row10611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10611, Integer.Sparse.eval_collectBalanced, rawRowCheck10611]

theorem rawRowCheck10612 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow10612 := by decide +kernel

theorem rowCheck10612 : row10612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10612 := by decide +kernel

theorem rowEval10612 (x : Key → ℝ) : Integer.Sparse.eval row10612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10612, Integer.Sparse.eval_collectBalanced, rawRowCheck10612]

theorem rawRowCheck10613 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form4 = rawRow10613 := by decide +kernel

theorem rowCheck10613 : row10613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10613 := by decide +kernel

theorem rowEval10613 (x : Key → ℝ) : Integer.Sparse.eval row10613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10613, Integer.Sparse.eval_collectBalanced, rawRowCheck10613]

theorem rawRowCheck10614 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form5 = rawRow10614 := by decide +kernel

theorem rowCheck10614 : row10614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10614 := by decide +kernel

theorem rowEval10614 (x : Key → ℝ) : Integer.Sparse.eval row10614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10614, Integer.Sparse.eval_collectBalanced, rawRowCheck10614]

theorem rawRowCheck10615 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form5 = rawRow10615 := by decide +kernel

theorem rowCheck10615 : row10615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10615 := by decide +kernel

theorem rowEval10615 (x : Key → ℝ) : Integer.Sparse.eval row10615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10615, Integer.Sparse.eval_collectBalanced, rawRowCheck10615]

theorem rawRowCheck10616 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form5 = rawRow10616 := by decide +kernel

theorem rowCheck10616 : row10616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10616 := by decide +kernel

theorem rowEval10616 (x : Key → ℝ) : Integer.Sparse.eval row10616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10616, Integer.Sparse.eval_collectBalanced, rawRowCheck10616]

theorem rawRowCheck10617 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow10617 := by decide +kernel

theorem rowCheck10617 : row10617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10617 := by decide +kernel

theorem rowEval10617 (x : Key → ℝ) : Integer.Sparse.eval row10617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10617, Integer.Sparse.eval_collectBalanced, rawRowCheck10617]

theorem rawRowCheck10618 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form5 = rawRow10618 := by decide +kernel

theorem rowCheck10618 : row10618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10618 := by decide +kernel

theorem rowEval10618 (x : Key → ℝ) : Integer.Sparse.eval row10618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10618, Integer.Sparse.eval_collectBalanced, rawRowCheck10618]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10624 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow10624 := by decide +kernel

theorem rowCheck10624 : row10624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10624 := by decide +kernel

theorem rowEval10624 (x : Key → ℝ) : Integer.Sparse.eval row10624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck10624, Integer.Sparse.eval_collectBalanced, rawRowCheck10624]

theorem rawRowCheck10625 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow10625 := by decide +kernel

theorem rowCheck10625 : row10625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10625 := by decide +kernel

theorem rowEval10625 (x : Key → ℝ) : Integer.Sparse.eval row10625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10625, Integer.Sparse.eval_collectBalanced, rawRowCheck10625]

theorem rawRowCheck10626 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow10626 := by decide +kernel

theorem rowCheck10626 : row10626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10626 := by decide +kernel

theorem rowEval10626 (x : Key → ℝ) : Integer.Sparse.eval row10626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10626, Integer.Sparse.eval_collectBalanced, rawRowCheck10626]

theorem rawRowCheck10627 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow10627 := by decide +kernel

theorem rowCheck10627 : row10627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10627 := by decide +kernel

theorem rowEval10627 (x : Key → ℝ) : Integer.Sparse.eval row10627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10627, Integer.Sparse.eval_collectBalanced, rawRowCheck10627]

theorem rawRowCheck10628 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form7 = rawRow10628 := by decide +kernel

theorem rowCheck10628 : row10628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10628 := by decide +kernel

theorem rowEval10628 (x : Key → ℝ) : Integer.Sparse.eval row10628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10628, Integer.Sparse.eval_collectBalanced, rawRowCheck10628]

theorem rawRowCheck10629 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form8 = rawRow10629 := by decide +kernel

theorem rowCheck10629 : row10629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10629 := by decide +kernel

theorem rowEval10629 (x : Key → ℝ) : Integer.Sparse.eval row10629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck10629, Integer.Sparse.eval_collectBalanced, rawRowCheck10629]

theorem rawRowCheck10630 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form8 = rawRow10630 := by decide +kernel

theorem rowCheck10630 : row10630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10630 := by decide +kernel

theorem rowEval10630 (x : Key → ℝ) : Integer.Sparse.eval row10630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10630, Integer.Sparse.eval_collectBalanced, rawRowCheck10630]

theorem rawRowCheck10631 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form8 = rawRow10631 := by decide +kernel

theorem rowCheck10631 : row10631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10631 := by decide +kernel

theorem rowEval10631 (x : Key → ℝ) : Integer.Sparse.eval row10631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10631, Integer.Sparse.eval_collectBalanced, rawRowCheck10631]

theorem rawRowCheck10632 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow10632 := by decide +kernel

theorem rowCheck10632 : row10632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10632 := by decide +kernel

theorem rowEval10632 (x : Key → ℝ) : Integer.Sparse.eval row10632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10632, Integer.Sparse.eval_collectBalanced, rawRowCheck10632]

theorem rawRowCheck10633 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form8 = rawRow10633 := by decide +kernel

theorem rowCheck10633 : row10633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10633 := by decide +kernel

theorem rowEval10633 (x : Key → ℝ) : Integer.Sparse.eval row10633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10633, Integer.Sparse.eval_collectBalanced, rawRowCheck10633]

theorem rawRowCheck10634 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form9 = rawRow10634 := by decide +kernel

theorem rowCheck10634 : row10634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10634 := by decide +kernel

theorem rowEval10634 (x : Key → ℝ) : Integer.Sparse.eval row10634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck10634, Integer.Sparse.eval_collectBalanced, rawRowCheck10634]

theorem rawRowCheck10635 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form9 = rawRow10635 := by decide +kernel

theorem rowCheck10635 : row10635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10635 := by decide +kernel

theorem rowEval10635 (x : Key → ℝ) : Integer.Sparse.eval row10635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10635, Integer.Sparse.eval_collectBalanced, rawRowCheck10635]

theorem rawRowCheck10636 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form9 = rawRow10636 := by decide +kernel

theorem rowCheck10636 : row10636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10636 := by decide +kernel

theorem rowEval10636 (x : Key → ℝ) : Integer.Sparse.eval row10636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10636, Integer.Sparse.eval_collectBalanced, rawRowCheck10636]

theorem rawRowCheck10637 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow10637 := by decide +kernel

theorem rowCheck10637 : row10637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10637 := by decide +kernel

theorem rowEval10637 (x : Key → ℝ) : Integer.Sparse.eval row10637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10637, Integer.Sparse.eval_collectBalanced, rawRowCheck10637]

theorem rawRowCheck10638 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form9 = rawRow10638 := by decide +kernel

theorem rowCheck10638 : row10638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10638 := by decide +kernel

theorem rowEval10638 (x : Key → ℝ) : Integer.Sparse.eval row10638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10638, Integer.Sparse.eval_collectBalanced, rawRowCheck10638]

theorem rawRowCheck10639 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow10639 := by decide +kernel

theorem rowCheck10639 : row10639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10639 := by decide +kernel

theorem rowEval10639 (x : Key → ℝ) : Integer.Sparse.eval row10639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck10639, Integer.Sparse.eval_collectBalanced, rawRowCheck10639]

theorem rawRowCheck10640 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow10640 := by decide +kernel

theorem rowCheck10640 : row10640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10640 := by decide +kernel

theorem rowEval10640 (x : Key → ℝ) : Integer.Sparse.eval row10640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10640, Integer.Sparse.eval_collectBalanced, rawRowCheck10640]

theorem rawRowCheck10641 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow10641 := by decide +kernel

theorem rowCheck10641 : row10641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10641 := by decide +kernel

theorem rowEval10641 (x : Key → ℝ) : Integer.Sparse.eval row10641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10641, Integer.Sparse.eval_collectBalanced, rawRowCheck10641]

theorem rawRowCheck10642 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow10642 := by decide +kernel

theorem rowCheck10642 : row10642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10642 := by decide +kernel

theorem rowEval10642 (x : Key → ℝ) : Integer.Sparse.eval row10642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10642, Integer.Sparse.eval_collectBalanced, rawRowCheck10642]

theorem rawRowCheck10643 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form10 = rawRow10643 := by decide +kernel

theorem rowCheck10643 : row10643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10643 := by decide +kernel

theorem rowEval10643 (x : Key → ℝ) : Integer.Sparse.eval row10643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10643, Integer.Sparse.eval_collectBalanced, rawRowCheck10643]

theorem rawRowCheck10644 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow10644 := by decide +kernel

theorem rowCheck10644 : row10644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10644 := by decide +kernel

theorem rowEval10644 (x : Key → ℝ) : Integer.Sparse.eval row10644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck10644, Integer.Sparse.eval_collectBalanced, rawRowCheck10644]

theorem rawRowCheck10645 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow10645 := by decide +kernel

theorem rowCheck10645 : row10645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10645 := by decide +kernel

theorem rowEval10645 (x : Key → ℝ) : Integer.Sparse.eval row10645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10645, Integer.Sparse.eval_collectBalanced, rawRowCheck10645]

theorem rawRowCheck10646 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow10646 := by decide +kernel

theorem rowCheck10646 : row10646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10646 := by decide +kernel

theorem rowEval10646 (x : Key → ℝ) : Integer.Sparse.eval row10646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10646, Integer.Sparse.eval_collectBalanced, rawRowCheck10646]

theorem rawRowCheck10647 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow10647 := by decide +kernel

theorem rowCheck10647 : row10647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10647 := by decide +kernel

theorem rowEval10647 (x : Key → ℝ) : Integer.Sparse.eval row10647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10647, Integer.Sparse.eval_collectBalanced, rawRowCheck10647]

theorem rawRowCheck10648 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form11 = rawRow10648 := by decide +kernel

theorem rowCheck10648 : row10648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10648 := by decide +kernel

theorem rowEval10648 (x : Key → ℝ) : Integer.Sparse.eval row10648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10648, Integer.Sparse.eval_collectBalanced, rawRowCheck10648]

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

theorem rawRowCheck10654 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form13 = rawRow10654 := by decide +kernel

theorem rowCheck10654 : row10654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10654 := by decide +kernel

theorem rowEval10654 (x : Key → ℝ) : Integer.Sparse.eval row10654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck10654, Integer.Sparse.eval_collectBalanced, rawRowCheck10654]

theorem rawRowCheck10655 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form13 = rawRow10655 := by decide +kernel

theorem rowCheck10655 : row10655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10655 := by decide +kernel

theorem rowEval10655 (x : Key → ℝ) : Integer.Sparse.eval row10655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10655, Integer.Sparse.eval_collectBalanced, rawRowCheck10655]

theorem rawRowCheck10656 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form13 = rawRow10656 := by decide +kernel

theorem rowCheck10656 : row10656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10656 := by decide +kernel

theorem rowEval10656 (x : Key → ℝ) : Integer.Sparse.eval row10656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10656, Integer.Sparse.eval_collectBalanced, rawRowCheck10656]

theorem rawRowCheck10657 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow10657 := by decide +kernel

theorem rowCheck10657 : row10657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10657 := by decide +kernel

theorem rowEval10657 (x : Key → ℝ) : Integer.Sparse.eval row10657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10657, Integer.Sparse.eval_collectBalanced, rawRowCheck10657]

theorem rawRowCheck10658 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form13 = rawRow10658 := by decide +kernel

theorem rowCheck10658 : row10658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10658 := by decide +kernel

theorem rowEval10658 (x : Key → ℝ) : Integer.Sparse.eval row10658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10658, Integer.Sparse.eval_collectBalanced, rawRowCheck10658]

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

theorem rawRowCheck10664 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form15 = rawRow10664 := by decide +kernel

theorem rowCheck10664 : row10664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10664 := by decide +kernel

theorem rowEval10664 (x : Key → ℝ) : Integer.Sparse.eval row10664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form15) x := by
  rw [rowCheck10664, Integer.Sparse.eval_collectBalanced, rawRowCheck10664]

theorem rawRowCheck10665 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form15 = rawRow10665 := by decide +kernel

theorem rowCheck10665 : row10665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10665 := by decide +kernel

theorem rowEval10665 (x : Key → ℝ) : Integer.Sparse.eval row10665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10665, Integer.Sparse.eval_collectBalanced, rawRowCheck10665]

theorem rawRowCheck10666 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form15 = rawRow10666 := by decide +kernel

theorem rowCheck10666 : row10666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10666 := by decide +kernel

theorem rowEval10666 (x : Key → ℝ) : Integer.Sparse.eval row10666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10666, Integer.Sparse.eval_collectBalanced, rawRowCheck10666]

theorem rawRowCheck10667 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow10667 := by decide +kernel

theorem rowCheck10667 : row10667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10667 := by decide +kernel

theorem rowEval10667 (x : Key → ℝ) : Integer.Sparse.eval row10667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10667, Integer.Sparse.eval_collectBalanced, rawRowCheck10667]

theorem rawRowCheck10668 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form15 = rawRow10668 := by decide +kernel

theorem rowCheck10668 : row10668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10668 := by decide +kernel

theorem rowEval10668 (x : Key → ℝ) : Integer.Sparse.eval row10668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10668, Integer.Sparse.eval_collectBalanced, rawRowCheck10668]

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

theorem rawRowCheck10674 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form17 = rawRow10674 := by decide +kernel

theorem rowCheck10674 : row10674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10674 := by decide +kernel

theorem rowEval10674 (x : Key → ℝ) : Integer.Sparse.eval row10674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form17) x := by
  rw [rowCheck10674, Integer.Sparse.eval_collectBalanced, rawRowCheck10674]

theorem rawRowCheck10675 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form17 = rawRow10675 := by decide +kernel

theorem rowCheck10675 : row10675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10675 := by decide +kernel

theorem rowEval10675 (x : Key → ℝ) : Integer.Sparse.eval row10675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10675, Integer.Sparse.eval_collectBalanced, rawRowCheck10675]

theorem rawRowCheck10676 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form17 = rawRow10676 := by decide +kernel

theorem rowCheck10676 : row10676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10676 := by decide +kernel

theorem rowEval10676 (x : Key → ℝ) : Integer.Sparse.eval row10676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10676, Integer.Sparse.eval_collectBalanced, rawRowCheck10676]

theorem rawRowCheck10677 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form17 = rawRow10677 := by decide +kernel

theorem rowCheck10677 : row10677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10677 := by decide +kernel

theorem rowEval10677 (x : Key → ℝ) : Integer.Sparse.eval row10677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10677, Integer.Sparse.eval_collectBalanced, rawRowCheck10677]

theorem rawRowCheck10678 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form17 = rawRow10678 := by decide +kernel

theorem rowCheck10678 : row10678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10678 := by decide +kernel

theorem rowEval10678 (x : Key → ℝ) : Integer.Sparse.eval row10678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10678, Integer.Sparse.eval_collectBalanced, rawRowCheck10678]

theorem rawRowCheck10679 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form18 = rawRow10679 := by decide +kernel

theorem rowCheck10679 : row10679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10679 := by decide +kernel

theorem rowEval10679 (x : Key → ℝ) : Integer.Sparse.eval row10679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form18) x := by
  rw [rowCheck10679, Integer.Sparse.eval_collectBalanced, rawRowCheck10679]

theorem rawRowCheck10680 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form18 = rawRow10680 := by decide +kernel

theorem rowCheck10680 : row10680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10680 := by decide +kernel

theorem rowEval10680 (x : Key → ℝ) : Integer.Sparse.eval row10680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10680, Integer.Sparse.eval_collectBalanced, rawRowCheck10680]

theorem rawRowCheck10681 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form18 = rawRow10681 := by decide +kernel

theorem rowCheck10681 : row10681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10681 := by decide +kernel

theorem rowEval10681 (x : Key → ℝ) : Integer.Sparse.eval row10681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10681, Integer.Sparse.eval_collectBalanced, rawRowCheck10681]

theorem rawRowCheck10682 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form18 = rawRow10682 := by decide +kernel

theorem rowCheck10682 : row10682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10682 := by decide +kernel

theorem rowEval10682 (x : Key → ℝ) : Integer.Sparse.eval row10682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10682, Integer.Sparse.eval_collectBalanced, rawRowCheck10682]

theorem rawRowCheck10683 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form18 = rawRow10683 := by decide +kernel

theorem rowCheck10683 : row10683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10683 := by decide +kernel

theorem rowEval10683 (x : Key → ℝ) : Integer.Sparse.eval row10683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10683, Integer.Sparse.eval_collectBalanced, rawRowCheck10683]

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

theorem rawRowCheck10689 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form20 = rawRow10689 := by decide +kernel

theorem rowCheck10689 : row10689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10689 := by decide +kernel

theorem rowEval10689 (x : Key → ℝ) : Integer.Sparse.eval row10689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form20) x := by
  rw [rowCheck10689, Integer.Sparse.eval_collectBalanced, rawRowCheck10689]

theorem rawRowCheck10690 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form20 = rawRow10690 := by decide +kernel

theorem rowCheck10690 : row10690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10690 := by decide +kernel

theorem rowEval10690 (x : Key → ℝ) : Integer.Sparse.eval row10690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck10690, Integer.Sparse.eval_collectBalanced, rawRowCheck10690]

theorem rawRowCheck10691 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form20 = rawRow10691 := by decide +kernel

theorem rowCheck10691 : row10691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10691 := by decide +kernel

theorem rowEval10691 (x : Key → ℝ) : Integer.Sparse.eval row10691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck10691, Integer.Sparse.eval_collectBalanced, rawRowCheck10691]

theorem rawRowCheck10692 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form20 = rawRow10692 := by decide +kernel

theorem rowCheck10692 : row10692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10692 := by decide +kernel

theorem rowEval10692 (x : Key → ℝ) : Integer.Sparse.eval row10692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck10692, Integer.Sparse.eval_collectBalanced, rawRowCheck10692]

theorem rawRowCheck10693 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form20 = rawRow10693 := by decide +kernel

theorem rowCheck10693 : row10693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10693 := by decide +kernel

theorem rowEval10693 (x : Key → ℝ) : Integer.Sparse.eval row10693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck10693, Integer.Sparse.eval_collectBalanced, rawRowCheck10693]

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

theorem entryCheck20_0 : entry20_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_0 k)) := by decide +kernel

theorem rowsSound20_0 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval10589 x
  · exact rowEval10590 x
  · exact rowEval10591 x
  · exact rowEval10592 x
  · exact rowEval10593 x

theorem entryEval20_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_0 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck20_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_0]

theorem entryCheck20_1 : entry20_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_1 k)) := by decide +kernel

theorem rowsSound20_1 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval10594 x
  · exact rowEval10595 x
  · exact rowEval10596 x
  · exact rowEval10597 x
  · exact rowEval10598 x

theorem entryEval20_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_1 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck20_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_1]

theorem entryCheck20_2 : entry20_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_2 k)) := by decide +kernel

theorem rowsSound20_2 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval10599 x
  · exact rowEval10600 x
  · exact rowEval10601 x
  · exact rowEval10602 x
  · exact rowEval10603 x

theorem entryEval20_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_2 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck20_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_2]

theorem entryCheck20_3 : entry20_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_3 k)) := by decide +kernel

theorem rowsSound20_3 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval10604 x
  · exact rowEval10605 x
  · exact rowEval10606 x
  · exact rowEval10607 x
  · exact rowEval10608 x

theorem entryEval20_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_3 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck20_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_3]

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval10609 x
  · exact rowEval10610 x
  · exact rowEval10611 x
  · exact rowEval10612 x
  · exact rowEval10613 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

theorem entryCheck20_5 : entry20_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_5 k)) := by decide +kernel

theorem rowsSound20_5 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval10614 x
  · exact rowEval10615 x
  · exact rowEval10616 x
  · exact rowEval10617 x
  · exact rowEval10618 x

theorem entryEval20_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_5 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck20_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_5]

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

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval10624 x
  · exact rowEval10625 x
  · exact rowEval10626 x
  · exact rowEval10627 x
  · exact rowEval10628 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

theorem entryCheck20_8 : entry20_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_8 k)) := by decide +kernel

theorem rowsSound20_8 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval10629 x
  · exact rowEval10630 x
  · exact rowEval10631 x
  · exact rowEval10632 x
  · exact rowEval10633 x

theorem entryEval20_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_8 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck20_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_8]

theorem entryCheck20_9 : entry20_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_9 k)) := by decide +kernel

theorem rowsSound20_9 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval10634 x
  · exact rowEval10635 x
  · exact rowEval10636 x
  · exact rowEval10637 x
  · exact rowEval10638 x

theorem entryEval20_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_9 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck20_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_9]

theorem entryCheck20_10 : entry20_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_10 k)) := by decide +kernel

theorem rowsSound20_10 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval10639 x
  · exact rowEval10640 x
  · exact rowEval10641 x
  · exact rowEval10642 x
  · exact rowEval10643 x

theorem entryEval20_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_10 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck20_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_10]

theorem entryCheck20_11 : entry20_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_11 k)) := by decide +kernel

theorem rowsSound20_11 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval10644 x
  · exact rowEval10645 x
  · exact rowEval10646 x
  · exact rowEval10647 x
  · exact rowEval10648 x

theorem entryEval20_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_11 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck20_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_11]

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

theorem entryCheck20_13 : entry20_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_13 k)) := by decide +kernel

theorem rowsSound20_13 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval10654 x
  · exact rowEval10655 x
  · exact rowEval10656 x
  · exact rowEval10657 x
  · exact rowEval10658 x

theorem entryEval20_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_13 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck20_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_13]

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

theorem entryCheck20_15 : entry20_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_15 k)) := by decide +kernel

theorem rowsSound20_15 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10664 x
  · exact rowEval10665 x
  · exact rowEval10666 x
  · exact rowEval10667 x
  · exact rowEval10668 x

theorem entryEval20_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_15 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck20_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_15]

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

theorem entryCheck20_17 : entry20_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_17 k)) := by decide +kernel

theorem rowsSound20_17 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval10674 x
  · exact rowEval10675 x
  · exact rowEval10676 x
  · exact rowEval10677 x
  · exact rowEval10678 x

theorem entryEval20_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_17 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck20_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_17]

theorem entryCheck20_18 : entry20_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_18 k)) := by decide +kernel

theorem rowsSound20_18 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval10679 x
  · exact rowEval10680 x
  · exact rowEval10681 x
  · exact rowEval10682 x
  · exact rowEval10683 x

theorem entryEval20_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_18 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck20_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_18]

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

theorem entryCheck20_20 : entry20_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_20 k)) := by decide +kernel

theorem rowsSound20_20 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval10689 x
  · exact rowEval10690 x
  · exact rowEval10691 x
  · exact rowEval10692 x
  · exact rowEval10693 x

theorem entryEval20_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_20 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck20_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_20]

end MUB6.Certificate.GramEntries.Block3

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

theorem rawRowCheck11414 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form20 = rawRow11414 := by decide +kernel

theorem rowCheck11414 : row11414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11414 := by decide +kernel

theorem rowEval11414 (x : Key → ℝ) : Integer.Sparse.eval row11414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11414, Integer.Sparse.eval_collectBalanced, rawRowCheck11414]

theorem rawRowCheck11415 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form20 = rawRow11415 := by decide +kernel

theorem rowCheck11415 : row11415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11415 := by decide +kernel

theorem rowEval11415 (x : Key → ℝ) : Integer.Sparse.eval row11415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11415, Integer.Sparse.eval_collectBalanced, rawRowCheck11415]

theorem rawRowCheck11416 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form20 = rawRow11416 := by decide +kernel

theorem rowCheck11416 : row11416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11416 := by decide +kernel

theorem rowEval11416 (x : Key → ℝ) : Integer.Sparse.eval row11416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11416, Integer.Sparse.eval_collectBalanced, rawRowCheck11416]

theorem rawRowCheck11417 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form20 = rawRow11417 := by decide +kernel

theorem rowCheck11417 : row11417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11417 := by decide +kernel

theorem rowEval11417 (x : Key → ℝ) : Integer.Sparse.eval row11417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11417, Integer.Sparse.eval_collectBalanced, rawRowCheck11417]

theorem rawRowCheck11418 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form20 = rawRow11418 := by decide +kernel

theorem rowCheck11418 : row11418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11418 := by decide +kernel

theorem rowEval11418 (x : Key → ℝ) : Integer.Sparse.eval row11418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11418, Integer.Sparse.eval_collectBalanced, rawRowCheck11418]

theorem rawRowCheck11419 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form20 = rawRow11419 := by decide +kernel

theorem rowCheck11419 : row11419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11419 := by decide +kernel

theorem rowEval11419 (x : Key → ℝ) : Integer.Sparse.eval row11419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11419, Integer.Sparse.eval_collectBalanced, rawRowCheck11419]

theorem rawRowCheck11420 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form20 = rawRow11420 := by decide +kernel

theorem rowCheck11420 : row11420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11420 := by decide +kernel

theorem rowEval11420 (x : Key → ℝ) : Integer.Sparse.eval row11420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11420, Integer.Sparse.eval_collectBalanced, rawRowCheck11420]

theorem rawRowCheck11421 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form20 = rawRow11421 := by decide +kernel

theorem rowCheck11421 : row11421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11421 := by decide +kernel

theorem rowEval11421 (x : Key → ℝ) : Integer.Sparse.eval row11421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11421, Integer.Sparse.eval_collectBalanced, rawRowCheck11421]

theorem rawRowCheck11422 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form20 = rawRow11422 := by decide +kernel

theorem rowCheck11422 : row11422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11422 := by decide +kernel

theorem rowEval11422 (x : Key → ℝ) : Integer.Sparse.eval row11422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11422, Integer.Sparse.eval_collectBalanced, rawRowCheck11422]

theorem rawRowCheck11423 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form20 = rawRow11423 := by decide +kernel

theorem rowCheck11423 : row11423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11423 := by decide +kernel

theorem rowEval11423 (x : Key → ℝ) : Integer.Sparse.eval row11423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11423, Integer.Sparse.eval_collectBalanced, rawRowCheck11423]

theorem rawRowCheck11424 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form20 = rawRow11424 := by decide +kernel

theorem rowCheck11424 : row11424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11424 := by decide +kernel

theorem rowEval11424 (x : Key → ℝ) : Integer.Sparse.eval row11424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11424, Integer.Sparse.eval_collectBalanced, rawRowCheck11424]

theorem rawRowCheck11425 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form20 = rawRow11425 := by decide +kernel

theorem rowCheck11425 : row11425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11425 := by decide +kernel

theorem rowEval11425 (x : Key → ℝ) : Integer.Sparse.eval row11425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11425, Integer.Sparse.eval_collectBalanced, rawRowCheck11425]

theorem rawRowCheck11426 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form20 = rawRow11426 := by decide +kernel

theorem rowCheck11426 : row11426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11426 := by decide +kernel

theorem rowEval11426 (x : Key → ℝ) : Integer.Sparse.eval row11426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11426, Integer.Sparse.eval_collectBalanced, rawRowCheck11426]

theorem rawRowCheck11427 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form20 = rawRow11427 := by decide +kernel

theorem rowCheck11427 : row11427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11427 := by decide +kernel

theorem rowEval11427 (x : Key → ℝ) : Integer.Sparse.eval row11427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11427, Integer.Sparse.eval_collectBalanced, rawRowCheck11427]

theorem rawRowCheck11428 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form20 = rawRow11428 := by decide +kernel

theorem rowCheck11428 : row11428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11428 := by decide +kernel

theorem rowEval11428 (x : Key → ℝ) : Integer.Sparse.eval row11428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11428, Integer.Sparse.eval_collectBalanced, rawRowCheck11428]

theorem rawRowCheck11429 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form20 = rawRow11429 := by decide +kernel

theorem rowCheck11429 : row11429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11429 := by decide +kernel

theorem rowEval11429 (x : Key → ℝ) : Integer.Sparse.eval row11429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11429, Integer.Sparse.eval_collectBalanced, rawRowCheck11429]

theorem rawRowCheck11430 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form20 = rawRow11430 := by decide +kernel

theorem rowCheck11430 : row11430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11430 := by decide +kernel

theorem rowEval11430 (x : Key → ℝ) : Integer.Sparse.eval row11430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11430, Integer.Sparse.eval_collectBalanced, rawRowCheck11430]

theorem rawRowCheck11431 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form20 = rawRow11431 := by decide +kernel

theorem rowCheck11431 : row11431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11431 := by decide +kernel

theorem rowEval11431 (x : Key → ℝ) : Integer.Sparse.eval row11431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11431, Integer.Sparse.eval_collectBalanced, rawRowCheck11431]

theorem rawRowCheck11432 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form20 = rawRow11432 := by decide +kernel

theorem rowCheck11432 : row11432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11432 := by decide +kernel

theorem rowEval11432 (x : Key → ℝ) : Integer.Sparse.eval row11432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11432, Integer.Sparse.eval_collectBalanced, rawRowCheck11432]

theorem rawRowCheck11433 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form20 = rawRow11433 := by decide +kernel

theorem rowCheck11433 : row11433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11433 := by decide +kernel

theorem rowEval11433 (x : Key → ℝ) : Integer.Sparse.eval row11433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11433, Integer.Sparse.eval_collectBalanced, rawRowCheck11433]

theorem rawRowCheck11434 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form20 = rawRow11434 := by decide +kernel

theorem rowCheck11434 : row11434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11434 := by decide +kernel

theorem rowEval11434 (x : Key → ℝ) : Integer.Sparse.eval row11434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11434, Integer.Sparse.eval_collectBalanced, rawRowCheck11434]

theorem rawRowCheck11435 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form20 = rawRow11435 := by decide +kernel

theorem rowCheck11435 : row11435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11435 := by decide +kernel

theorem rowEval11435 (x : Key → ℝ) : Integer.Sparse.eval row11435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11435, Integer.Sparse.eval_collectBalanced, rawRowCheck11435]

theorem rawRowCheck11436 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form20 = rawRow11436 := by decide +kernel

theorem rowCheck11436 : row11436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11436 := by decide +kernel

theorem rowEval11436 (x : Key → ℝ) : Integer.Sparse.eval row11436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11436, Integer.Sparse.eval_collectBalanced, rawRowCheck11436]

theorem rawRowCheck11437 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form20 = rawRow11437 := by decide +kernel

theorem rowCheck11437 : row11437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11437 := by decide +kernel

theorem rowEval11437 (x : Key → ℝ) : Integer.Sparse.eval row11437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11437, Integer.Sparse.eval_collectBalanced, rawRowCheck11437]

theorem rawRowCheck11438 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form20 = rawRow11438 := by decide +kernel

theorem rowCheck11438 : row11438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11438 := by decide +kernel

theorem rowEval11438 (x : Key → ℝ) : Integer.Sparse.eval row11438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11438, Integer.Sparse.eval_collectBalanced, rawRowCheck11438]

theorem rawRowCheck11439 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form20 = rawRow11439 := by decide +kernel

theorem rowCheck11439 : row11439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11439 := by decide +kernel

theorem rowEval11439 (x : Key → ℝ) : Integer.Sparse.eval row11439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11439, Integer.Sparse.eval_collectBalanced, rawRowCheck11439]

theorem rawRowCheck11440 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form20 = rawRow11440 := by decide +kernel

theorem rowCheck11440 : row11440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11440 := by decide +kernel

theorem rowEval11440 (x : Key → ℝ) : Integer.Sparse.eval row11440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11440, Integer.Sparse.eval_collectBalanced, rawRowCheck11440]

theorem rawRowCheck11441 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form20 = rawRow11441 := by decide +kernel

theorem rowCheck11441 : row11441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11441 := by decide +kernel

theorem rowEval11441 (x : Key → ℝ) : Integer.Sparse.eval row11441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11441, Integer.Sparse.eval_collectBalanced, rawRowCheck11441]

theorem rawRowCheck11442 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form20 = rawRow11442 := by decide +kernel

theorem rowCheck11442 : row11442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11442 := by decide +kernel

theorem rowEval11442 (x : Key → ℝ) : Integer.Sparse.eval row11442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11442, Integer.Sparse.eval_collectBalanced, rawRowCheck11442]

theorem rawRowCheck11443 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form20 = rawRow11443 := by decide +kernel

theorem rowCheck11443 : row11443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11443 := by decide +kernel

theorem rowEval11443 (x : Key → ℝ) : Integer.Sparse.eval row11443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11443, Integer.Sparse.eval_collectBalanced, rawRowCheck11443]

theorem rawRowCheck11444 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form20 = rawRow11444 := by decide +kernel

theorem rowCheck11444 : row11444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11444 := by decide +kernel

theorem rowEval11444 (x : Key → ℝ) : Integer.Sparse.eval row11444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11444, Integer.Sparse.eval_collectBalanced, rawRowCheck11444]

theorem rawRowCheck11445 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form20 = rawRow11445 := by decide +kernel

theorem rowCheck11445 : row11445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11445 := by decide +kernel

theorem rowEval11445 (x : Key → ℝ) : Integer.Sparse.eval row11445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11445, Integer.Sparse.eval_collectBalanced, rawRowCheck11445]

theorem rawRowCheck11446 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form20 = rawRow11446 := by decide +kernel

theorem rowCheck11446 : row11446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11446 := by decide +kernel

theorem rowEval11446 (x : Key → ℝ) : Integer.Sparse.eval row11446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11446, Integer.Sparse.eval_collectBalanced, rawRowCheck11446]

theorem rawRowCheck11447 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form20 = rawRow11447 := by decide +kernel

theorem rowCheck11447 : row11447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11447 := by decide +kernel

theorem rowEval11447 (x : Key → ℝ) : Integer.Sparse.eval row11447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11447, Integer.Sparse.eval_collectBalanced, rawRowCheck11447]

theorem rawRowCheck11448 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form20 = rawRow11448 := by decide +kernel

theorem rowCheck11448 : row11448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11448 := by decide +kernel

theorem rowEval11448 (x : Key → ℝ) : Integer.Sparse.eval row11448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11448, Integer.Sparse.eval_collectBalanced, rawRowCheck11448]

theorem rawRowCheck11449 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form20 = rawRow11449 := by decide +kernel

theorem rowCheck11449 : row11449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11449 := by decide +kernel

theorem rowEval11449 (x : Key → ℝ) : Integer.Sparse.eval row11449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11449, Integer.Sparse.eval_collectBalanced, rawRowCheck11449]

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

theorem entryCheck21_20 : entry21_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form21.terms k).coefficient) (rows21_20 k)) := by decide +kernel

theorem rowsSound21_20 (k : Fin GramFunctions.Block3.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form21.terms k).tag (GramFunctions.Block3.form21.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval11414 x
  · exact rowEval11415 x
  · exact rowEval11416 x
  · exact rowEval11417 x
  · exact rowEval11418 x
  · exact rowEval11419 x
  · exact rowEval11420 x
  · exact rowEval11421 x
  · exact rowEval11422 x
  · exact rowEval11423 x
  · exact rowEval11424 x
  · exact rowEval11425 x
  · exact rowEval11426 x
  · exact rowEval11427 x
  · exact rowEval11428 x
  · exact rowEval11429 x
  · exact rowEval11430 x
  · exact rowEval11431 x
  · exact rowEval11432 x
  · exact rowEval11433 x
  · exact rowEval11434 x
  · exact rowEval11435 x
  · exact rowEval11436 x
  · exact rowEval11437 x
  · exact rowEval11438 x
  · exact rowEval11439 x
  · exact rowEval11440 x
  · exact rowEval11441 x
  · exact rowEval11442 x
  · exact rowEval11443 x
  · exact rowEval11444 x
  · exact rowEval11445 x
  · exact rowEval11446 x
  · exact rowEval11447 x
  · exact rowEval11448 x
  · exact rowEval11449 x

theorem entryEval21_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_20 (GramNormalization.eval B) = GramFunctions.Block3.form21.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck21_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form21 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_20]

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

theorem rawRowCheck11726 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form20 = rawRow11726 := by decide +kernel

theorem rowCheck11726 : row11726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11726 := by decide +kernel

theorem rowEval11726 (x : Key → ℝ) : Integer.Sparse.eval row11726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11726, Integer.Sparse.eval_collectBalanced, rawRowCheck11726]

theorem rawRowCheck11727 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form20 = rawRow11727 := by decide +kernel

theorem rowCheck11727 : row11727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11727 := by decide +kernel

theorem rowEval11727 (x : Key → ℝ) : Integer.Sparse.eval row11727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11727, Integer.Sparse.eval_collectBalanced, rawRowCheck11727]

theorem rawRowCheck11728 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form20 = rawRow11728 := by decide +kernel

theorem rowCheck11728 : row11728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11728 := by decide +kernel

theorem rowEval11728 (x : Key → ℝ) : Integer.Sparse.eval row11728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11728, Integer.Sparse.eval_collectBalanced, rawRowCheck11728]

theorem rawRowCheck11729 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form20 = rawRow11729 := by decide +kernel

theorem rowCheck11729 : row11729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11729 := by decide +kernel

theorem rowEval11729 (x : Key → ℝ) : Integer.Sparse.eval row11729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11729, Integer.Sparse.eval_collectBalanced, rawRowCheck11729]

theorem rawRowCheck11730 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form20 = rawRow11730 := by decide +kernel

theorem rowCheck11730 : row11730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11730 := by decide +kernel

theorem rowEval11730 (x : Key → ℝ) : Integer.Sparse.eval row11730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11730, Integer.Sparse.eval_collectBalanced, rawRowCheck11730]

theorem rawRowCheck11731 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form20 = rawRow11731 := by decide +kernel

theorem rowCheck11731 : row11731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11731 := by decide +kernel

theorem rowEval11731 (x : Key → ℝ) : Integer.Sparse.eval row11731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11731, Integer.Sparse.eval_collectBalanced, rawRowCheck11731]

theorem rawRowCheck11732 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form20 = rawRow11732 := by decide +kernel

theorem rowCheck11732 : row11732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11732 := by decide +kernel

theorem rowEval11732 (x : Key → ℝ) : Integer.Sparse.eval row11732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11732, Integer.Sparse.eval_collectBalanced, rawRowCheck11732]

theorem rawRowCheck11733 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form20 = rawRow11733 := by decide +kernel

theorem rowCheck11733 : row11733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11733 := by decide +kernel

theorem rowEval11733 (x : Key → ℝ) : Integer.Sparse.eval row11733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11733, Integer.Sparse.eval_collectBalanced, rawRowCheck11733]

theorem rawRowCheck11734 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form20 = rawRow11734 := by decide +kernel

theorem rowCheck11734 : row11734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11734 := by decide +kernel

theorem rowEval11734 (x : Key → ℝ) : Integer.Sparse.eval row11734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11734, Integer.Sparse.eval_collectBalanced, rawRowCheck11734]

theorem rawRowCheck11735 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form20 = rawRow11735 := by decide +kernel

theorem rowCheck11735 : row11735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11735 := by decide +kernel

theorem rowEval11735 (x : Key → ℝ) : Integer.Sparse.eval row11735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11735, Integer.Sparse.eval_collectBalanced, rawRowCheck11735]

theorem rawRowCheck11736 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form20 = rawRow11736 := by decide +kernel

theorem rowCheck11736 : row11736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11736 := by decide +kernel

theorem rowEval11736 (x : Key → ℝ) : Integer.Sparse.eval row11736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11736, Integer.Sparse.eval_collectBalanced, rawRowCheck11736]

theorem rawRowCheck11737 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form20 = rawRow11737 := by decide +kernel

theorem rowCheck11737 : row11737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11737 := by decide +kernel

theorem rowEval11737 (x : Key → ℝ) : Integer.Sparse.eval row11737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11737, Integer.Sparse.eval_collectBalanced, rawRowCheck11737]

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

theorem entryCheck22_20 : entry22_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form22.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form22.terms k).coefficient) (rows22_20 k)) := by decide +kernel

theorem rowsSound22_20 (k : Fin GramFunctions.Block3.form22.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows22_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form22.terms k).tag (GramFunctions.Block3.form22.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval11726 x
  · exact rowEval11727 x
  · exact rowEval11728 x
  · exact rowEval11729 x
  · exact rowEval11730 x
  · exact rowEval11731 x
  · exact rowEval11732 x
  · exact rowEval11733 x
  · exact rowEval11734 x
  · exact rowEval11735 x
  · exact rowEval11736 x
  · exact rowEval11737 x
  · exact rowEval11414 x
  · exact rowEval11415 x
  · exact rowEval11416 x
  · exact rowEval11417 x
  · exact rowEval11418 x
  · exact rowEval11419 x
  · exact rowEval11420 x
  · exact rowEval11421 x
  · exact rowEval11422 x
  · exact rowEval11423 x
  · exact rowEval11424 x
  · exact rowEval11425 x
  · exact rowEval11426 x
  · exact rowEval11427 x
  · exact rowEval11428 x
  · exact rowEval11429 x
  · exact rowEval11430 x
  · exact rowEval11431 x
  · exact rowEval11432 x
  · exact rowEval11433 x
  · exact rowEval11434 x
  · exact rowEval11435 x
  · exact rowEval11436 x
  · exact rowEval11437 x

theorem entryEval22_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry22_20 (GramNormalization.eval B) = GramFunctions.Block3.form22.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck22_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form22 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound22_20]

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

theorem rawRowCheck12134 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form20 = rawRow12134 := by decide +kernel

theorem rowCheck12134 : row12134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12134 := by decide +kernel

theorem rowEval12134 (x : Key → ℝ) : Integer.Sparse.eval row12134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12134, Integer.Sparse.eval_collectBalanced, rawRowCheck12134]

theorem rawRowCheck12135 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form20 = rawRow12135 := by decide +kernel

theorem rowCheck12135 : row12135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12135 := by decide +kernel

theorem rowEval12135 (x : Key → ℝ) : Integer.Sparse.eval row12135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12135, Integer.Sparse.eval_collectBalanced, rawRowCheck12135]

theorem rawRowCheck12136 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form20 = rawRow12136 := by decide +kernel

theorem rowCheck12136 : row12136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12136 := by decide +kernel

theorem rowEval12136 (x : Key → ℝ) : Integer.Sparse.eval row12136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12136, Integer.Sparse.eval_collectBalanced, rawRowCheck12136]

theorem rawRowCheck12137 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form20 = rawRow12137 := by decide +kernel

theorem rowCheck12137 : row12137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12137 := by decide +kernel

theorem rowEval12137 (x : Key → ℝ) : Integer.Sparse.eval row12137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12137, Integer.Sparse.eval_collectBalanced, rawRowCheck12137]

theorem rawRowCheck12138 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form20 = rawRow12138 := by decide +kernel

theorem rowCheck12138 : row12138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12138 := by decide +kernel

theorem rowEval12138 (x : Key → ℝ) : Integer.Sparse.eval row12138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12138, Integer.Sparse.eval_collectBalanced, rawRowCheck12138]

theorem rawRowCheck12139 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form20 = rawRow12139 := by decide +kernel

theorem rowCheck12139 : row12139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12139 := by decide +kernel

theorem rowEval12139 (x : Key → ℝ) : Integer.Sparse.eval row12139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12139, Integer.Sparse.eval_collectBalanced, rawRowCheck12139]

theorem rawRowCheck12140 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form20 = rawRow12140 := by decide +kernel

theorem rowCheck12140 : row12140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12140 := by decide +kernel

theorem rowEval12140 (x : Key → ℝ) : Integer.Sparse.eval row12140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12140, Integer.Sparse.eval_collectBalanced, rawRowCheck12140]

theorem rawRowCheck12141 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form20 = rawRow12141 := by decide +kernel

theorem rowCheck12141 : row12141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12141 := by decide +kernel

theorem rowEval12141 (x : Key → ℝ) : Integer.Sparse.eval row12141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12141, Integer.Sparse.eval_collectBalanced, rawRowCheck12141]

theorem rawRowCheck12142 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form20 = rawRow12142 := by decide +kernel

theorem rowCheck12142 : row12142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12142 := by decide +kernel

theorem rowEval12142 (x : Key → ℝ) : Integer.Sparse.eval row12142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12142, Integer.Sparse.eval_collectBalanced, rawRowCheck12142]

theorem rawRowCheck12143 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form20 = rawRow12143 := by decide +kernel

theorem rowCheck12143 : row12143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12143 := by decide +kernel

theorem rowEval12143 (x : Key → ℝ) : Integer.Sparse.eval row12143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12143, Integer.Sparse.eval_collectBalanced, rawRowCheck12143]

theorem rawRowCheck12144 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form20 = rawRow12144 := by decide +kernel

theorem rowCheck12144 : row12144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12144 := by decide +kernel

theorem rowEval12144 (x : Key → ℝ) : Integer.Sparse.eval row12144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12144, Integer.Sparse.eval_collectBalanced, rawRowCheck12144]

theorem rawRowCheck12145 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form20 = rawRow12145 := by decide +kernel

theorem rowCheck12145 : row12145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12145 := by decide +kernel

theorem rowEval12145 (x : Key → ℝ) : Integer.Sparse.eval row12145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12145, Integer.Sparse.eval_collectBalanced, rawRowCheck12145]

theorem rawRowCheck12146 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form20 = rawRow12146 := by decide +kernel

theorem rowCheck12146 : row12146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12146 := by decide +kernel

theorem rowEval12146 (x : Key → ℝ) : Integer.Sparse.eval row12146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12146, Integer.Sparse.eval_collectBalanced, rawRowCheck12146]

theorem rawRowCheck12147 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form20 = rawRow12147 := by decide +kernel

theorem rowCheck12147 : row12147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12147 := by decide +kernel

theorem rowEval12147 (x : Key → ℝ) : Integer.Sparse.eval row12147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12147, Integer.Sparse.eval_collectBalanced, rawRowCheck12147]

theorem rawRowCheck12148 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form20 = rawRow12148 := by decide +kernel

theorem rowCheck12148 : row12148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12148 := by decide +kernel

theorem rowEval12148 (x : Key → ℝ) : Integer.Sparse.eval row12148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12148, Integer.Sparse.eval_collectBalanced, rawRowCheck12148]

theorem rawRowCheck12149 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form20 = rawRow12149 := by decide +kernel

theorem rowCheck12149 : row12149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12149 := by decide +kernel

theorem rowEval12149 (x : Key → ℝ) : Integer.Sparse.eval row12149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12149, Integer.Sparse.eval_collectBalanced, rawRowCheck12149]

theorem rawRowCheck12150 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form20 = rawRow12150 := by decide +kernel

theorem rowCheck12150 : row12150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12150 := by decide +kernel

theorem rowEval12150 (x : Key → ℝ) : Integer.Sparse.eval row12150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12150, Integer.Sparse.eval_collectBalanced, rawRowCheck12150]

theorem rawRowCheck12151 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form20 = rawRow12151 := by decide +kernel

theorem rowCheck12151 : row12151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12151 := by decide +kernel

theorem rowEval12151 (x : Key → ℝ) : Integer.Sparse.eval row12151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12151, Integer.Sparse.eval_collectBalanced, rawRowCheck12151]

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

theorem entryCheck23_20 : entry23_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_20 k)) := by decide +kernel

theorem rowsSound23_20 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval12134 x
  · exact rowEval12135 x
  · exact rowEval12136 x
  · exact rowEval12137 x
  · exact rowEval12138 x
  · exact rowEval12139 x
  · exact rowEval12140 x
  · exact rowEval12141 x
  · exact rowEval12142 x
  · exact rowEval12143 x
  · exact rowEval12144 x
  · exact rowEval12145 x
  · exact rowEval12146 x
  · exact rowEval12147 x
  · exact rowEval12148 x
  · exact rowEval12149 x
  · exact rowEval12150 x
  · exact rowEval12151 x

theorem entryEval23_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_20 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck23_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_20]

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

theorem rawRowCheck12306 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form20 = rawRow12306 := by decide +kernel

theorem rowCheck12306 : row12306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12306 := by decide +kernel

theorem rowEval12306 (x : Key → ℝ) : Integer.Sparse.eval row12306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12306, Integer.Sparse.eval_collectBalanced, rawRowCheck12306]

theorem rawRowCheck12307 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form20 = rawRow12307 := by decide +kernel

theorem rowCheck12307 : row12307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12307 := by decide +kernel

theorem rowEval12307 (x : Key → ℝ) : Integer.Sparse.eval row12307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12307, Integer.Sparse.eval_collectBalanced, rawRowCheck12307]

theorem rawRowCheck12308 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form20 = rawRow12308 := by decide +kernel

theorem rowCheck12308 : row12308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12308 := by decide +kernel

theorem rowEval12308 (x : Key → ℝ) : Integer.Sparse.eval row12308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12308, Integer.Sparse.eval_collectBalanced, rawRowCheck12308]

theorem rawRowCheck12309 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form20 = rawRow12309 := by decide +kernel

theorem rowCheck12309 : row12309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12309 := by decide +kernel

theorem rowEval12309 (x : Key → ℝ) : Integer.Sparse.eval row12309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12309, Integer.Sparse.eval_collectBalanced, rawRowCheck12309]

theorem rawRowCheck12310 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form20 = rawRow12310 := by decide +kernel

theorem rowCheck12310 : row12310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12310 := by decide +kernel

theorem rowEval12310 (x : Key → ℝ) : Integer.Sparse.eval row12310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck12310, Integer.Sparse.eval_collectBalanced, rawRowCheck12310]

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

theorem entryCheck24_20 : entry24_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_20 k)) := by decide +kernel

theorem rowsSound24_20 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval12306 x
  · exact rowEval12307 x
  · exact rowEval12308 x
  · exact rowEval12309 x
  · exact rowEval12310 x

theorem entryEval24_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_20 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck24_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_20]

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

theorem rawRowCheck13019 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form20 = rawRow13019 := by decide +kernel

theorem rowCheck13019 : row13019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13019 := by decide +kernel

theorem rowEval13019 (x : Key → ℝ) : Integer.Sparse.eval row13019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13019, Integer.Sparse.eval_collectBalanced, rawRowCheck13019]

theorem rawRowCheck13020 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form20 = rawRow13020 := by decide +kernel

theorem rowCheck13020 : row13020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13020 := by decide +kernel

theorem rowEval13020 (x : Key → ℝ) : Integer.Sparse.eval row13020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13020, Integer.Sparse.eval_collectBalanced, rawRowCheck13020]

theorem rawRowCheck13021 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form20 = rawRow13021 := by decide +kernel

theorem rowCheck13021 : row13021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13021 := by decide +kernel

theorem rowEval13021 (x : Key → ℝ) : Integer.Sparse.eval row13021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13021, Integer.Sparse.eval_collectBalanced, rawRowCheck13021]

theorem rawRowCheck13022 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form20 = rawRow13022 := by decide +kernel

theorem rowCheck13022 : row13022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13022 := by decide +kernel

theorem rowEval13022 (x : Key → ℝ) : Integer.Sparse.eval row13022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13022, Integer.Sparse.eval_collectBalanced, rawRowCheck13022]

theorem rawRowCheck13023 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form20 = rawRow13023 := by decide +kernel

theorem rowCheck13023 : row13023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13023 := by decide +kernel

theorem rowEval13023 (x : Key → ℝ) : Integer.Sparse.eval row13023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13023, Integer.Sparse.eval_collectBalanced, rawRowCheck13023]

theorem rawRowCheck13024 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form20 = rawRow13024 := by decide +kernel

theorem rowCheck13024 : row13024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13024 := by decide +kernel

theorem rowEval13024 (x : Key → ℝ) : Integer.Sparse.eval row13024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13024, Integer.Sparse.eval_collectBalanced, rawRowCheck13024]

theorem rawRowCheck13025 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form20 = rawRow13025 := by decide +kernel

theorem rowCheck13025 : row13025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13025 := by decide +kernel

theorem rowEval13025 (x : Key → ℝ) : Integer.Sparse.eval row13025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13025, Integer.Sparse.eval_collectBalanced, rawRowCheck13025]

theorem rawRowCheck13026 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form20 = rawRow13026 := by decide +kernel

theorem rowCheck13026 : row13026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13026 := by decide +kernel

theorem rowEval13026 (x : Key → ℝ) : Integer.Sparse.eval row13026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13026, Integer.Sparse.eval_collectBalanced, rawRowCheck13026]

theorem rawRowCheck13027 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form20 = rawRow13027 := by decide +kernel

theorem rowCheck13027 : row13027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13027 := by decide +kernel

theorem rowEval13027 (x : Key → ℝ) : Integer.Sparse.eval row13027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13027, Integer.Sparse.eval_collectBalanced, rawRowCheck13027]

theorem rawRowCheck13028 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form20 = rawRow13028 := by decide +kernel

theorem rowCheck13028 : row13028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13028 := by decide +kernel

theorem rowEval13028 (x : Key → ℝ) : Integer.Sparse.eval row13028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13028, Integer.Sparse.eval_collectBalanced, rawRowCheck13028]

theorem rawRowCheck13029 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form20 = rawRow13029 := by decide +kernel

theorem rowCheck13029 : row13029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13029 := by decide +kernel

theorem rowEval13029 (x : Key → ℝ) : Integer.Sparse.eval row13029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13029, Integer.Sparse.eval_collectBalanced, rawRowCheck13029]

theorem rawRowCheck13030 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form20 = rawRow13030 := by decide +kernel

theorem rowCheck13030 : row13030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13030 := by decide +kernel

theorem rowEval13030 (x : Key → ℝ) : Integer.Sparse.eval row13030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13030, Integer.Sparse.eval_collectBalanced, rawRowCheck13030]

theorem rawRowCheck13031 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form20 = rawRow13031 := by decide +kernel

theorem rowCheck13031 : row13031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13031 := by decide +kernel

theorem rowEval13031 (x : Key → ℝ) : Integer.Sparse.eval row13031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13031, Integer.Sparse.eval_collectBalanced, rawRowCheck13031]

theorem rawRowCheck13032 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form20 = rawRow13032 := by decide +kernel

theorem rowCheck13032 : row13032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13032 := by decide +kernel

theorem rowEval13032 (x : Key → ℝ) : Integer.Sparse.eval row13032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13032, Integer.Sparse.eval_collectBalanced, rawRowCheck13032]

theorem rawRowCheck13033 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form20 = rawRow13033 := by decide +kernel

theorem rowCheck13033 : row13033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13033 := by decide +kernel

theorem rowEval13033 (x : Key → ℝ) : Integer.Sparse.eval row13033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13033, Integer.Sparse.eval_collectBalanced, rawRowCheck13033]

theorem rawRowCheck13034 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form20 = rawRow13034 := by decide +kernel

theorem rowCheck13034 : row13034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13034 := by decide +kernel

theorem rowEval13034 (x : Key → ℝ) : Integer.Sparse.eval row13034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13034, Integer.Sparse.eval_collectBalanced, rawRowCheck13034]

theorem rawRowCheck13035 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form20 = rawRow13035 := by decide +kernel

theorem rowCheck13035 : row13035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13035 := by decide +kernel

theorem rowEval13035 (x : Key → ℝ) : Integer.Sparse.eval row13035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13035, Integer.Sparse.eval_collectBalanced, rawRowCheck13035]

theorem rawRowCheck13036 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form20 = rawRow13036 := by decide +kernel

theorem rowCheck13036 : row13036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13036 := by decide +kernel

theorem rowEval13036 (x : Key → ℝ) : Integer.Sparse.eval row13036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13036, Integer.Sparse.eval_collectBalanced, rawRowCheck13036]

theorem rawRowCheck13037 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form20 = rawRow13037 := by decide +kernel

theorem rowCheck13037 : row13037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13037 := by decide +kernel

theorem rowEval13037 (x : Key → ℝ) : Integer.Sparse.eval row13037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13037, Integer.Sparse.eval_collectBalanced, rawRowCheck13037]

theorem rawRowCheck13038 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form20 = rawRow13038 := by decide +kernel

theorem rowCheck13038 : row13038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13038 := by decide +kernel

theorem rowEval13038 (x : Key → ℝ) : Integer.Sparse.eval row13038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13038, Integer.Sparse.eval_collectBalanced, rawRowCheck13038]

theorem rawRowCheck13039 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form20 = rawRow13039 := by decide +kernel

theorem rowCheck13039 : row13039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13039 := by decide +kernel

theorem rowEval13039 (x : Key → ℝ) : Integer.Sparse.eval row13039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13039, Integer.Sparse.eval_collectBalanced, rawRowCheck13039]

theorem rawRowCheck13040 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form20 = rawRow13040 := by decide +kernel

theorem rowCheck13040 : row13040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13040 := by decide +kernel

theorem rowEval13040 (x : Key → ℝ) : Integer.Sparse.eval row13040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13040, Integer.Sparse.eval_collectBalanced, rawRowCheck13040]

theorem rawRowCheck13041 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form20 = rawRow13041 := by decide +kernel

theorem rowCheck13041 : row13041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13041 := by decide +kernel

theorem rowEval13041 (x : Key → ℝ) : Integer.Sparse.eval row13041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13041, Integer.Sparse.eval_collectBalanced, rawRowCheck13041]

theorem rawRowCheck13042 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form20 = rawRow13042 := by decide +kernel

theorem rowCheck13042 : row13042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13042 := by decide +kernel

theorem rowEval13042 (x : Key → ℝ) : Integer.Sparse.eval row13042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13042, Integer.Sparse.eval_collectBalanced, rawRowCheck13042]

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

theorem entryCheck26_20 : entry26_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_20 k)) := by decide +kernel

theorem rowsSound26_20 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval13019 x
  · exact rowEval13020 x
  · exact rowEval13021 x
  · exact rowEval13022 x
  · exact rowEval13023 x
  · exact rowEval13024 x
  · exact rowEval13025 x
  · exact rowEval13026 x
  · exact rowEval13027 x
  · exact rowEval13028 x
  · exact rowEval13029 x
  · exact rowEval13030 x
  · exact rowEval13031 x
  · exact rowEval13032 x
  · exact rowEval13033 x
  · exact rowEval13034 x
  · exact rowEval13035 x
  · exact rowEval13036 x
  · exact rowEval13037 x
  · exact rowEval13038 x
  · exact rowEval13039 x
  · exact rowEval13040 x
  · exact rowEval13041 x
  · exact rowEval13042 x

theorem entryEval26_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_20 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck26_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_20]

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

theorem entryEvalRow20_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 20 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 20).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval20_0 B hB
  · exact entryEval20_1 B hB
  · exact entryEval20_2 B hB
  · exact entryEval20_3 B hB
  · exact entryEval20_4 B hB
  · exact entryEval20_5 B hB
  · exact entryEval20_6 B hB
  · exact entryEval20_7 B hB
  · exact entryEval20_8 B hB
  · exact entryEval20_9 B hB
  · exact entryEval20_10 B hB
  · exact entryEval20_11 B hB
  · exact entryEval20_12 B hB
  · exact entryEval20_13 B hB
  · exact entryEval20_14 B hB
  · exact entryEval20_15 B hB
  · exact entryEval20_16 B hB
  · exact entryEval20_17 B hB
  · exact entryEval20_18 B hB
  · exact entryEval20_19 B hB
  · exact entryEval20_20 B hB
  · exact (entryEval21_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval22_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval23_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval24_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval25_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e_oai
