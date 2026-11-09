-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramNonnegative.quadratic1_nonneg_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:20:46.636453+00:00
-- url     : https://prove2.me/submissions/137af9d8-f575-4948-8cf1-d26a00f0bdde

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E042
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

theorem average_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∀ i, 0 ≤ f i) : 0 ≤ average f := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => h i))

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

/-- A real positive semidefinite matrix gives a nonnegative Gram form of any
finite family of complex-valued random variables. -/
theorem realGram_psd_nonneg [DecidableEq ι] (Z : Matrix ι ι ℝ) (hZ : Z.PosSemidef)
    (F : ι → Ω → ℂ) : 0 ≤ ∑ i, ∑ j, Z i j * realGram (F i) (F j) := by
  have hpoint (ω : Ω) : 0 ≤ ∑ i, ∑ j, Z i j * (F i ω * conj (F j ω)).re := by
    have hr := hZ.dotProduct_mulVec_nonneg (fun i => (F i ω).re)
    have hi := hZ.dotProduct_mulVec_nonneg (fun i => (F i ω).im)
    have hexpand : (∑ i, ∑ j, Z i j * (F i ω * conj (F j ω)).re) =
        (star (fun i => (F i ω).re) ⬝ᵥ Z *ᵥ (fun i => (F i ω).re)) +
        (star (fun i => (F i ω).im) ⬝ᵥ Z *ᵥ (fun i => (F i ω).im)) := by
      simp only [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, Pi.star_apply, star_trivial, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hexpand]
    exact add_nonneg hr hi
  have h := average_nonneg _ hpoint
  simpa only [average_sum, average_mul, realGram] using h

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

/-- A positive semidefinite matrix proves nonnegativity of the fully
expanded mixed expression for any finite family of integer linear forms. -/
theorem LinearForm.mixedGram_psd_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → LinearForm) (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (Z : Matrix ι ι ℝ) (hZ : Z.PosSemidef) :
    0 ≤ ∑ i, ∑ j, Z i j * (P i).mixedGram (P j) B := by
  have h := realGram_psd_nonneg Z hZ (fun i => (P i).auxiliaryEval B)
  simpa only [LinearForm.auxiliaryEval_gram _ _ B hB] using h

end MUB6.Certificate.GramFunctions

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact rational Gram witnesses

A unit lower triangular matrix and a positive rational diagonal certify a real
matrix's positive definiteness. The large numerical checks can therefore be
split into separate rational identities for individual matrix entries.
-/
namespace MUB6.Certificate

open Matrix
open scoped BigOperators

theorem real_lowerUnit_det {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ) :
    (realMatrix (lowerUnit entries)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [realMatrix]
  · intro i j hij
    change i < j at hij
    change (lowerUnit entries i j : ℝ) = 0
    rw [lowerUnit_above entries hij]
    norm_num

/-- A collection of scalar rational checks certifies the full real Gram identity. -/
theorem real_gram_eq {n : ℕ} (Z U : Matrix (Fin n) (Fin n) ℚ) (D : Fin n → ℚ)
    (h : ∀ i j, Z i j = ∑ k, U k i * D k * U k j) :
    realMatrix Z = (realMatrix U)ᴴ * Matrix.diagonal (fun k => (D k : ℝ)) * realMatrix U := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have hij := congrArg (fun q : ℚ => (q : ℝ)) (h i j)
  simpa [realMatrix, Rat.cast_sum, Rat.cast_mul] using hij

/-- Soundness of a positive diagonal/unit-triangular Gram certificate. -/
theorem posDef_of_rational_gram {n : ℕ}
    (Z entries : Matrix (Fin n) (Fin n) ℚ) (D : Fin n → ℚ)
    (hD : ∀ i, 0 < D i)
    (hZ : ∀ i j, Z i j = ∑ k, lowerUnit entries k i * D k * lowerUnit entries k j) :
    (realMatrix Z).PosDef := by
  rw [real_gram_eq Z (lowerUnit entries) D hZ]
  apply Matrix.PosDef.conjTranspose_mul_mul_same
  · apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast hD i
  · apply Matrix.mulVec_injective_of_isUnit
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [real_lowerUnit_det]
    exact isUnit_one

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact integer matrix for λ = (1, 1, 3), m = 21, exponent = 13.
-/

namespace MUB6.Certificate.GramData.Block1

open Matrix
open scoped BigOperators

theorem pivot_0 : 40000 < D 0 := by decide +kernel

theorem pivot_1 : 40000 < D 1 := by decide +kernel

theorem pivot_2 : 40000 < D 2 := by decide +kernel

theorem pivot_3 : 40000 < D 3 := by decide +kernel

theorem pivot_4 : 40000 < D 4 := by decide +kernel

theorem pivot_5 : 40000 < D 5 := by decide +kernel

theorem pivot_6 : 40000 < D 6 := by decide +kernel

theorem pivot_7 : 40000 < D 7 := by decide +kernel

theorem pivot_8 : 40000 < D 8 := by decide +kernel

theorem pivot_9 : 40000 < D 9 := by decide +kernel

theorem pivot_10 : 40000 < D 10 := by decide +kernel

theorem pivot_11 : 40000 < D 11 := by decide +kernel

theorem pivot_12 : 40000 < D 12 := by decide +kernel

theorem pivot_13 : 40000 < D 13 := by decide +kernel

theorem pivot_14 : 40000 < D 14 := by decide +kernel

theorem pivot_15 : 40000 < D 15 := by decide +kernel

theorem pivot_16 : 40000 < D 16 := by decide +kernel

theorem pivot_17 : 40000 < D 17 := by decide +kernel

theorem pivot_18 : 40000 < D 18 := by decide +kernel

theorem pivot_19 : 40000 < D 19 := by decide +kernel

theorem pivot_20 : 40000 < D 20 := by decide +kernel

theorem entry_0_0 : Z 0 0 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_0_1 : Z 0 1 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_0_2 : Z 0 2 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_0_3 : Z 0 3 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_0_4 : Z 0 4 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_0_5 : Z 0 5 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_0_6 : Z 0 6 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_0_7 : Z 0 7 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_0_8 : Z 0 8 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_0_9 : Z 0 9 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_0_10 : Z 0 10 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_0_11 : Z 0 11 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_0_12 : Z 0 12 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_0_13 : Z 0 13 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_0_14 : Z 0 14 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_0_15 : Z 0 15 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_0_16 : Z 0 16 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_0_17 : Z 0 17 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_0_18 : Z 0 18 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_0_19 : Z 0 19 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_0_20 : Z 0 20 =
    ∑ k : Fin 21, lowerUnit entries k 0 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_1_0 : Z 1 0 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_1_1 : Z 1 1 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_1_2 : Z 1 2 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_1_3 : Z 1 3 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_1_4 : Z 1 4 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_1_5 : Z 1 5 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_1_6 : Z 1 6 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_1_7 : Z 1 7 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_1_8 : Z 1 8 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_1_9 : Z 1 9 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_1_10 : Z 1 10 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_1_11 : Z 1 11 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_1_12 : Z 1 12 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_1_13 : Z 1 13 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_1_14 : Z 1 14 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_1_15 : Z 1 15 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_1_16 : Z 1 16 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_1_17 : Z 1 17 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_1_18 : Z 1 18 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_1_19 : Z 1 19 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_1_20 : Z 1 20 =
    ∑ k : Fin 21, lowerUnit entries k 1 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_2_0 : Z 2 0 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_2_1 : Z 2 1 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_2_2 : Z 2 2 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_2_3 : Z 2 3 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_2_4 : Z 2 4 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_2_5 : Z 2 5 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_2_6 : Z 2 6 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_2_7 : Z 2 7 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_2_8 : Z 2 8 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_2_9 : Z 2 9 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_2_10 : Z 2 10 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_2_11 : Z 2 11 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_2_12 : Z 2 12 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_2_13 : Z 2 13 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_2_14 : Z 2 14 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_2_15 : Z 2 15 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_2_16 : Z 2 16 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_2_17 : Z 2 17 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_2_18 : Z 2 18 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_2_19 : Z 2 19 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_2_20 : Z 2 20 =
    ∑ k : Fin 21, lowerUnit entries k 2 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_3_0 : Z 3 0 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_3_1 : Z 3 1 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_3_2 : Z 3 2 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_3_3 : Z 3 3 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_3_4 : Z 3 4 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_3_5 : Z 3 5 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_3_6 : Z 3 6 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_3_7 : Z 3 7 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_3_8 : Z 3 8 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_3_9 : Z 3 9 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_3_10 : Z 3 10 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_3_11 : Z 3 11 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_3_12 : Z 3 12 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_3_13 : Z 3 13 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_3_14 : Z 3 14 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_3_15 : Z 3 15 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_3_16 : Z 3 16 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_3_17 : Z 3 17 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_3_18 : Z 3 18 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_3_19 : Z 3 19 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_3_20 : Z 3 20 =
    ∑ k : Fin 21, lowerUnit entries k 3 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_4_0 : Z 4 0 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_4_1 : Z 4 1 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_4_2 : Z 4 2 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_4_3 : Z 4 3 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_4_4 : Z 4 4 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_4_5 : Z 4 5 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_4_6 : Z 4 6 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_4_7 : Z 4 7 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_4_8 : Z 4 8 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_4_9 : Z 4 9 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_4_10 : Z 4 10 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_4_11 : Z 4 11 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_4_12 : Z 4 12 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_4_13 : Z 4 13 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_4_14 : Z 4 14 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_4_15 : Z 4 15 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_4_16 : Z 4 16 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_4_17 : Z 4 17 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_4_18 : Z 4 18 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_4_19 : Z 4 19 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_4_20 : Z 4 20 =
    ∑ k : Fin 21, lowerUnit entries k 4 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_5_0 : Z 5 0 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_5_1 : Z 5 1 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_5_2 : Z 5 2 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_5_3 : Z 5 3 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_5_4 : Z 5 4 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_5_5 : Z 5 5 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_5_6 : Z 5 6 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_5_7 : Z 5 7 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_5_8 : Z 5 8 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_5_9 : Z 5 9 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_5_10 : Z 5 10 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_5_11 : Z 5 11 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_5_12 : Z 5 12 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_5_13 : Z 5 13 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_5_14 : Z 5 14 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_5_15 : Z 5 15 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_5_16 : Z 5 16 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_5_17 : Z 5 17 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_5_18 : Z 5 18 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_5_19 : Z 5 19 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_5_20 : Z 5 20 =
    ∑ k : Fin 21, lowerUnit entries k 5 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_6_0 : Z 6 0 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_6_1 : Z 6 1 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_6_2 : Z 6 2 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_6_3 : Z 6 3 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_6_4 : Z 6 4 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_6_5 : Z 6 5 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_6_6 : Z 6 6 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_6_7 : Z 6 7 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_6_8 : Z 6 8 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_6_9 : Z 6 9 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_6_10 : Z 6 10 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_6_11 : Z 6 11 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_6_12 : Z 6 12 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_6_13 : Z 6 13 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_6_14 : Z 6 14 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_6_15 : Z 6 15 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_6_16 : Z 6 16 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_6_17 : Z 6 17 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_6_18 : Z 6 18 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_6_19 : Z 6 19 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_6_20 : Z 6 20 =
    ∑ k : Fin 21, lowerUnit entries k 6 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_7_0 : Z 7 0 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_7_1 : Z 7 1 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_7_2 : Z 7 2 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_7_3 : Z 7 3 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_7_4 : Z 7 4 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_7_5 : Z 7 5 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_7_6 : Z 7 6 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_7_7 : Z 7 7 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_7_8 : Z 7 8 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_7_9 : Z 7 9 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_7_10 : Z 7 10 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_7_11 : Z 7 11 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_7_12 : Z 7 12 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_7_13 : Z 7 13 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_7_14 : Z 7 14 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_7_15 : Z 7 15 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_7_16 : Z 7 16 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_7_17 : Z 7 17 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_7_18 : Z 7 18 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_7_19 : Z 7 19 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_7_20 : Z 7 20 =
    ∑ k : Fin 21, lowerUnit entries k 7 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_8_0 : Z 8 0 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_8_1 : Z 8 1 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_8_2 : Z 8 2 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_8_3 : Z 8 3 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_8_4 : Z 8 4 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_8_5 : Z 8 5 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_8_6 : Z 8 6 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_8_7 : Z 8 7 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_8_8 : Z 8 8 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_8_9 : Z 8 9 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_8_10 : Z 8 10 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_8_11 : Z 8 11 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_8_12 : Z 8 12 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_8_13 : Z 8 13 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_8_14 : Z 8 14 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_8_15 : Z 8 15 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_8_16 : Z 8 16 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_8_17 : Z 8 17 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_8_18 : Z 8 18 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_8_19 : Z 8 19 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_8_20 : Z 8 20 =
    ∑ k : Fin 21, lowerUnit entries k 8 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_9_0 : Z 9 0 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_9_1 : Z 9 1 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_9_2 : Z 9 2 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_9_3 : Z 9 3 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_9_4 : Z 9 4 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_9_5 : Z 9 5 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_9_6 : Z 9 6 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_9_7 : Z 9 7 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_9_8 : Z 9 8 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_9_9 : Z 9 9 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_9_10 : Z 9 10 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_9_11 : Z 9 11 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_9_12 : Z 9 12 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_9_13 : Z 9 13 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_9_14 : Z 9 14 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_9_15 : Z 9 15 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_9_16 : Z 9 16 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_9_17 : Z 9 17 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_9_18 : Z 9 18 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_9_19 : Z 9 19 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_9_20 : Z 9 20 =
    ∑ k : Fin 21, lowerUnit entries k 9 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_10_0 : Z 10 0 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_10_1 : Z 10 1 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_10_2 : Z 10 2 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_10_3 : Z 10 3 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_10_4 : Z 10 4 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_10_5 : Z 10 5 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_10_6 : Z 10 6 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_10_7 : Z 10 7 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_10_8 : Z 10 8 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_10_9 : Z 10 9 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_10_10 : Z 10 10 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_10_11 : Z 10 11 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_10_12 : Z 10 12 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_10_13 : Z 10 13 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_10_14 : Z 10 14 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_10_15 : Z 10 15 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_10_16 : Z 10 16 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_10_17 : Z 10 17 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_10_18 : Z 10 18 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_10_19 : Z 10 19 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_10_20 : Z 10 20 =
    ∑ k : Fin 21, lowerUnit entries k 10 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_11_0 : Z 11 0 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_11_1 : Z 11 1 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_11_2 : Z 11 2 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_11_3 : Z 11 3 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_11_4 : Z 11 4 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_11_5 : Z 11 5 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_11_6 : Z 11 6 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_11_7 : Z 11 7 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_11_8 : Z 11 8 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_11_9 : Z 11 9 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_11_10 : Z 11 10 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_11_11 : Z 11 11 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_11_12 : Z 11 12 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_11_13 : Z 11 13 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_11_14 : Z 11 14 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_11_15 : Z 11 15 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_11_16 : Z 11 16 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_11_17 : Z 11 17 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_11_18 : Z 11 18 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_11_19 : Z 11 19 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_11_20 : Z 11 20 =
    ∑ k : Fin 21, lowerUnit entries k 11 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_12_0 : Z 12 0 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_12_1 : Z 12 1 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_12_2 : Z 12 2 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_12_3 : Z 12 3 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_12_4 : Z 12 4 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_12_5 : Z 12 5 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_12_6 : Z 12 6 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_12_7 : Z 12 7 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_12_8 : Z 12 8 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_12_9 : Z 12 9 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_12_10 : Z 12 10 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_12_11 : Z 12 11 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_12_12 : Z 12 12 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_12_13 : Z 12 13 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_12_14 : Z 12 14 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_12_15 : Z 12 15 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_12_16 : Z 12 16 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_12_17 : Z 12 17 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_12_18 : Z 12 18 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_12_19 : Z 12 19 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_12_20 : Z 12 20 =
    ∑ k : Fin 21, lowerUnit entries k 12 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_13_0 : Z 13 0 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_13_1 : Z 13 1 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_13_2 : Z 13 2 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_13_3 : Z 13 3 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_13_4 : Z 13 4 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_13_5 : Z 13 5 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_13_6 : Z 13 6 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_13_7 : Z 13 7 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_13_8 : Z 13 8 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_13_9 : Z 13 9 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_13_10 : Z 13 10 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_13_11 : Z 13 11 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_13_12 : Z 13 12 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_13_13 : Z 13 13 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_13_14 : Z 13 14 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_13_15 : Z 13 15 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_13_16 : Z 13 16 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_13_17 : Z 13 17 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_13_18 : Z 13 18 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_13_19 : Z 13 19 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_13_20 : Z 13 20 =
    ∑ k : Fin 21, lowerUnit entries k 13 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_14_0 : Z 14 0 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_14_1 : Z 14 1 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_14_2 : Z 14 2 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_14_3 : Z 14 3 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_14_4 : Z 14 4 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_14_5 : Z 14 5 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_14_6 : Z 14 6 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_14_7 : Z 14 7 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_14_8 : Z 14 8 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_14_9 : Z 14 9 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_14_10 : Z 14 10 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_14_11 : Z 14 11 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_14_12 : Z 14 12 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_14_13 : Z 14 13 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_14_14 : Z 14 14 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_14_15 : Z 14 15 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_14_16 : Z 14 16 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_14_17 : Z 14 17 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_14_18 : Z 14 18 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_14_19 : Z 14 19 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_14_20 : Z 14 20 =
    ∑ k : Fin 21, lowerUnit entries k 14 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_15_0 : Z 15 0 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_15_1 : Z 15 1 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_15_2 : Z 15 2 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_15_3 : Z 15 3 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_15_4 : Z 15 4 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_15_5 : Z 15 5 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_15_6 : Z 15 6 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_15_7 : Z 15 7 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_15_8 : Z 15 8 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_15_9 : Z 15 9 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_15_10 : Z 15 10 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_15_11 : Z 15 11 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_15_12 : Z 15 12 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_15_13 : Z 15 13 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_15_14 : Z 15 14 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_15_15 : Z 15 15 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_15_16 : Z 15 16 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_15_17 : Z 15 17 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_15_18 : Z 15 18 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_15_19 : Z 15 19 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_15_20 : Z 15 20 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_16_0 : Z 16 0 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_16_1 : Z 16 1 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_16_2 : Z 16 2 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_16_3 : Z 16 3 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_16_4 : Z 16 4 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_16_5 : Z 16 5 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_16_6 : Z 16 6 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_16_7 : Z 16 7 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_16_8 : Z 16 8 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_16_9 : Z 16 9 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_16_10 : Z 16 10 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_16_11 : Z 16 11 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_16_12 : Z 16 12 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_16_13 : Z 16 13 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_16_14 : Z 16 14 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_16_15 : Z 16 15 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_16_16 : Z 16 16 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_16_17 : Z 16 17 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_16_18 : Z 16 18 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_16_19 : Z 16 19 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_16_20 : Z 16 20 =
    ∑ k : Fin 21, lowerUnit entries k 16 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_17_0 : Z 17 0 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_17_1 : Z 17 1 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_17_2 : Z 17 2 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_17_3 : Z 17 3 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_17_4 : Z 17 4 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_17_5 : Z 17 5 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_17_6 : Z 17 6 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_17_7 : Z 17 7 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_17_8 : Z 17 8 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_17_9 : Z 17 9 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_17_10 : Z 17 10 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_17_11 : Z 17 11 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_17_12 : Z 17 12 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_17_13 : Z 17 13 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_17_14 : Z 17 14 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_17_15 : Z 17 15 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_17_16 : Z 17 16 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_17_17 : Z 17 17 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_17_18 : Z 17 18 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_17_19 : Z 17 19 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_17_20 : Z 17 20 =
    ∑ k : Fin 21, lowerUnit entries k 17 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_18_0 : Z 18 0 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_18_1 : Z 18 1 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_18_2 : Z 18 2 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_18_3 : Z 18 3 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_18_4 : Z 18 4 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_18_5 : Z 18 5 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_18_6 : Z 18 6 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_18_7 : Z 18 7 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_18_8 : Z 18 8 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_18_9 : Z 18 9 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_18_10 : Z 18 10 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_18_11 : Z 18 11 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_18_12 : Z 18 12 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_18_13 : Z 18 13 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_18_14 : Z 18 14 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_18_15 : Z 18 15 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_18_16 : Z 18 16 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_18_17 : Z 18 17 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_18_18 : Z 18 18 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_18_19 : Z 18 19 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_18_20 : Z 18 20 =
    ∑ k : Fin 21, lowerUnit entries k 18 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_19_0 : Z 19 0 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_19_1 : Z 19 1 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_19_2 : Z 19 2 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_19_3 : Z 19 3 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_19_4 : Z 19 4 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_19_5 : Z 19 5 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_19_6 : Z 19 6 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_19_7 : Z 19 7 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_19_8 : Z 19 8 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_19_9 : Z 19 9 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_19_10 : Z 19 10 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_19_11 : Z 19 11 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_19_12 : Z 19 12 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_19_13 : Z 19 13 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_19_14 : Z 19 14 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_19_15 : Z 19 15 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_19_16 : Z 19 16 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_19_17 : Z 19 17 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_19_18 : Z 19 18 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_19_19 : Z 19 19 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_19_20 : Z 19 20 =
    ∑ k : Fin 21, lowerUnit entries k 19 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_20_0 : Z 20 0 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_20_1 : Z 20 1 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_20_2 : Z 20 2 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_20_3 : Z 20 3 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_20_4 : Z 20 4 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_20_5 : Z 20 5 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_20_6 : Z 20 6 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_20_7 : Z 20 7 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_20_8 : Z 20 8 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_20_9 : Z 20 9 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_20_10 : Z 20 10 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_20_11 : Z 20 11 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_20_12 : Z 20 12 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 12 := by
  decide +kernel

theorem entry_20_13 : Z 20 13 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 13 := by
  decide +kernel

theorem entry_20_14 : Z 20 14 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 14 := by
  decide +kernel

theorem entry_20_15 : Z 20 15 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 15 := by
  decide +kernel

theorem entry_20_16 : Z 20 16 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 16 := by
  decide +kernel

theorem entry_20_17 : Z 20 17 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_20_18 : Z 20 18 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_20_19 : Z 20 19 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_20_20 : Z 20 20 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem pivots_pos : ∀ k : Fin 21, 0 < D k := by
  intro k
  fin_cases k
  · exact lt_trans (by norm_num) pivot_0
  · exact lt_trans (by norm_num) pivot_1
  · exact lt_trans (by norm_num) pivot_2
  · exact lt_trans (by norm_num) pivot_3
  · exact lt_trans (by norm_num) pivot_4
  · exact lt_trans (by norm_num) pivot_5
  · exact lt_trans (by norm_num) pivot_6
  · exact lt_trans (by norm_num) pivot_7
  · exact lt_trans (by norm_num) pivot_8
  · exact lt_trans (by norm_num) pivot_9
  · exact lt_trans (by norm_num) pivot_10
  · exact lt_trans (by norm_num) pivot_11
  · exact lt_trans (by norm_num) pivot_12
  · exact lt_trans (by norm_num) pivot_13
  · exact lt_trans (by norm_num) pivot_14
  · exact lt_trans (by norm_num) pivot_15
  · exact lt_trans (by norm_num) pivot_16
  · exact lt_trans (by norm_num) pivot_17
  · exact lt_trans (by norm_num) pivot_18
  · exact lt_trans (by norm_num) pivot_19
  · exact lt_trans (by norm_num) pivot_20

theorem gram : ∀ i j : Fin 21, Z i j =
    ∑ k, lowerUnit entries k i * D k * lowerUnit entries k j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact entry_0_0
  · exact entry_0_1
  · exact entry_0_2
  · exact entry_0_3
  · exact entry_0_4
  · exact entry_0_5
  · exact entry_0_6
  · exact entry_0_7
  · exact entry_0_8
  · exact entry_0_9
  · exact entry_0_10
  · exact entry_0_11
  · exact entry_0_12
  · exact entry_0_13
  · exact entry_0_14
  · exact entry_0_15
  · exact entry_0_16
  · exact entry_0_17
  · exact entry_0_18
  · exact entry_0_19
  · exact entry_0_20
  · exact entry_1_0
  · exact entry_1_1
  · exact entry_1_2
  · exact entry_1_3
  · exact entry_1_4
  · exact entry_1_5
  · exact entry_1_6
  · exact entry_1_7
  · exact entry_1_8
  · exact entry_1_9
  · exact entry_1_10
  · exact entry_1_11
  · exact entry_1_12
  · exact entry_1_13
  · exact entry_1_14
  · exact entry_1_15
  · exact entry_1_16
  · exact entry_1_17
  · exact entry_1_18
  · exact entry_1_19
  · exact entry_1_20
  · exact entry_2_0
  · exact entry_2_1
  · exact entry_2_2
  · exact entry_2_3
  · exact entry_2_4
  · exact entry_2_5
  · exact entry_2_6
  · exact entry_2_7
  · exact entry_2_8
  · exact entry_2_9
  · exact entry_2_10
  · exact entry_2_11
  · exact entry_2_12
  · exact entry_2_13
  · exact entry_2_14
  · exact entry_2_15
  · exact entry_2_16
  · exact entry_2_17
  · exact entry_2_18
  · exact entry_2_19
  · exact entry_2_20
  · exact entry_3_0
  · exact entry_3_1
  · exact entry_3_2
  · exact entry_3_3
  · exact entry_3_4
  · exact entry_3_5
  · exact entry_3_6
  · exact entry_3_7
  · exact entry_3_8
  · exact entry_3_9
  · exact entry_3_10
  · exact entry_3_11
  · exact entry_3_12
  · exact entry_3_13
  · exact entry_3_14
  · exact entry_3_15
  · exact entry_3_16
  · exact entry_3_17
  · exact entry_3_18
  · exact entry_3_19
  · exact entry_3_20
  · exact entry_4_0
  · exact entry_4_1
  · exact entry_4_2
  · exact entry_4_3
  · exact entry_4_4
  · exact entry_4_5
  · exact entry_4_6
  · exact entry_4_7
  · exact entry_4_8
  · exact entry_4_9
  · exact entry_4_10
  · exact entry_4_11
  · exact entry_4_12
  · exact entry_4_13
  · exact entry_4_14
  · exact entry_4_15
  · exact entry_4_16
  · exact entry_4_17
  · exact entry_4_18
  · exact entry_4_19
  · exact entry_4_20
  · exact entry_5_0
  · exact entry_5_1
  · exact entry_5_2
  · exact entry_5_3
  · exact entry_5_4
  · exact entry_5_5
  · exact entry_5_6
  · exact entry_5_7
  · exact entry_5_8
  · exact entry_5_9
  · exact entry_5_10
  · exact entry_5_11
  · exact entry_5_12
  · exact entry_5_13
  · exact entry_5_14
  · exact entry_5_15
  · exact entry_5_16
  · exact entry_5_17
  · exact entry_5_18
  · exact entry_5_19
  · exact entry_5_20
  · exact entry_6_0
  · exact entry_6_1
  · exact entry_6_2
  · exact entry_6_3
  · exact entry_6_4
  · exact entry_6_5
  · exact entry_6_6
  · exact entry_6_7
  · exact entry_6_8
  · exact entry_6_9
  · exact entry_6_10
  · exact entry_6_11
  · exact entry_6_12
  · exact entry_6_13
  · exact entry_6_14
  · exact entry_6_15
  · exact entry_6_16
  · exact entry_6_17
  · exact entry_6_18
  · exact entry_6_19
  · exact entry_6_20
  · exact entry_7_0
  · exact entry_7_1
  · exact entry_7_2
  · exact entry_7_3
  · exact entry_7_4
  · exact entry_7_5
  · exact entry_7_6
  · exact entry_7_7
  · exact entry_7_8
  · exact entry_7_9
  · exact entry_7_10
  · exact entry_7_11
  · exact entry_7_12
  · exact entry_7_13
  · exact entry_7_14
  · exact entry_7_15
  · exact entry_7_16
  · exact entry_7_17
  · exact entry_7_18
  · exact entry_7_19
  · exact entry_7_20
  · exact entry_8_0
  · exact entry_8_1
  · exact entry_8_2
  · exact entry_8_3
  · exact entry_8_4
  · exact entry_8_5
  · exact entry_8_6
  · exact entry_8_7
  · exact entry_8_8
  · exact entry_8_9
  · exact entry_8_10
  · exact entry_8_11
  · exact entry_8_12
  · exact entry_8_13
  · exact entry_8_14
  · exact entry_8_15
  · exact entry_8_16
  · exact entry_8_17
  · exact entry_8_18
  · exact entry_8_19
  · exact entry_8_20
  · exact entry_9_0
  · exact entry_9_1
  · exact entry_9_2
  · exact entry_9_3
  · exact entry_9_4
  · exact entry_9_5
  · exact entry_9_6
  · exact entry_9_7
  · exact entry_9_8
  · exact entry_9_9
  · exact entry_9_10
  · exact entry_9_11
  · exact entry_9_12
  · exact entry_9_13
  · exact entry_9_14
  · exact entry_9_15
  · exact entry_9_16
  · exact entry_9_17
  · exact entry_9_18
  · exact entry_9_19
  · exact entry_9_20
  · exact entry_10_0
  · exact entry_10_1
  · exact entry_10_2
  · exact entry_10_3
  · exact entry_10_4
  · exact entry_10_5
  · exact entry_10_6
  · exact entry_10_7
  · exact entry_10_8
  · exact entry_10_9
  · exact entry_10_10
  · exact entry_10_11
  · exact entry_10_12
  · exact entry_10_13
  · exact entry_10_14
  · exact entry_10_15
  · exact entry_10_16
  · exact entry_10_17
  · exact entry_10_18
  · exact entry_10_19
  · exact entry_10_20
  · exact entry_11_0
  · exact entry_11_1
  · exact entry_11_2
  · exact entry_11_3
  · exact entry_11_4
  · exact entry_11_5
  · exact entry_11_6
  · exact entry_11_7
  · exact entry_11_8
  · exact entry_11_9
  · exact entry_11_10
  · exact entry_11_11
  · exact entry_11_12
  · exact entry_11_13
  · exact entry_11_14
  · exact entry_11_15
  · exact entry_11_16
  · exact entry_11_17
  · exact entry_11_18
  · exact entry_11_19
  · exact entry_11_20
  · exact entry_12_0
  · exact entry_12_1
  · exact entry_12_2
  · exact entry_12_3
  · exact entry_12_4
  · exact entry_12_5
  · exact entry_12_6
  · exact entry_12_7
  · exact entry_12_8
  · exact entry_12_9
  · exact entry_12_10
  · exact entry_12_11
  · exact entry_12_12
  · exact entry_12_13
  · exact entry_12_14
  · exact entry_12_15
  · exact entry_12_16
  · exact entry_12_17
  · exact entry_12_18
  · exact entry_12_19
  · exact entry_12_20
  · exact entry_13_0
  · exact entry_13_1
  · exact entry_13_2
  · exact entry_13_3
  · exact entry_13_4
  · exact entry_13_5
  · exact entry_13_6
  · exact entry_13_7
  · exact entry_13_8
  · exact entry_13_9
  · exact entry_13_10
  · exact entry_13_11
  · exact entry_13_12
  · exact entry_13_13
  · exact entry_13_14
  · exact entry_13_15
  · exact entry_13_16
  · exact entry_13_17
  · exact entry_13_18
  · exact entry_13_19
  · exact entry_13_20
  · exact entry_14_0
  · exact entry_14_1
  · exact entry_14_2
  · exact entry_14_3
  · exact entry_14_4
  · exact entry_14_5
  · exact entry_14_6
  · exact entry_14_7
  · exact entry_14_8
  · exact entry_14_9
  · exact entry_14_10
  · exact entry_14_11
  · exact entry_14_12
  · exact entry_14_13
  · exact entry_14_14
  · exact entry_14_15
  · exact entry_14_16
  · exact entry_14_17
  · exact entry_14_18
  · exact entry_14_19
  · exact entry_14_20
  · exact entry_15_0
  · exact entry_15_1
  · exact entry_15_2
  · exact entry_15_3
  · exact entry_15_4
  · exact entry_15_5
  · exact entry_15_6
  · exact entry_15_7
  · exact entry_15_8
  · exact entry_15_9
  · exact entry_15_10
  · exact entry_15_11
  · exact entry_15_12
  · exact entry_15_13
  · exact entry_15_14
  · exact entry_15_15
  · exact entry_15_16
  · exact entry_15_17
  · exact entry_15_18
  · exact entry_15_19
  · exact entry_15_20
  · exact entry_16_0
  · exact entry_16_1
  · exact entry_16_2
  · exact entry_16_3
  · exact entry_16_4
  · exact entry_16_5
  · exact entry_16_6
  · exact entry_16_7
  · exact entry_16_8
  · exact entry_16_9
  · exact entry_16_10
  · exact entry_16_11
  · exact entry_16_12
  · exact entry_16_13
  · exact entry_16_14
  · exact entry_16_15
  · exact entry_16_16
  · exact entry_16_17
  · exact entry_16_18
  · exact entry_16_19
  · exact entry_16_20
  · exact entry_17_0
  · exact entry_17_1
  · exact entry_17_2
  · exact entry_17_3
  · exact entry_17_4
  · exact entry_17_5
  · exact entry_17_6
  · exact entry_17_7
  · exact entry_17_8
  · exact entry_17_9
  · exact entry_17_10
  · exact entry_17_11
  · exact entry_17_12
  · exact entry_17_13
  · exact entry_17_14
  · exact entry_17_15
  · exact entry_17_16
  · exact entry_17_17
  · exact entry_17_18
  · exact entry_17_19
  · exact entry_17_20
  · exact entry_18_0
  · exact entry_18_1
  · exact entry_18_2
  · exact entry_18_3
  · exact entry_18_4
  · exact entry_18_5
  · exact entry_18_6
  · exact entry_18_7
  · exact entry_18_8
  · exact entry_18_9
  · exact entry_18_10
  · exact entry_18_11
  · exact entry_18_12
  · exact entry_18_13
  · exact entry_18_14
  · exact entry_18_15
  · exact entry_18_16
  · exact entry_18_17
  · exact entry_18_18
  · exact entry_18_19
  · exact entry_18_20
  · exact entry_19_0
  · exact entry_19_1
  · exact entry_19_2
  · exact entry_19_3
  · exact entry_19_4
  · exact entry_19_5
  · exact entry_19_6
  · exact entry_19_7
  · exact entry_19_8
  · exact entry_19_9
  · exact entry_19_10
  · exact entry_19_11
  · exact entry_19_12
  · exact entry_19_13
  · exact entry_19_14
  · exact entry_19_15
  · exact entry_19_16
  · exact entry_19_17
  · exact entry_19_18
  · exact entry_19_19
  · exact entry_19_20
  · exact entry_20_0
  · exact entry_20_1
  · exact entry_20_2
  · exact entry_20_3
  · exact entry_20_4
  · exact entry_20_5
  · exact entry_20_6
  · exact entry_20_7
  · exact entry_20_8
  · exact entry_20_9
  · exact entry_20_10
  · exact entry_20_11
  · exact entry_20_12
  · exact entry_20_13
  · exact entry_20_14
  · exact entry_20_15
  · exact entry_20_16
  · exact entry_20_17
  · exact entry_20_18
  · exact entry_20_19
  · exact entry_20_20

theorem positiveDefinite : (realMatrix Z).PosDef :=
  posDef_of_rational_gram Z entries D pivots_pos gram

end MUB6.Certificate.GramData.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_GramNonnegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity of the six literal integer Gram forms and the exact
positive scaling used by the mixed certificate. -/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramNonnegative

theorem quadratic1_nonneg_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ quadratic1 B :=
  GramFunctions.LinearForm.mixedGram_psd_nonneg GramFunctions.Block1.forms B hB
    (realMatrix GramData.Block1.Z) GramData.Block1.positiveDefinite.posSemidef

end MUB6.Certificate.GramNonnegative

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramNonnegative.quadratic1_nonneg_e_oai := @OAI.MUB6.Certificate.GramNonnegative.quadratic1_nonneg_e_oai
