-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:56:44.842165+00:00
-- url     : https://prove2.me/submissions/9594a926-eea2-47ba-9471-f8ae7e62b8aa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval21_6_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17989 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form0 = rawRow17989 := by decide +kernel

theorem rowCheck17989 : row17989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17989 := by decide +kernel

theorem rowEval17989 (x : Key → ℝ) : Integer.Sparse.eval row17989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17989, Integer.Sparse.eval_collectBalanced, rawRowCheck17989]

theorem rawRowCheck17990 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form0 = rawRow17990 := by decide +kernel

theorem rowCheck17990 : row17990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17990 := by decide +kernel

theorem rowEval17990 (x : Key → ℝ) : Integer.Sparse.eval row17990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17990, Integer.Sparse.eval_collectBalanced, rawRowCheck17990]

theorem rawRowCheck17991 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form0 = rawRow17991 := by decide +kernel

theorem rowCheck17991 : row17991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17991 := by decide +kernel

theorem rowEval17991 (x : Key → ℝ) : Integer.Sparse.eval row17991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17991, Integer.Sparse.eval_collectBalanced, rawRowCheck17991]

theorem rawRowCheck17992 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form0 = rawRow17992 := by decide +kernel

theorem rowCheck17992 : row17992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17992 := by decide +kernel

theorem rowEval17992 (x : Key → ℝ) : Integer.Sparse.eval row17992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17992, Integer.Sparse.eval_collectBalanced, rawRowCheck17992]

theorem rawRowCheck17993 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form0 = rawRow17993 := by decide +kernel

theorem rowCheck17993 : row17993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17993 := by decide +kernel

theorem rowEval17993 (x : Key → ℝ) : Integer.Sparse.eval row17993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17993, Integer.Sparse.eval_collectBalanced, rawRowCheck17993]

theorem rawRowCheck17994 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form0 = rawRow17994 := by decide +kernel

theorem rowCheck17994 : row17994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17994 := by decide +kernel

theorem rowEval17994 (x : Key → ℝ) : Integer.Sparse.eval row17994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17994, Integer.Sparse.eval_collectBalanced, rawRowCheck17994]

theorem rawRowCheck17995 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form0 = rawRow17995 := by decide +kernel

theorem rowCheck17995 : row17995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17995 := by decide +kernel

theorem rowEval17995 (x : Key → ℝ) : Integer.Sparse.eval row17995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17995, Integer.Sparse.eval_collectBalanced, rawRowCheck17995]

theorem rawRowCheck17996 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form0 = rawRow17996 := by decide +kernel

theorem rowCheck17996 : row17996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17996 := by decide +kernel

theorem rowEval17996 (x : Key → ℝ) : Integer.Sparse.eval row17996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17996, Integer.Sparse.eval_collectBalanced, rawRowCheck17996]

theorem rawRowCheck17997 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form0 = rawRow17997 := by decide +kernel

theorem rowCheck17997 : row17997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17997 := by decide +kernel

theorem rowEval17997 (x : Key → ℝ) : Integer.Sparse.eval row17997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17997, Integer.Sparse.eval_collectBalanced, rawRowCheck17997]

theorem rawRowCheck17998 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow17998 := by decide +kernel

theorem rowCheck17998 : row17998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17998 := by decide +kernel

theorem rowEval17998 (x : Key → ℝ) : Integer.Sparse.eval row17998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17998, Integer.Sparse.eval_collectBalanced, rawRowCheck17998]

theorem rawRowCheck17999 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow17999 := by decide +kernel

theorem rowCheck17999 : row17999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17999 := by decide +kernel

theorem rowEval17999 (x : Key → ℝ) : Integer.Sparse.eval row17999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17999, Integer.Sparse.eval_collectBalanced, rawRowCheck17999]

theorem rawRowCheck18000 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow18000 := by decide +kernel

theorem rowCheck18000 : row18000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18000 := by decide +kernel

theorem rowEval18000 (x : Key → ℝ) : Integer.Sparse.eval row18000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18000, Integer.Sparse.eval_collectBalanced, rawRowCheck18000]

theorem rawRowCheck18001 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form0 = rawRow18001 := by decide +kernel

theorem rowCheck18001 : row18001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18001 := by decide +kernel

theorem rowEval18001 (x : Key → ℝ) : Integer.Sparse.eval row18001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18001, Integer.Sparse.eval_collectBalanced, rawRowCheck18001]

theorem rawRowCheck18002 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form0 = rawRow18002 := by decide +kernel

theorem rowCheck18002 : row18002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18002 := by decide +kernel

theorem rowEval18002 (x : Key → ℝ) : Integer.Sparse.eval row18002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18002, Integer.Sparse.eval_collectBalanced, rawRowCheck18002]

theorem rawRowCheck18003 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form0 = rawRow18003 := by decide +kernel

theorem rowCheck18003 : row18003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18003 := by decide +kernel

theorem rowEval18003 (x : Key → ℝ) : Integer.Sparse.eval row18003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18003, Integer.Sparse.eval_collectBalanced, rawRowCheck18003]

theorem rawRowCheck18004 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form0 = rawRow18004 := by decide +kernel

theorem rowCheck18004 : row18004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18004 := by decide +kernel

theorem rowEval18004 (x : Key → ℝ) : Integer.Sparse.eval row18004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18004, Integer.Sparse.eval_collectBalanced, rawRowCheck18004]

theorem rawRowCheck18005 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow18005 := by decide +kernel

theorem rowCheck18005 : row18005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18005 := by decide +kernel

theorem rowEval18005 (x : Key → ℝ) : Integer.Sparse.eval row18005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck18005, Integer.Sparse.eval_collectBalanced, rawRowCheck18005]

theorem rawRowCheck18006 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow18006 := by decide +kernel

theorem rowCheck18006 : row18006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18006 := by decide +kernel

theorem rowEval18006 (x : Key → ℝ) : Integer.Sparse.eval row18006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18006, Integer.Sparse.eval_collectBalanced, rawRowCheck18006]

theorem rawRowCheck18007 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow18007 := by decide +kernel

theorem rowCheck18007 : row18007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18007 := by decide +kernel

theorem rowEval18007 (x : Key → ℝ) : Integer.Sparse.eval row18007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18007, Integer.Sparse.eval_collectBalanced, rawRowCheck18007]

theorem rawRowCheck18008 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow18008 := by decide +kernel

theorem rowCheck18008 : row18008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18008 := by decide +kernel

theorem rowEval18008 (x : Key → ℝ) : Integer.Sparse.eval row18008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18008, Integer.Sparse.eval_collectBalanced, rawRowCheck18008]

theorem rawRowCheck18009 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form1 = rawRow18009 := by decide +kernel

theorem rowCheck18009 : row18009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18009 := by decide +kernel

theorem rowEval18009 (x : Key → ℝ) : Integer.Sparse.eval row18009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18009, Integer.Sparse.eval_collectBalanced, rawRowCheck18009]

theorem rawRowCheck18010 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form1 = rawRow18010 := by decide +kernel

theorem rowCheck18010 : row18010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18010 := by decide +kernel

theorem rowEval18010 (x : Key → ℝ) : Integer.Sparse.eval row18010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18010, Integer.Sparse.eval_collectBalanced, rawRowCheck18010]

theorem rawRowCheck18011 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form1 = rawRow18011 := by decide +kernel

theorem rowCheck18011 : row18011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18011 := by decide +kernel

theorem rowEval18011 (x : Key → ℝ) : Integer.Sparse.eval row18011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18011, Integer.Sparse.eval_collectBalanced, rawRowCheck18011]

theorem rawRowCheck18012 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form1 = rawRow18012 := by decide +kernel

theorem rowCheck18012 : row18012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18012 := by decide +kernel

theorem rowEval18012 (x : Key → ℝ) : Integer.Sparse.eval row18012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18012, Integer.Sparse.eval_collectBalanced, rawRowCheck18012]

theorem rawRowCheck18013 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form1 = rawRow18013 := by decide +kernel

theorem rowCheck18013 : row18013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18013 := by decide +kernel

theorem rowEval18013 (x : Key → ℝ) : Integer.Sparse.eval row18013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18013, Integer.Sparse.eval_collectBalanced, rawRowCheck18013]

theorem rawRowCheck18014 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form1 = rawRow18014 := by decide +kernel

theorem rowCheck18014 : row18014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18014 := by decide +kernel

theorem rowEval18014 (x : Key → ℝ) : Integer.Sparse.eval row18014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18014, Integer.Sparse.eval_collectBalanced, rawRowCheck18014]

theorem rawRowCheck18015 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form1 = rawRow18015 := by decide +kernel

theorem rowCheck18015 : row18015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18015 := by decide +kernel

theorem rowEval18015 (x : Key → ℝ) : Integer.Sparse.eval row18015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18015, Integer.Sparse.eval_collectBalanced, rawRowCheck18015]

theorem rawRowCheck18016 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form1 = rawRow18016 := by decide +kernel

theorem rowCheck18016 : row18016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18016 := by decide +kernel

theorem rowEval18016 (x : Key → ℝ) : Integer.Sparse.eval row18016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18016, Integer.Sparse.eval_collectBalanced, rawRowCheck18016]

theorem rawRowCheck18017 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form1 = rawRow18017 := by decide +kernel

theorem rowCheck18017 : row18017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18017 := by decide +kernel

theorem rowEval18017 (x : Key → ℝ) : Integer.Sparse.eval row18017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18017, Integer.Sparse.eval_collectBalanced, rawRowCheck18017]

theorem rawRowCheck18018 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow18018 := by decide +kernel

theorem rowCheck18018 : row18018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18018 := by decide +kernel

theorem rowEval18018 (x : Key → ℝ) : Integer.Sparse.eval row18018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18018, Integer.Sparse.eval_collectBalanced, rawRowCheck18018]

theorem rawRowCheck18019 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow18019 := by decide +kernel

theorem rowCheck18019 : row18019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18019 := by decide +kernel

theorem rowEval18019 (x : Key → ℝ) : Integer.Sparse.eval row18019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18019, Integer.Sparse.eval_collectBalanced, rawRowCheck18019]

theorem rawRowCheck18020 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow18020 := by decide +kernel

theorem rowCheck18020 : row18020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18020 := by decide +kernel

theorem rowEval18020 (x : Key → ℝ) : Integer.Sparse.eval row18020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18020, Integer.Sparse.eval_collectBalanced, rawRowCheck18020]

theorem rawRowCheck18021 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form1 = rawRow18021 := by decide +kernel

theorem rowCheck18021 : row18021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18021 := by decide +kernel

theorem rowEval18021 (x : Key → ℝ) : Integer.Sparse.eval row18021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18021, Integer.Sparse.eval_collectBalanced, rawRowCheck18021]

theorem rawRowCheck18022 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form1 = rawRow18022 := by decide +kernel

theorem rowCheck18022 : row18022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18022 := by decide +kernel

theorem rowEval18022 (x : Key → ℝ) : Integer.Sparse.eval row18022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18022, Integer.Sparse.eval_collectBalanced, rawRowCheck18022]

theorem rawRowCheck18023 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form1 = rawRow18023 := by decide +kernel

theorem rowCheck18023 : row18023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18023 := by decide +kernel

theorem rowEval18023 (x : Key → ℝ) : Integer.Sparse.eval row18023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18023, Integer.Sparse.eval_collectBalanced, rawRowCheck18023]

theorem rawRowCheck18024 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form1 = rawRow18024 := by decide +kernel

theorem rowCheck18024 : row18024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18024 := by decide +kernel

theorem rowEval18024 (x : Key → ℝ) : Integer.Sparse.eval row18024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18024, Integer.Sparse.eval_collectBalanced, rawRowCheck18024]

theorem rawRowCheck18025 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow18025 := by decide +kernel

theorem rowCheck18025 : row18025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18025 := by decide +kernel

theorem rowEval18025 (x : Key → ℝ) : Integer.Sparse.eval row18025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18025, Integer.Sparse.eval_collectBalanced, rawRowCheck18025]

theorem rawRowCheck18026 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow18026 := by decide +kernel

theorem rowCheck18026 : row18026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18026 := by decide +kernel

theorem rowEval18026 (x : Key → ℝ) : Integer.Sparse.eval row18026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18026, Integer.Sparse.eval_collectBalanced, rawRowCheck18026]

theorem rawRowCheck18027 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow18027 := by decide +kernel

theorem rowCheck18027 : row18027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18027 := by decide +kernel

theorem rowEval18027 (x : Key → ℝ) : Integer.Sparse.eval row18027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18027, Integer.Sparse.eval_collectBalanced, rawRowCheck18027]

theorem rawRowCheck18028 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow18028 := by decide +kernel

theorem rowCheck18028 : row18028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18028 := by decide +kernel

theorem rowEval18028 (x : Key → ℝ) : Integer.Sparse.eval row18028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18028, Integer.Sparse.eval_collectBalanced, rawRowCheck18028]

theorem rawRowCheck18029 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form2 = rawRow18029 := by decide +kernel

theorem rowCheck18029 : row18029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18029 := by decide +kernel

theorem rowEval18029 (x : Key → ℝ) : Integer.Sparse.eval row18029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18029, Integer.Sparse.eval_collectBalanced, rawRowCheck18029]

theorem rawRowCheck18030 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form2 = rawRow18030 := by decide +kernel

theorem rowCheck18030 : row18030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18030 := by decide +kernel

theorem rowEval18030 (x : Key → ℝ) : Integer.Sparse.eval row18030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18030, Integer.Sparse.eval_collectBalanced, rawRowCheck18030]

theorem rawRowCheck18031 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form2 = rawRow18031 := by decide +kernel

theorem rowCheck18031 : row18031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18031 := by decide +kernel

theorem rowEval18031 (x : Key → ℝ) : Integer.Sparse.eval row18031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18031, Integer.Sparse.eval_collectBalanced, rawRowCheck18031]

theorem rawRowCheck18032 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form2 = rawRow18032 := by decide +kernel

theorem rowCheck18032 : row18032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18032 := by decide +kernel

theorem rowEval18032 (x : Key → ℝ) : Integer.Sparse.eval row18032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18032, Integer.Sparse.eval_collectBalanced, rawRowCheck18032]

theorem rawRowCheck18033 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form2 = rawRow18033 := by decide +kernel

theorem rowCheck18033 : row18033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18033 := by decide +kernel

theorem rowEval18033 (x : Key → ℝ) : Integer.Sparse.eval row18033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18033, Integer.Sparse.eval_collectBalanced, rawRowCheck18033]

theorem rawRowCheck18034 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form2 = rawRow18034 := by decide +kernel

theorem rowCheck18034 : row18034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18034 := by decide +kernel

theorem rowEval18034 (x : Key → ℝ) : Integer.Sparse.eval row18034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18034, Integer.Sparse.eval_collectBalanced, rawRowCheck18034]

theorem rawRowCheck18035 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form2 = rawRow18035 := by decide +kernel

theorem rowCheck18035 : row18035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18035 := by decide +kernel

theorem rowEval18035 (x : Key → ℝ) : Integer.Sparse.eval row18035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18035, Integer.Sparse.eval_collectBalanced, rawRowCheck18035]

theorem rawRowCheck18036 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form2 = rawRow18036 := by decide +kernel

theorem rowCheck18036 : row18036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18036 := by decide +kernel

theorem rowEval18036 (x : Key → ℝ) : Integer.Sparse.eval row18036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18036, Integer.Sparse.eval_collectBalanced, rawRowCheck18036]

theorem rawRowCheck18037 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form2 = rawRow18037 := by decide +kernel

theorem rowCheck18037 : row18037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18037 := by decide +kernel

theorem rowEval18037 (x : Key → ℝ) : Integer.Sparse.eval row18037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18037, Integer.Sparse.eval_collectBalanced, rawRowCheck18037]

theorem rawRowCheck18038 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow18038 := by decide +kernel

theorem rowCheck18038 : row18038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18038 := by decide +kernel

theorem rowEval18038 (x : Key → ℝ) : Integer.Sparse.eval row18038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18038, Integer.Sparse.eval_collectBalanced, rawRowCheck18038]

theorem rawRowCheck18039 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow18039 := by decide +kernel

theorem rowCheck18039 : row18039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18039 := by decide +kernel

theorem rowEval18039 (x : Key → ℝ) : Integer.Sparse.eval row18039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18039, Integer.Sparse.eval_collectBalanced, rawRowCheck18039]

theorem rawRowCheck18040 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow18040 := by decide +kernel

theorem rowCheck18040 : row18040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18040 := by decide +kernel

theorem rowEval18040 (x : Key → ℝ) : Integer.Sparse.eval row18040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18040, Integer.Sparse.eval_collectBalanced, rawRowCheck18040]

theorem rawRowCheck18041 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form2 = rawRow18041 := by decide +kernel

theorem rowCheck18041 : row18041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18041 := by decide +kernel

theorem rowEval18041 (x : Key → ℝ) : Integer.Sparse.eval row18041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18041, Integer.Sparse.eval_collectBalanced, rawRowCheck18041]

theorem rawRowCheck18042 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form2 = rawRow18042 := by decide +kernel

theorem rowCheck18042 : row18042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18042 := by decide +kernel

theorem rowEval18042 (x : Key → ℝ) : Integer.Sparse.eval row18042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18042, Integer.Sparse.eval_collectBalanced, rawRowCheck18042]

theorem rawRowCheck18043 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form2 = rawRow18043 := by decide +kernel

theorem rowCheck18043 : row18043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18043 := by decide +kernel

theorem rowEval18043 (x : Key → ℝ) : Integer.Sparse.eval row18043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18043, Integer.Sparse.eval_collectBalanced, rawRowCheck18043]

theorem rawRowCheck18044 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form2 = rawRow18044 := by decide +kernel

theorem rowCheck18044 : row18044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18044 := by decide +kernel

theorem rowEval18044 (x : Key → ℝ) : Integer.Sparse.eval row18044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18044, Integer.Sparse.eval_collectBalanced, rawRowCheck18044]

theorem rawRowCheck18045 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow18045 := by decide +kernel

theorem rowCheck18045 : row18045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18045 := by decide +kernel

theorem rowEval18045 (x : Key → ℝ) : Integer.Sparse.eval row18045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18045, Integer.Sparse.eval_collectBalanced, rawRowCheck18045]

theorem rawRowCheck18046 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow18046 := by decide +kernel

theorem rowCheck18046 : row18046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18046 := by decide +kernel

theorem rowEval18046 (x : Key → ℝ) : Integer.Sparse.eval row18046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18046, Integer.Sparse.eval_collectBalanced, rawRowCheck18046]

theorem rawRowCheck18047 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow18047 := by decide +kernel

theorem rowCheck18047 : row18047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18047 := by decide +kernel

theorem rowEval18047 (x : Key → ℝ) : Integer.Sparse.eval row18047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18047, Integer.Sparse.eval_collectBalanced, rawRowCheck18047]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18048 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow18048 := by decide +kernel

theorem rowCheck18048 : row18048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18048 := by decide +kernel

theorem rowEval18048 (x : Key → ℝ) : Integer.Sparse.eval row18048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18048, Integer.Sparse.eval_collectBalanced, rawRowCheck18048]

theorem rawRowCheck18049 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form3 = rawRow18049 := by decide +kernel

theorem rowCheck18049 : row18049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18049 := by decide +kernel

theorem rowEval18049 (x : Key → ℝ) : Integer.Sparse.eval row18049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18049, Integer.Sparse.eval_collectBalanced, rawRowCheck18049]

theorem rawRowCheck18050 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form3 = rawRow18050 := by decide +kernel

theorem rowCheck18050 : row18050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18050 := by decide +kernel

theorem rowEval18050 (x : Key → ℝ) : Integer.Sparse.eval row18050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18050, Integer.Sparse.eval_collectBalanced, rawRowCheck18050]

theorem rawRowCheck18051 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form3 = rawRow18051 := by decide +kernel

theorem rowCheck18051 : row18051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18051 := by decide +kernel

theorem rowEval18051 (x : Key → ℝ) : Integer.Sparse.eval row18051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18051, Integer.Sparse.eval_collectBalanced, rawRowCheck18051]

theorem rawRowCheck18052 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form3 = rawRow18052 := by decide +kernel

theorem rowCheck18052 : row18052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18052 := by decide +kernel

theorem rowEval18052 (x : Key → ℝ) : Integer.Sparse.eval row18052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18052, Integer.Sparse.eval_collectBalanced, rawRowCheck18052]

theorem rawRowCheck18053 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form3 = rawRow18053 := by decide +kernel

theorem rowCheck18053 : row18053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18053 := by decide +kernel

theorem rowEval18053 (x : Key → ℝ) : Integer.Sparse.eval row18053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18053, Integer.Sparse.eval_collectBalanced, rawRowCheck18053]

theorem rawRowCheck18054 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form3 = rawRow18054 := by decide +kernel

theorem rowCheck18054 : row18054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18054 := by decide +kernel

theorem rowEval18054 (x : Key → ℝ) : Integer.Sparse.eval row18054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18054, Integer.Sparse.eval_collectBalanced, rawRowCheck18054]

theorem rawRowCheck18055 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form3 = rawRow18055 := by decide +kernel

theorem rowCheck18055 : row18055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18055 := by decide +kernel

theorem rowEval18055 (x : Key → ℝ) : Integer.Sparse.eval row18055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18055, Integer.Sparse.eval_collectBalanced, rawRowCheck18055]

theorem rawRowCheck18056 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form3 = rawRow18056 := by decide +kernel

theorem rowCheck18056 : row18056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18056 := by decide +kernel

theorem rowEval18056 (x : Key → ℝ) : Integer.Sparse.eval row18056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18056, Integer.Sparse.eval_collectBalanced, rawRowCheck18056]

theorem rawRowCheck18057 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form3 = rawRow18057 := by decide +kernel

theorem rowCheck18057 : row18057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18057 := by decide +kernel

theorem rowEval18057 (x : Key → ℝ) : Integer.Sparse.eval row18057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18057, Integer.Sparse.eval_collectBalanced, rawRowCheck18057]

theorem rawRowCheck18058 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow18058 := by decide +kernel

theorem rowCheck18058 : row18058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18058 := by decide +kernel

theorem rowEval18058 (x : Key → ℝ) : Integer.Sparse.eval row18058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18058, Integer.Sparse.eval_collectBalanced, rawRowCheck18058]

theorem rawRowCheck18059 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow18059 := by decide +kernel

theorem rowCheck18059 : row18059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18059 := by decide +kernel

theorem rowEval18059 (x : Key → ℝ) : Integer.Sparse.eval row18059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18059, Integer.Sparse.eval_collectBalanced, rawRowCheck18059]

theorem rawRowCheck18060 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow18060 := by decide +kernel

theorem rowCheck18060 : row18060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18060 := by decide +kernel

theorem rowEval18060 (x : Key → ℝ) : Integer.Sparse.eval row18060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18060, Integer.Sparse.eval_collectBalanced, rawRowCheck18060]

theorem rawRowCheck18061 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form3 = rawRow18061 := by decide +kernel

theorem rowCheck18061 : row18061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18061 := by decide +kernel

theorem rowEval18061 (x : Key → ℝ) : Integer.Sparse.eval row18061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18061, Integer.Sparse.eval_collectBalanced, rawRowCheck18061]

theorem rawRowCheck18062 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form3 = rawRow18062 := by decide +kernel

theorem rowCheck18062 : row18062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18062 := by decide +kernel

theorem rowEval18062 (x : Key → ℝ) : Integer.Sparse.eval row18062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18062, Integer.Sparse.eval_collectBalanced, rawRowCheck18062]

theorem rawRowCheck18063 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form3 = rawRow18063 := by decide +kernel

theorem rowCheck18063 : row18063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18063 := by decide +kernel

theorem rowEval18063 (x : Key → ℝ) : Integer.Sparse.eval row18063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18063, Integer.Sparse.eval_collectBalanced, rawRowCheck18063]

theorem rawRowCheck18064 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form3 = rawRow18064 := by decide +kernel

theorem rowCheck18064 : row18064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18064 := by decide +kernel

theorem rowEval18064 (x : Key → ℝ) : Integer.Sparse.eval row18064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18064, Integer.Sparse.eval_collectBalanced, rawRowCheck18064]

theorem rawRowCheck18065 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow18065 := by decide +kernel

theorem rowCheck18065 : row18065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18065 := by decide +kernel

theorem rowEval18065 (x : Key → ℝ) : Integer.Sparse.eval row18065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18065, Integer.Sparse.eval_collectBalanced, rawRowCheck18065]

theorem rawRowCheck18066 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow18066 := by decide +kernel

theorem rowCheck18066 : row18066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18066 := by decide +kernel

theorem rowEval18066 (x : Key → ℝ) : Integer.Sparse.eval row18066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18066, Integer.Sparse.eval_collectBalanced, rawRowCheck18066]

theorem rawRowCheck18067 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow18067 := by decide +kernel

theorem rowCheck18067 : row18067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18067 := by decide +kernel

theorem rowEval18067 (x : Key → ℝ) : Integer.Sparse.eval row18067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18067, Integer.Sparse.eval_collectBalanced, rawRowCheck18067]

theorem rawRowCheck18068 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow18068 := by decide +kernel

theorem rowCheck18068 : row18068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18068 := by decide +kernel

theorem rowEval18068 (x : Key → ℝ) : Integer.Sparse.eval row18068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18068, Integer.Sparse.eval_collectBalanced, rawRowCheck18068]

theorem rawRowCheck18069 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form4 = rawRow18069 := by decide +kernel

theorem rowCheck18069 : row18069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18069 := by decide +kernel

theorem rowEval18069 (x : Key → ℝ) : Integer.Sparse.eval row18069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18069, Integer.Sparse.eval_collectBalanced, rawRowCheck18069]

theorem rawRowCheck18070 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form4 = rawRow18070 := by decide +kernel

theorem rowCheck18070 : row18070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18070 := by decide +kernel

theorem rowEval18070 (x : Key → ℝ) : Integer.Sparse.eval row18070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18070, Integer.Sparse.eval_collectBalanced, rawRowCheck18070]

theorem rawRowCheck18071 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form4 = rawRow18071 := by decide +kernel

theorem rowCheck18071 : row18071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18071 := by decide +kernel

theorem rowEval18071 (x : Key → ℝ) : Integer.Sparse.eval row18071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18071, Integer.Sparse.eval_collectBalanced, rawRowCheck18071]

theorem rawRowCheck18072 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form4 = rawRow18072 := by decide +kernel

theorem rowCheck18072 : row18072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18072 := by decide +kernel

theorem rowEval18072 (x : Key → ℝ) : Integer.Sparse.eval row18072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18072, Integer.Sparse.eval_collectBalanced, rawRowCheck18072]

theorem rawRowCheck18073 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form4 = rawRow18073 := by decide +kernel

theorem rowCheck18073 : row18073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18073 := by decide +kernel

theorem rowEval18073 (x : Key → ℝ) : Integer.Sparse.eval row18073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18073, Integer.Sparse.eval_collectBalanced, rawRowCheck18073]

theorem rawRowCheck18074 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form4 = rawRow18074 := by decide +kernel

theorem rowCheck18074 : row18074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18074 := by decide +kernel

theorem rowEval18074 (x : Key → ℝ) : Integer.Sparse.eval row18074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18074, Integer.Sparse.eval_collectBalanced, rawRowCheck18074]

theorem rawRowCheck18075 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form4 = rawRow18075 := by decide +kernel

theorem rowCheck18075 : row18075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18075 := by decide +kernel

theorem rowEval18075 (x : Key → ℝ) : Integer.Sparse.eval row18075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18075, Integer.Sparse.eval_collectBalanced, rawRowCheck18075]

theorem rawRowCheck18076 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form4 = rawRow18076 := by decide +kernel

theorem rowCheck18076 : row18076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18076 := by decide +kernel

theorem rowEval18076 (x : Key → ℝ) : Integer.Sparse.eval row18076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18076, Integer.Sparse.eval_collectBalanced, rawRowCheck18076]

theorem rawRowCheck18077 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form4 = rawRow18077 := by decide +kernel

theorem rowCheck18077 : row18077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18077 := by decide +kernel

theorem rowEval18077 (x : Key → ℝ) : Integer.Sparse.eval row18077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18077, Integer.Sparse.eval_collectBalanced, rawRowCheck18077]

theorem rawRowCheck18078 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow18078 := by decide +kernel

theorem rowCheck18078 : row18078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18078 := by decide +kernel

theorem rowEval18078 (x : Key → ℝ) : Integer.Sparse.eval row18078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18078, Integer.Sparse.eval_collectBalanced, rawRowCheck18078]

theorem rawRowCheck18079 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow18079 := by decide +kernel

theorem rowCheck18079 : row18079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18079 := by decide +kernel

theorem rowEval18079 (x : Key → ℝ) : Integer.Sparse.eval row18079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18079, Integer.Sparse.eval_collectBalanced, rawRowCheck18079]

theorem rawRowCheck18080 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow18080 := by decide +kernel

theorem rowCheck18080 : row18080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18080 := by decide +kernel

theorem rowEval18080 (x : Key → ℝ) : Integer.Sparse.eval row18080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18080, Integer.Sparse.eval_collectBalanced, rawRowCheck18080]

theorem rawRowCheck18081 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form4 = rawRow18081 := by decide +kernel

theorem rowCheck18081 : row18081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18081 := by decide +kernel

theorem rowEval18081 (x : Key → ℝ) : Integer.Sparse.eval row18081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18081, Integer.Sparse.eval_collectBalanced, rawRowCheck18081]

theorem rawRowCheck18082 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form4 = rawRow18082 := by decide +kernel

theorem rowCheck18082 : row18082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18082 := by decide +kernel

theorem rowEval18082 (x : Key → ℝ) : Integer.Sparse.eval row18082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18082, Integer.Sparse.eval_collectBalanced, rawRowCheck18082]

theorem rawRowCheck18083 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form4 = rawRow18083 := by decide +kernel

theorem rowCheck18083 : row18083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18083 := by decide +kernel

theorem rowEval18083 (x : Key → ℝ) : Integer.Sparse.eval row18083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18083, Integer.Sparse.eval_collectBalanced, rawRowCheck18083]

theorem rawRowCheck18084 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form4 = rawRow18084 := by decide +kernel

theorem rowCheck18084 : row18084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18084 := by decide +kernel

theorem rowEval18084 (x : Key → ℝ) : Integer.Sparse.eval row18084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18084, Integer.Sparse.eval_collectBalanced, rawRowCheck18084]

theorem rawRowCheck18085 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow18085 := by decide +kernel

theorem rowCheck18085 : row18085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18085 := by decide +kernel

theorem rowEval18085 (x : Key → ℝ) : Integer.Sparse.eval row18085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18085, Integer.Sparse.eval_collectBalanced, rawRowCheck18085]

theorem rawRowCheck18086 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow18086 := by decide +kernel

theorem rowCheck18086 : row18086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18086 := by decide +kernel

theorem rowEval18086 (x : Key → ℝ) : Integer.Sparse.eval row18086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18086, Integer.Sparse.eval_collectBalanced, rawRowCheck18086]

theorem rawRowCheck18087 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow18087 := by decide +kernel

theorem rowCheck18087 : row18087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18087 := by decide +kernel

theorem rowEval18087 (x : Key → ℝ) : Integer.Sparse.eval row18087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18087, Integer.Sparse.eval_collectBalanced, rawRowCheck18087]

theorem rawRowCheck18088 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow18088 := by decide +kernel

theorem rowCheck18088 : row18088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18088 := by decide +kernel

theorem rowEval18088 (x : Key → ℝ) : Integer.Sparse.eval row18088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18088, Integer.Sparse.eval_collectBalanced, rawRowCheck18088]

theorem rawRowCheck18089 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form5 = rawRow18089 := by decide +kernel

theorem rowCheck18089 : row18089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18089 := by decide +kernel

theorem rowEval18089 (x : Key → ℝ) : Integer.Sparse.eval row18089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18089, Integer.Sparse.eval_collectBalanced, rawRowCheck18089]

theorem rawRowCheck18090 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form5 = rawRow18090 := by decide +kernel

theorem rowCheck18090 : row18090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18090 := by decide +kernel

theorem rowEval18090 (x : Key → ℝ) : Integer.Sparse.eval row18090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18090, Integer.Sparse.eval_collectBalanced, rawRowCheck18090]

theorem rawRowCheck18091 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form5 = rawRow18091 := by decide +kernel

theorem rowCheck18091 : row18091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18091 := by decide +kernel

theorem rowEval18091 (x : Key → ℝ) : Integer.Sparse.eval row18091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18091, Integer.Sparse.eval_collectBalanced, rawRowCheck18091]

theorem rawRowCheck18092 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form5 = rawRow18092 := by decide +kernel

theorem rowCheck18092 : row18092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18092 := by decide +kernel

theorem rowEval18092 (x : Key → ℝ) : Integer.Sparse.eval row18092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18092, Integer.Sparse.eval_collectBalanced, rawRowCheck18092]

theorem rawRowCheck18093 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form5 = rawRow18093 := by decide +kernel

theorem rowCheck18093 : row18093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18093 := by decide +kernel

theorem rowEval18093 (x : Key → ℝ) : Integer.Sparse.eval row18093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18093, Integer.Sparse.eval_collectBalanced, rawRowCheck18093]

theorem rawRowCheck18094 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form5 = rawRow18094 := by decide +kernel

theorem rowCheck18094 : row18094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18094 := by decide +kernel

theorem rowEval18094 (x : Key → ℝ) : Integer.Sparse.eval row18094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18094, Integer.Sparse.eval_collectBalanced, rawRowCheck18094]

theorem rawRowCheck18095 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form5 = rawRow18095 := by decide +kernel

theorem rowCheck18095 : row18095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18095 := by decide +kernel

theorem rowEval18095 (x : Key → ℝ) : Integer.Sparse.eval row18095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18095, Integer.Sparse.eval_collectBalanced, rawRowCheck18095]

theorem rawRowCheck18096 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form5 = rawRow18096 := by decide +kernel

theorem rowCheck18096 : row18096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18096 := by decide +kernel

theorem rowEval18096 (x : Key → ℝ) : Integer.Sparse.eval row18096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18096, Integer.Sparse.eval_collectBalanced, rawRowCheck18096]

theorem rawRowCheck18097 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form5 = rawRow18097 := by decide +kernel

theorem rowCheck18097 : row18097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18097 := by decide +kernel

theorem rowEval18097 (x : Key → ℝ) : Integer.Sparse.eval row18097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18097, Integer.Sparse.eval_collectBalanced, rawRowCheck18097]

theorem rawRowCheck18098 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow18098 := by decide +kernel

theorem rowCheck18098 : row18098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18098 := by decide +kernel

theorem rowEval18098 (x : Key → ℝ) : Integer.Sparse.eval row18098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18098, Integer.Sparse.eval_collectBalanced, rawRowCheck18098]

theorem rawRowCheck18099 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow18099 := by decide +kernel

theorem rowCheck18099 : row18099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18099 := by decide +kernel

theorem rowEval18099 (x : Key → ℝ) : Integer.Sparse.eval row18099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18099, Integer.Sparse.eval_collectBalanced, rawRowCheck18099]

theorem rawRowCheck18100 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow18100 := by decide +kernel

theorem rowCheck18100 : row18100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18100 := by decide +kernel

theorem rowEval18100 (x : Key → ℝ) : Integer.Sparse.eval row18100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18100, Integer.Sparse.eval_collectBalanced, rawRowCheck18100]

theorem rawRowCheck18101 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form5 = rawRow18101 := by decide +kernel

theorem rowCheck18101 : row18101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18101 := by decide +kernel

theorem rowEval18101 (x : Key → ℝ) : Integer.Sparse.eval row18101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18101, Integer.Sparse.eval_collectBalanced, rawRowCheck18101]

theorem rawRowCheck18102 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form5 = rawRow18102 := by decide +kernel

theorem rowCheck18102 : row18102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18102 := by decide +kernel

theorem rowEval18102 (x : Key → ℝ) : Integer.Sparse.eval row18102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18102, Integer.Sparse.eval_collectBalanced, rawRowCheck18102]

theorem rawRowCheck18103 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form5 = rawRow18103 := by decide +kernel

theorem rowCheck18103 : row18103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18103 := by decide +kernel

theorem rowEval18103 (x : Key → ℝ) : Integer.Sparse.eval row18103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18103, Integer.Sparse.eval_collectBalanced, rawRowCheck18103]

theorem rawRowCheck18104 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form5 = rawRow18104 := by decide +kernel

theorem rowCheck18104 : row18104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18104 := by decide +kernel

theorem rowEval18104 (x : Key → ℝ) : Integer.Sparse.eval row18104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18104, Integer.Sparse.eval_collectBalanced, rawRowCheck18104]

theorem rawRowCheck18105 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow18105 := by decide +kernel

theorem rowCheck18105 : row18105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18105 := by decide +kernel

theorem rowEval18105 (x : Key → ℝ) : Integer.Sparse.eval row18105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18105, Integer.Sparse.eval_collectBalanced, rawRowCheck18105]

theorem rawRowCheck18106 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow18106 := by decide +kernel

theorem rowCheck18106 : row18106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18106 := by decide +kernel

theorem rowEval18106 (x : Key → ℝ) : Integer.Sparse.eval row18106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18106, Integer.Sparse.eval_collectBalanced, rawRowCheck18106]

theorem rawRowCheck18107 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow18107 := by decide +kernel

theorem rowCheck18107 : row18107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18107 := by decide +kernel

theorem rowEval18107 (x : Key → ℝ) : Integer.Sparse.eval row18107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18107, Integer.Sparse.eval_collectBalanced, rawRowCheck18107]

theorem rawRowCheck18108 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow18108 := by decide +kernel

theorem rowCheck18108 : row18108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18108 := by decide +kernel

theorem rowEval18108 (x : Key → ℝ) : Integer.Sparse.eval row18108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18108, Integer.Sparse.eval_collectBalanced, rawRowCheck18108]

theorem rawRowCheck18129 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form7 = rawRow18129 := by decide +kernel

theorem rowCheck18129 : row18129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18129 := by decide +kernel

theorem rowEval18129 (x : Key → ℝ) : Integer.Sparse.eval row18129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18129, Integer.Sparse.eval_collectBalanced, rawRowCheck18129]

theorem rawRowCheck18130 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form7 = rawRow18130 := by decide +kernel

theorem rowCheck18130 : row18130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18130 := by decide +kernel

theorem rowEval18130 (x : Key → ℝ) : Integer.Sparse.eval row18130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18130, Integer.Sparse.eval_collectBalanced, rawRowCheck18130]

theorem rawRowCheck18131 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form7 = rawRow18131 := by decide +kernel

theorem rowCheck18131 : row18131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18131 := by decide +kernel

theorem rowEval18131 (x : Key → ℝ) : Integer.Sparse.eval row18131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18131, Integer.Sparse.eval_collectBalanced, rawRowCheck18131]

theorem rawRowCheck18132 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form7 = rawRow18132 := by decide +kernel

theorem rowCheck18132 : row18132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18132 := by decide +kernel

theorem rowEval18132 (x : Key → ℝ) : Integer.Sparse.eval row18132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18132, Integer.Sparse.eval_collectBalanced, rawRowCheck18132]

theorem rawRowCheck18133 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form7 = rawRow18133 := by decide +kernel

theorem rowCheck18133 : row18133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18133 := by decide +kernel

theorem rowEval18133 (x : Key → ℝ) : Integer.Sparse.eval row18133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18133, Integer.Sparse.eval_collectBalanced, rawRowCheck18133]

theorem rawRowCheck18134 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form7 = rawRow18134 := by decide +kernel

theorem rowCheck18134 : row18134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18134 := by decide +kernel

theorem rowEval18134 (x : Key → ℝ) : Integer.Sparse.eval row18134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18134, Integer.Sparse.eval_collectBalanced, rawRowCheck18134]

theorem rawRowCheck18135 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form7 = rawRow18135 := by decide +kernel

theorem rowCheck18135 : row18135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18135 := by decide +kernel

theorem rowEval18135 (x : Key → ℝ) : Integer.Sparse.eval row18135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18135, Integer.Sparse.eval_collectBalanced, rawRowCheck18135]

theorem rawRowCheck18136 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form7 = rawRow18136 := by decide +kernel

theorem rowCheck18136 : row18136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18136 := by decide +kernel

theorem rowEval18136 (x : Key → ℝ) : Integer.Sparse.eval row18136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18136, Integer.Sparse.eval_collectBalanced, rawRowCheck18136]

theorem rawRowCheck18137 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form7 = rawRow18137 := by decide +kernel

theorem rowCheck18137 : row18137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18137 := by decide +kernel

theorem rowEval18137 (x : Key → ℝ) : Integer.Sparse.eval row18137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18137, Integer.Sparse.eval_collectBalanced, rawRowCheck18137]

theorem rawRowCheck18138 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow18138 := by decide +kernel

theorem rowCheck18138 : row18138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18138 := by decide +kernel

theorem rowEval18138 (x : Key → ℝ) : Integer.Sparse.eval row18138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18138, Integer.Sparse.eval_collectBalanced, rawRowCheck18138]

theorem rawRowCheck18139 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow18139 := by decide +kernel

theorem rowCheck18139 : row18139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18139 := by decide +kernel

theorem rowEval18139 (x : Key → ℝ) : Integer.Sparse.eval row18139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18139, Integer.Sparse.eval_collectBalanced, rawRowCheck18139]

theorem rawRowCheck18140 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow18140 := by decide +kernel

theorem rowCheck18140 : row18140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18140 := by decide +kernel

theorem rowEval18140 (x : Key → ℝ) : Integer.Sparse.eval row18140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18140, Integer.Sparse.eval_collectBalanced, rawRowCheck18140]

theorem rawRowCheck18141 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form7 = rawRow18141 := by decide +kernel

theorem rowCheck18141 : row18141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18141 := by decide +kernel

theorem rowEval18141 (x : Key → ℝ) : Integer.Sparse.eval row18141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18141, Integer.Sparse.eval_collectBalanced, rawRowCheck18141]

theorem rawRowCheck18142 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form7 = rawRow18142 := by decide +kernel

theorem rowCheck18142 : row18142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18142 := by decide +kernel

theorem rowEval18142 (x : Key → ℝ) : Integer.Sparse.eval row18142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18142, Integer.Sparse.eval_collectBalanced, rawRowCheck18142]

theorem rawRowCheck18143 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form7 = rawRow18143 := by decide +kernel

theorem rowCheck18143 : row18143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18143 := by decide +kernel

theorem rowEval18143 (x : Key → ℝ) : Integer.Sparse.eval row18143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18143, Integer.Sparse.eval_collectBalanced, rawRowCheck18143]

theorem rawRowCheck18144 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form7 = rawRow18144 := by decide +kernel

theorem rowCheck18144 : row18144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18144 := by decide +kernel

theorem rowEval18144 (x : Key → ℝ) : Integer.Sparse.eval row18144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18144, Integer.Sparse.eval_collectBalanced, rawRowCheck18144]

theorem rawRowCheck18145 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow18145 := by decide +kernel

theorem rowCheck18145 : row18145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18145 := by decide +kernel

theorem rowEval18145 (x : Key → ℝ) : Integer.Sparse.eval row18145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18145, Integer.Sparse.eval_collectBalanced, rawRowCheck18145]

theorem rawRowCheck18146 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow18146 := by decide +kernel

theorem rowCheck18146 : row18146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18146 := by decide +kernel

theorem rowEval18146 (x : Key → ℝ) : Integer.Sparse.eval row18146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18146, Integer.Sparse.eval_collectBalanced, rawRowCheck18146]

theorem rawRowCheck18147 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow18147 := by decide +kernel

theorem rowCheck18147 : row18147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18147 := by decide +kernel

theorem rowEval18147 (x : Key → ℝ) : Integer.Sparse.eval row18147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18147, Integer.Sparse.eval_collectBalanced, rawRowCheck18147]

theorem rawRowCheck18148 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow18148 := by decide +kernel

theorem rowCheck18148 : row18148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18148 := by decide +kernel

theorem rowEval18148 (x : Key → ℝ) : Integer.Sparse.eval row18148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18148, Integer.Sparse.eval_collectBalanced, rawRowCheck18148]

theorem rawRowCheck18149 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form8 = rawRow18149 := by decide +kernel

theorem rowCheck18149 : row18149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18149 := by decide +kernel

theorem rowEval18149 (x : Key → ℝ) : Integer.Sparse.eval row18149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18149, Integer.Sparse.eval_collectBalanced, rawRowCheck18149]

theorem rawRowCheck18150 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form8 = rawRow18150 := by decide +kernel

theorem rowCheck18150 : row18150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18150 := by decide +kernel

theorem rowEval18150 (x : Key → ℝ) : Integer.Sparse.eval row18150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18150, Integer.Sparse.eval_collectBalanced, rawRowCheck18150]

theorem rawRowCheck18151 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form8 = rawRow18151 := by decide +kernel

theorem rowCheck18151 : row18151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18151 := by decide +kernel

theorem rowEval18151 (x : Key → ℝ) : Integer.Sparse.eval row18151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18151, Integer.Sparse.eval_collectBalanced, rawRowCheck18151]

theorem rawRowCheck18152 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form8 = rawRow18152 := by decide +kernel

theorem rowCheck18152 : row18152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18152 := by decide +kernel

theorem rowEval18152 (x : Key → ℝ) : Integer.Sparse.eval row18152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18152, Integer.Sparse.eval_collectBalanced, rawRowCheck18152]

theorem rawRowCheck18153 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form8 = rawRow18153 := by decide +kernel

theorem rowCheck18153 : row18153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18153 := by decide +kernel

theorem rowEval18153 (x : Key → ℝ) : Integer.Sparse.eval row18153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18153, Integer.Sparse.eval_collectBalanced, rawRowCheck18153]

theorem rawRowCheck18154 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form8 = rawRow18154 := by decide +kernel

theorem rowCheck18154 : row18154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18154 := by decide +kernel

theorem rowEval18154 (x : Key → ℝ) : Integer.Sparse.eval row18154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18154, Integer.Sparse.eval_collectBalanced, rawRowCheck18154]

theorem rawRowCheck18155 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form8 = rawRow18155 := by decide +kernel

theorem rowCheck18155 : row18155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18155 := by decide +kernel

theorem rowEval18155 (x : Key → ℝ) : Integer.Sparse.eval row18155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18155, Integer.Sparse.eval_collectBalanced, rawRowCheck18155]

theorem rawRowCheck18156 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form8 = rawRow18156 := by decide +kernel

theorem rowCheck18156 : row18156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18156 := by decide +kernel

theorem rowEval18156 (x : Key → ℝ) : Integer.Sparse.eval row18156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18156, Integer.Sparse.eval_collectBalanced, rawRowCheck18156]

theorem rawRowCheck18157 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form8 = rawRow18157 := by decide +kernel

theorem rowCheck18157 : row18157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18157 := by decide +kernel

theorem rowEval18157 (x : Key → ℝ) : Integer.Sparse.eval row18157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18157, Integer.Sparse.eval_collectBalanced, rawRowCheck18157]

theorem rawRowCheck18158 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow18158 := by decide +kernel

theorem rowCheck18158 : row18158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18158 := by decide +kernel

theorem rowEval18158 (x : Key → ℝ) : Integer.Sparse.eval row18158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18158, Integer.Sparse.eval_collectBalanced, rawRowCheck18158]

theorem rawRowCheck18159 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow18159 := by decide +kernel

theorem rowCheck18159 : row18159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18159 := by decide +kernel

theorem rowEval18159 (x : Key → ℝ) : Integer.Sparse.eval row18159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18159, Integer.Sparse.eval_collectBalanced, rawRowCheck18159]

theorem rawRowCheck18160 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow18160 := by decide +kernel

theorem rowCheck18160 : row18160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18160 := by decide +kernel

theorem rowEval18160 (x : Key → ℝ) : Integer.Sparse.eval row18160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18160, Integer.Sparse.eval_collectBalanced, rawRowCheck18160]

theorem rawRowCheck18161 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form8 = rawRow18161 := by decide +kernel

theorem rowCheck18161 : row18161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18161 := by decide +kernel

theorem rowEval18161 (x : Key → ℝ) : Integer.Sparse.eval row18161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18161, Integer.Sparse.eval_collectBalanced, rawRowCheck18161]

theorem rawRowCheck18162 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form8 = rawRow18162 := by decide +kernel

theorem rowCheck18162 : row18162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18162 := by decide +kernel

theorem rowEval18162 (x : Key → ℝ) : Integer.Sparse.eval row18162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18162, Integer.Sparse.eval_collectBalanced, rawRowCheck18162]

theorem rawRowCheck18163 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form8 = rawRow18163 := by decide +kernel

theorem rowCheck18163 : row18163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18163 := by decide +kernel

theorem rowEval18163 (x : Key → ℝ) : Integer.Sparse.eval row18163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18163, Integer.Sparse.eval_collectBalanced, rawRowCheck18163]

theorem rawRowCheck18164 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form8 = rawRow18164 := by decide +kernel

theorem rowCheck18164 : row18164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18164 := by decide +kernel

theorem rowEval18164 (x : Key → ℝ) : Integer.Sparse.eval row18164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18164, Integer.Sparse.eval_collectBalanced, rawRowCheck18164]

theorem rawRowCheck18165 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow18165 := by decide +kernel

theorem rowCheck18165 : row18165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18165 := by decide +kernel

theorem rowEval18165 (x : Key → ℝ) : Integer.Sparse.eval row18165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18165, Integer.Sparse.eval_collectBalanced, rawRowCheck18165]

theorem rawRowCheck18166 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow18166 := by decide +kernel

theorem rowCheck18166 : row18166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18166 := by decide +kernel

theorem rowEval18166 (x : Key → ℝ) : Integer.Sparse.eval row18166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18166, Integer.Sparse.eval_collectBalanced, rawRowCheck18166]

theorem rawRowCheck18167 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow18167 := by decide +kernel

theorem rowCheck18167 : row18167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18167 := by decide +kernel

theorem rowEval18167 (x : Key → ℝ) : Integer.Sparse.eval row18167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18167, Integer.Sparse.eval_collectBalanced, rawRowCheck18167]

theorem rawRowCheck18168 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form8 = rawRow18168 := by decide +kernel

theorem rowCheck18168 : row18168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18168 := by decide +kernel

theorem rowEval18168 (x : Key → ℝ) : Integer.Sparse.eval row18168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18168, Integer.Sparse.eval_collectBalanced, rawRowCheck18168]

theorem rawRowCheck18169 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form9 = rawRow18169 := by decide +kernel

theorem rowCheck18169 : row18169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18169 := by decide +kernel

theorem rowEval18169 (x : Key → ℝ) : Integer.Sparse.eval row18169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18169, Integer.Sparse.eval_collectBalanced, rawRowCheck18169]

theorem rawRowCheck18170 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form9 = rawRow18170 := by decide +kernel

theorem rowCheck18170 : row18170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18170 := by decide +kernel

theorem rowEval18170 (x : Key → ℝ) : Integer.Sparse.eval row18170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18170, Integer.Sparse.eval_collectBalanced, rawRowCheck18170]

theorem rawRowCheck18171 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form9 = rawRow18171 := by decide +kernel

theorem rowCheck18171 : row18171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18171 := by decide +kernel

theorem rowEval18171 (x : Key → ℝ) : Integer.Sparse.eval row18171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18171, Integer.Sparse.eval_collectBalanced, rawRowCheck18171]

theorem rawRowCheck18172 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form9 = rawRow18172 := by decide +kernel

theorem rowCheck18172 : row18172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18172 := by decide +kernel

theorem rowEval18172 (x : Key → ℝ) : Integer.Sparse.eval row18172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18172, Integer.Sparse.eval_collectBalanced, rawRowCheck18172]

theorem rawRowCheck18173 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form9 = rawRow18173 := by decide +kernel

theorem rowCheck18173 : row18173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18173 := by decide +kernel

theorem rowEval18173 (x : Key → ℝ) : Integer.Sparse.eval row18173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18173, Integer.Sparse.eval_collectBalanced, rawRowCheck18173]

theorem rawRowCheck18174 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form9 = rawRow18174 := by decide +kernel

theorem rowCheck18174 : row18174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18174 := by decide +kernel

theorem rowEval18174 (x : Key → ℝ) : Integer.Sparse.eval row18174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18174, Integer.Sparse.eval_collectBalanced, rawRowCheck18174]

theorem rawRowCheck18175 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form9 = rawRow18175 := by decide +kernel

theorem rowCheck18175 : row18175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18175 := by decide +kernel

theorem rowEval18175 (x : Key → ℝ) : Integer.Sparse.eval row18175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18175, Integer.Sparse.eval_collectBalanced, rawRowCheck18175]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18176 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form9 = rawRow18176 := by decide +kernel

theorem rowCheck18176 : row18176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18176 := by decide +kernel

theorem rowEval18176 (x : Key → ℝ) : Integer.Sparse.eval row18176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18176, Integer.Sparse.eval_collectBalanced, rawRowCheck18176]

theorem rawRowCheck18177 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form9 = rawRow18177 := by decide +kernel

theorem rowCheck18177 : row18177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18177 := by decide +kernel

theorem rowEval18177 (x : Key → ℝ) : Integer.Sparse.eval row18177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18177, Integer.Sparse.eval_collectBalanced, rawRowCheck18177]

theorem rawRowCheck18178 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow18178 := by decide +kernel

theorem rowCheck18178 : row18178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18178 := by decide +kernel

theorem rowEval18178 (x : Key → ℝ) : Integer.Sparse.eval row18178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18178, Integer.Sparse.eval_collectBalanced, rawRowCheck18178]

theorem rawRowCheck18179 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow18179 := by decide +kernel

theorem rowCheck18179 : row18179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18179 := by decide +kernel

theorem rowEval18179 (x : Key → ℝ) : Integer.Sparse.eval row18179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18179, Integer.Sparse.eval_collectBalanced, rawRowCheck18179]

theorem rawRowCheck18180 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow18180 := by decide +kernel

theorem rowCheck18180 : row18180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18180 := by decide +kernel

theorem rowEval18180 (x : Key → ℝ) : Integer.Sparse.eval row18180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18180, Integer.Sparse.eval_collectBalanced, rawRowCheck18180]

theorem rawRowCheck18181 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form9 = rawRow18181 := by decide +kernel

theorem rowCheck18181 : row18181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18181 := by decide +kernel

theorem rowEval18181 (x : Key → ℝ) : Integer.Sparse.eval row18181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18181, Integer.Sparse.eval_collectBalanced, rawRowCheck18181]

theorem rawRowCheck18182 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form9 = rawRow18182 := by decide +kernel

theorem rowCheck18182 : row18182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18182 := by decide +kernel

theorem rowEval18182 (x : Key → ℝ) : Integer.Sparse.eval row18182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18182, Integer.Sparse.eval_collectBalanced, rawRowCheck18182]

theorem rawRowCheck18183 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form9 = rawRow18183 := by decide +kernel

theorem rowCheck18183 : row18183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18183 := by decide +kernel

theorem rowEval18183 (x : Key → ℝ) : Integer.Sparse.eval row18183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18183, Integer.Sparse.eval_collectBalanced, rawRowCheck18183]

theorem rawRowCheck18184 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form9 = rawRow18184 := by decide +kernel

theorem rowCheck18184 : row18184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18184 := by decide +kernel

theorem rowEval18184 (x : Key → ℝ) : Integer.Sparse.eval row18184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18184, Integer.Sparse.eval_collectBalanced, rawRowCheck18184]

theorem rawRowCheck18185 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow18185 := by decide +kernel

theorem rowCheck18185 : row18185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18185 := by decide +kernel

theorem rowEval18185 (x : Key → ℝ) : Integer.Sparse.eval row18185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18185, Integer.Sparse.eval_collectBalanced, rawRowCheck18185]

theorem rawRowCheck18186 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow18186 := by decide +kernel

theorem rowCheck18186 : row18186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18186 := by decide +kernel

theorem rowEval18186 (x : Key → ℝ) : Integer.Sparse.eval row18186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18186, Integer.Sparse.eval_collectBalanced, rawRowCheck18186]

theorem rawRowCheck18187 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow18187 := by decide +kernel

theorem rowCheck18187 : row18187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18187 := by decide +kernel

theorem rowEval18187 (x : Key → ℝ) : Integer.Sparse.eval row18187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18187, Integer.Sparse.eval_collectBalanced, rawRowCheck18187]

theorem rawRowCheck18188 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form9 = rawRow18188 := by decide +kernel

theorem rowCheck18188 : row18188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18188 := by decide +kernel

theorem rowEval18188 (x : Key → ℝ) : Integer.Sparse.eval row18188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18188, Integer.Sparse.eval_collectBalanced, rawRowCheck18188]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck18329 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form17 = rawRow18329 := by decide +kernel

theorem rowCheck18329 : row18329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18329 := by decide +kernel

theorem rowEval18329 (x : Key → ℝ) : Integer.Sparse.eval row18329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18329, Integer.Sparse.eval_collectBalanced, rawRowCheck18329]

theorem rawRowCheck18330 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form17 = rawRow18330 := by decide +kernel

theorem rowCheck18330 : row18330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18330 := by decide +kernel

theorem rowEval18330 (x : Key → ℝ) : Integer.Sparse.eval row18330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18330, Integer.Sparse.eval_collectBalanced, rawRowCheck18330]

theorem rawRowCheck18331 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form17 = rawRow18331 := by decide +kernel

theorem rowCheck18331 : row18331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18331 := by decide +kernel

theorem rowEval18331 (x : Key → ℝ) : Integer.Sparse.eval row18331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18331, Integer.Sparse.eval_collectBalanced, rawRowCheck18331]

theorem rawRowCheck18332 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form17 = rawRow18332 := by decide +kernel

theorem rowCheck18332 : row18332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18332 := by decide +kernel

theorem rowEval18332 (x : Key → ℝ) : Integer.Sparse.eval row18332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18332, Integer.Sparse.eval_collectBalanced, rawRowCheck18332]

theorem rawRowCheck18333 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form17 = rawRow18333 := by decide +kernel

theorem rowCheck18333 : row18333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18333 := by decide +kernel

theorem rowEval18333 (x : Key → ℝ) : Integer.Sparse.eval row18333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18333, Integer.Sparse.eval_collectBalanced, rawRowCheck18333]

theorem rawRowCheck18334 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form17 = rawRow18334 := by decide +kernel

theorem rowCheck18334 : row18334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18334 := by decide +kernel

theorem rowEval18334 (x : Key → ℝ) : Integer.Sparse.eval row18334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18334, Integer.Sparse.eval_collectBalanced, rawRowCheck18334]

theorem rawRowCheck18335 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form17 = rawRow18335 := by decide +kernel

theorem rowCheck18335 : row18335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18335 := by decide +kernel

theorem rowEval18335 (x : Key → ℝ) : Integer.Sparse.eval row18335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18335, Integer.Sparse.eval_collectBalanced, rawRowCheck18335]

theorem rawRowCheck18336 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form17 = rawRow18336 := by decide +kernel

theorem rowCheck18336 : row18336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18336 := by decide +kernel

theorem rowEval18336 (x : Key → ℝ) : Integer.Sparse.eval row18336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18336, Integer.Sparse.eval_collectBalanced, rawRowCheck18336]

theorem rawRowCheck18337 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form17 = rawRow18337 := by decide +kernel

theorem rowCheck18337 : row18337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18337 := by decide +kernel

theorem rowEval18337 (x : Key → ℝ) : Integer.Sparse.eval row18337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18337, Integer.Sparse.eval_collectBalanced, rawRowCheck18337]

theorem rawRowCheck18338 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form17 = rawRow18338 := by decide +kernel

theorem rowCheck18338 : row18338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18338 := by decide +kernel

theorem rowEval18338 (x : Key → ℝ) : Integer.Sparse.eval row18338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18338, Integer.Sparse.eval_collectBalanced, rawRowCheck18338]

theorem rawRowCheck18339 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form17 = rawRow18339 := by decide +kernel

theorem rowCheck18339 : row18339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18339 := by decide +kernel

theorem rowEval18339 (x : Key → ℝ) : Integer.Sparse.eval row18339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18339, Integer.Sparse.eval_collectBalanced, rawRowCheck18339]

theorem rawRowCheck18340 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form17 = rawRow18340 := by decide +kernel

theorem rowCheck18340 : row18340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18340 := by decide +kernel

theorem rowEval18340 (x : Key → ℝ) : Integer.Sparse.eval row18340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18340, Integer.Sparse.eval_collectBalanced, rawRowCheck18340]

theorem rawRowCheck18341 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form17 = rawRow18341 := by decide +kernel

theorem rowCheck18341 : row18341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18341 := by decide +kernel

theorem rowEval18341 (x : Key → ℝ) : Integer.Sparse.eval row18341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18341, Integer.Sparse.eval_collectBalanced, rawRowCheck18341]

theorem rawRowCheck18342 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form17 = rawRow18342 := by decide +kernel

theorem rowCheck18342 : row18342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18342 := by decide +kernel

theorem rowEval18342 (x : Key → ℝ) : Integer.Sparse.eval row18342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18342, Integer.Sparse.eval_collectBalanced, rawRowCheck18342]

theorem rawRowCheck18343 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form17 = rawRow18343 := by decide +kernel

theorem rowCheck18343 : row18343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18343 := by decide +kernel

theorem rowEval18343 (x : Key → ℝ) : Integer.Sparse.eval row18343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18343, Integer.Sparse.eval_collectBalanced, rawRowCheck18343]

theorem rawRowCheck18344 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form17 = rawRow18344 := by decide +kernel

theorem rowCheck18344 : row18344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18344 := by decide +kernel

theorem rowEval18344 (x : Key → ℝ) : Integer.Sparse.eval row18344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18344, Integer.Sparse.eval_collectBalanced, rawRowCheck18344]

theorem rawRowCheck18345 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form17 = rawRow18345 := by decide +kernel

theorem rowCheck18345 : row18345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18345 := by decide +kernel

theorem rowEval18345 (x : Key → ℝ) : Integer.Sparse.eval row18345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18345, Integer.Sparse.eval_collectBalanced, rawRowCheck18345]

theorem rawRowCheck18346 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form17 = rawRow18346 := by decide +kernel

theorem rowCheck18346 : row18346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18346 := by decide +kernel

theorem rowEval18346 (x : Key → ℝ) : Integer.Sparse.eval row18346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18346, Integer.Sparse.eval_collectBalanced, rawRowCheck18346]

theorem rawRowCheck18347 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form17 = rawRow18347 := by decide +kernel

theorem rowCheck18347 : row18347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18347 := by decide +kernel

theorem rowEval18347 (x : Key → ℝ) : Integer.Sparse.eval row18347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18347, Integer.Sparse.eval_collectBalanced, rawRowCheck18347]

theorem rawRowCheck18348 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form17 = rawRow18348 := by decide +kernel

theorem rowCheck18348 : row18348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18348 := by decide +kernel

theorem rowEval18348 (x : Key → ℝ) : Integer.Sparse.eval row18348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18348, Integer.Sparse.eval_collectBalanced, rawRowCheck18348]

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

theorem rawRowCheck18389 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form20 = rawRow18389 := by decide +kernel

theorem rowCheck18389 : row18389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18389 := by decide +kernel

theorem rowEval18389 (x : Key → ℝ) : Integer.Sparse.eval row18389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18389, Integer.Sparse.eval_collectBalanced, rawRowCheck18389]

theorem rawRowCheck18390 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form20 = rawRow18390 := by decide +kernel

theorem rowCheck18390 : row18390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18390 := by decide +kernel

theorem rowEval18390 (x : Key → ℝ) : Integer.Sparse.eval row18390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18390, Integer.Sparse.eval_collectBalanced, rawRowCheck18390]

theorem rawRowCheck18391 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form20 = rawRow18391 := by decide +kernel

theorem rowCheck18391 : row18391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18391 := by decide +kernel

theorem rowEval18391 (x : Key → ℝ) : Integer.Sparse.eval row18391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18391, Integer.Sparse.eval_collectBalanced, rawRowCheck18391]

theorem rawRowCheck18392 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form20 = rawRow18392 := by decide +kernel

theorem rowCheck18392 : row18392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18392 := by decide +kernel

theorem rowEval18392 (x : Key → ℝ) : Integer.Sparse.eval row18392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18392, Integer.Sparse.eval_collectBalanced, rawRowCheck18392]

theorem rawRowCheck18393 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form20 = rawRow18393 := by decide +kernel

theorem rowCheck18393 : row18393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18393 := by decide +kernel

theorem rowEval18393 (x : Key → ℝ) : Integer.Sparse.eval row18393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18393, Integer.Sparse.eval_collectBalanced, rawRowCheck18393]

theorem rawRowCheck18394 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form20 = rawRow18394 := by decide +kernel

theorem rowCheck18394 : row18394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18394 := by decide +kernel

theorem rowEval18394 (x : Key → ℝ) : Integer.Sparse.eval row18394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18394, Integer.Sparse.eval_collectBalanced, rawRowCheck18394]

theorem rawRowCheck18395 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form20 = rawRow18395 := by decide +kernel

theorem rowCheck18395 : row18395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18395 := by decide +kernel

theorem rowEval18395 (x : Key → ℝ) : Integer.Sparse.eval row18395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18395, Integer.Sparse.eval_collectBalanced, rawRowCheck18395]

theorem rawRowCheck18396 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form20 = rawRow18396 := by decide +kernel

theorem rowCheck18396 : row18396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18396 := by decide +kernel

theorem rowEval18396 (x : Key → ℝ) : Integer.Sparse.eval row18396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18396, Integer.Sparse.eval_collectBalanced, rawRowCheck18396]

theorem rawRowCheck18397 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form20 = rawRow18397 := by decide +kernel

theorem rowCheck18397 : row18397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18397 := by decide +kernel

theorem rowEval18397 (x : Key → ℝ) : Integer.Sparse.eval row18397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18397, Integer.Sparse.eval_collectBalanced, rawRowCheck18397]

theorem rawRowCheck18398 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form20 = rawRow18398 := by decide +kernel

theorem rowCheck18398 : row18398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18398 := by decide +kernel

theorem rowEval18398 (x : Key → ℝ) : Integer.Sparse.eval row18398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18398, Integer.Sparse.eval_collectBalanced, rawRowCheck18398]

theorem rawRowCheck18399 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form20 = rawRow18399 := by decide +kernel

theorem rowCheck18399 : row18399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18399 := by decide +kernel

theorem rowEval18399 (x : Key → ℝ) : Integer.Sparse.eval row18399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18399, Integer.Sparse.eval_collectBalanced, rawRowCheck18399]

theorem rawRowCheck18400 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form20 = rawRow18400 := by decide +kernel

theorem rowCheck18400 : row18400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18400 := by decide +kernel

theorem rowEval18400 (x : Key → ℝ) : Integer.Sparse.eval row18400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18400, Integer.Sparse.eval_collectBalanced, rawRowCheck18400]

theorem rawRowCheck18401 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form20 = rawRow18401 := by decide +kernel

theorem rowCheck18401 : row18401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18401 := by decide +kernel

theorem rowEval18401 (x : Key → ℝ) : Integer.Sparse.eval row18401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18401, Integer.Sparse.eval_collectBalanced, rawRowCheck18401]

theorem rawRowCheck18402 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form20 = rawRow18402 := by decide +kernel

theorem rowCheck18402 : row18402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18402 := by decide +kernel

theorem rowEval18402 (x : Key → ℝ) : Integer.Sparse.eval row18402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18402, Integer.Sparse.eval_collectBalanced, rawRowCheck18402]

theorem rawRowCheck18403 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form20 = rawRow18403 := by decide +kernel

theorem rowCheck18403 : row18403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18403 := by decide +kernel

theorem rowEval18403 (x : Key → ℝ) : Integer.Sparse.eval row18403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18403, Integer.Sparse.eval_collectBalanced, rawRowCheck18403]

theorem rawRowCheck18404 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form20 = rawRow18404 := by decide +kernel

theorem rowCheck18404 : row18404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18404 := by decide +kernel

theorem rowEval18404 (x : Key → ℝ) : Integer.Sparse.eval row18404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18404, Integer.Sparse.eval_collectBalanced, rawRowCheck18404]

theorem rawRowCheck18405 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form20 = rawRow18405 := by decide +kernel

theorem rowCheck18405 : row18405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18405 := by decide +kernel

theorem rowEval18405 (x : Key → ℝ) : Integer.Sparse.eval row18405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18405, Integer.Sparse.eval_collectBalanced, rawRowCheck18405]

theorem rawRowCheck18406 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form20 = rawRow18406 := by decide +kernel

theorem rowCheck18406 : row18406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18406 := by decide +kernel

theorem rowEval18406 (x : Key → ℝ) : Integer.Sparse.eval row18406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18406, Integer.Sparse.eval_collectBalanced, rawRowCheck18406]

theorem rawRowCheck18407 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form20 = rawRow18407 := by decide +kernel

theorem rowCheck18407 : row18407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18407 := by decide +kernel

theorem rowEval18407 (x : Key → ℝ) : Integer.Sparse.eval row18407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18407, Integer.Sparse.eval_collectBalanced, rawRowCheck18407]

theorem rawRowCheck18408 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form20 = rawRow18408 := by decide +kernel

theorem rowCheck18408 : row18408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18408 := by decide +kernel

theorem rowEval18408 (x : Key → ℝ) : Integer.Sparse.eval row18408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18408, Integer.Sparse.eval_collectBalanced, rawRowCheck18408]

theorem rawRowCheck18409 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form21 = rawRow18409 := by decide +kernel

theorem rowCheck18409 : row18409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18409 := by decide +kernel

theorem rowEval18409 (x : Key → ℝ) : Integer.Sparse.eval row18409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18409, Integer.Sparse.eval_collectBalanced, rawRowCheck18409]

theorem rawRowCheck18410 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form21 = rawRow18410 := by decide +kernel

theorem rowCheck18410 : row18410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18410 := by decide +kernel

theorem rowEval18410 (x : Key → ℝ) : Integer.Sparse.eval row18410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form21) x := by
  rw [rowCheck18410, Integer.Sparse.eval_collectBalanced, rawRowCheck18410]

theorem rawRowCheck18411 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form21 = rawRow18411 := by decide +kernel

theorem rowCheck18411 : row18411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18411 := by decide +kernel

theorem rowEval18411 (x : Key → ℝ) : Integer.Sparse.eval row18411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18411, Integer.Sparse.eval_collectBalanced, rawRowCheck18411]

theorem rawRowCheck18412 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form21 = rawRow18412 := by decide +kernel

theorem rowCheck18412 : row18412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18412 := by decide +kernel

theorem rowEval18412 (x : Key → ℝ) : Integer.Sparse.eval row18412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18412, Integer.Sparse.eval_collectBalanced, rawRowCheck18412]

theorem rawRowCheck18413 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form21 = rawRow18413 := by decide +kernel

theorem rowCheck18413 : row18413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18413 := by decide +kernel

theorem rowEval18413 (x : Key → ℝ) : Integer.Sparse.eval row18413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form21) x := by
  rw [rowCheck18413, Integer.Sparse.eval_collectBalanced, rawRowCheck18413]

theorem rawRowCheck18414 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form21 = rawRow18414 := by decide +kernel

theorem rowCheck18414 : row18414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18414 := by decide +kernel

theorem rowEval18414 (x : Key → ℝ) : Integer.Sparse.eval row18414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18414, Integer.Sparse.eval_collectBalanced, rawRowCheck18414]

theorem rawRowCheck18415 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form21 = rawRow18415 := by decide +kernel

theorem rowCheck18415 : row18415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18415 := by decide +kernel

theorem rowEval18415 (x : Key → ℝ) : Integer.Sparse.eval row18415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18415, Integer.Sparse.eval_collectBalanced, rawRowCheck18415]

theorem rawRowCheck18416 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form21 = rawRow18416 := by decide +kernel

theorem rowCheck18416 : row18416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18416 := by decide +kernel

theorem rowEval18416 (x : Key → ℝ) : Integer.Sparse.eval row18416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18416, Integer.Sparse.eval_collectBalanced, rawRowCheck18416]

theorem rawRowCheck18417 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form21 = rawRow18417 := by decide +kernel

theorem rowCheck18417 : row18417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18417 := by decide +kernel

theorem rowEval18417 (x : Key → ℝ) : Integer.Sparse.eval row18417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18417, Integer.Sparse.eval_collectBalanced, rawRowCheck18417]

theorem rawRowCheck18418 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form21 = rawRow18418 := by decide +kernel

theorem rowCheck18418 : row18418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18418 := by decide +kernel

theorem rowEval18418 (x : Key → ℝ) : Integer.Sparse.eval row18418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form21) x := by
  rw [rowCheck18418, Integer.Sparse.eval_collectBalanced, rawRowCheck18418]

theorem rawRowCheck18419 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form21 = rawRow18419 := by decide +kernel

theorem rowCheck18419 : row18419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18419 := by decide +kernel

theorem rowEval18419 (x : Key → ℝ) : Integer.Sparse.eval row18419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18419, Integer.Sparse.eval_collectBalanced, rawRowCheck18419]

theorem rawRowCheck18420 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form21 = rawRow18420 := by decide +kernel

theorem rowCheck18420 : row18420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18420 := by decide +kernel

theorem rowEval18420 (x : Key → ℝ) : Integer.Sparse.eval row18420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18420, Integer.Sparse.eval_collectBalanced, rawRowCheck18420]

theorem rawRowCheck18421 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form21 = rawRow18421 := by decide +kernel

theorem rowCheck18421 : row18421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18421 := by decide +kernel

theorem rowEval18421 (x : Key → ℝ) : Integer.Sparse.eval row18421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18421, Integer.Sparse.eval_collectBalanced, rawRowCheck18421]

theorem rawRowCheck18422 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form21 = rawRow18422 := by decide +kernel

theorem rowCheck18422 : row18422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18422 := by decide +kernel

theorem rowEval18422 (x : Key → ℝ) : Integer.Sparse.eval row18422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18422, Integer.Sparse.eval_collectBalanced, rawRowCheck18422]

theorem rawRowCheck18423 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form21 = rawRow18423 := by decide +kernel

theorem rowCheck18423 : row18423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18423 := by decide +kernel

theorem rowEval18423 (x : Key → ℝ) : Integer.Sparse.eval row18423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18423, Integer.Sparse.eval_collectBalanced, rawRowCheck18423]

theorem rawRowCheck18424 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form21 = rawRow18424 := by decide +kernel

theorem rowCheck18424 : row18424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18424 := by decide +kernel

theorem rowEval18424 (x : Key → ℝ) : Integer.Sparse.eval row18424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18424, Integer.Sparse.eval_collectBalanced, rawRowCheck18424]

theorem rawRowCheck18425 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form21 = rawRow18425 := by decide +kernel

theorem rowCheck18425 : row18425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18425 := by decide +kernel

theorem rowEval18425 (x : Key → ℝ) : Integer.Sparse.eval row18425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form21) x := by
  rw [rowCheck18425, Integer.Sparse.eval_collectBalanced, rawRowCheck18425]

theorem rawRowCheck18426 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form21 = rawRow18426 := by decide +kernel

theorem rowCheck18426 : row18426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18426 := by decide +kernel

theorem rowEval18426 (x : Key → ℝ) : Integer.Sparse.eval row18426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18426, Integer.Sparse.eval_collectBalanced, rawRowCheck18426]

theorem rawRowCheck18427 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form21 = rawRow18427 := by decide +kernel

theorem rowCheck18427 : row18427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18427 := by decide +kernel

theorem rowEval18427 (x : Key → ℝ) : Integer.Sparse.eval row18427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18427, Integer.Sparse.eval_collectBalanced, rawRowCheck18427]

theorem rawRowCheck18428 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form21 = rawRow18428 := by decide +kernel

theorem rowCheck18428 : row18428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18428 := by decide +kernel

theorem rowEval18428 (x : Key → ℝ) : Integer.Sparse.eval row18428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18428, Integer.Sparse.eval_collectBalanced, rawRowCheck18428]

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

theorem entryCheck21_0 : entry21_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_0 k)) := by decide +kernel

theorem rowsSound21_0 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17989 x
  · exact rowEval17990 x
  · exact rowEval17991 x
  · exact rowEval17992 x
  · exact rowEval17993 x
  · exact rowEval17994 x
  · exact rowEval17995 x
  · exact rowEval17996 x
  · exact rowEval17997 x
  · exact rowEval17998 x
  · exact rowEval17999 x
  · exact rowEval18000 x
  · exact rowEval18001 x
  · exact rowEval18002 x
  · exact rowEval18003 x
  · exact rowEval18004 x
  · exact rowEval18005 x
  · exact rowEval18006 x
  · exact rowEval18007 x
  · exact rowEval18008 x

theorem entryEval21_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_0 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck21_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_0]

theorem entryCheck21_1 : entry21_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_1 k)) := by decide +kernel

theorem rowsSound21_1 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval18009 x
  · exact rowEval18010 x
  · exact rowEval18011 x
  · exact rowEval18012 x
  · exact rowEval18013 x
  · exact rowEval18014 x
  · exact rowEval18015 x
  · exact rowEval18016 x
  · exact rowEval18017 x
  · exact rowEval18018 x
  · exact rowEval18019 x
  · exact rowEval18020 x
  · exact rowEval18021 x
  · exact rowEval18022 x
  · exact rowEval18023 x
  · exact rowEval18024 x
  · exact rowEval18025 x
  · exact rowEval18026 x
  · exact rowEval18027 x
  · exact rowEval18028 x

theorem entryEval21_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_1 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck21_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_1]

theorem entryCheck21_2 : entry21_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_2 k)) := by decide +kernel

theorem rowsSound21_2 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval18029 x
  · exact rowEval18030 x
  · exact rowEval18031 x
  · exact rowEval18032 x
  · exact rowEval18033 x
  · exact rowEval18034 x
  · exact rowEval18035 x
  · exact rowEval18036 x
  · exact rowEval18037 x
  · exact rowEval18038 x
  · exact rowEval18039 x
  · exact rowEval18040 x
  · exact rowEval18041 x
  · exact rowEval18042 x
  · exact rowEval18043 x
  · exact rowEval18044 x
  · exact rowEval18045 x
  · exact rowEval18046 x
  · exact rowEval18047 x
  · exact rowEval18048 x

theorem entryEval21_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_2 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck21_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_2]

theorem entryCheck21_3 : entry21_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_3 k)) := by decide +kernel

theorem rowsSound21_3 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval18049 x
  · exact rowEval18050 x
  · exact rowEval18051 x
  · exact rowEval18052 x
  · exact rowEval18053 x
  · exact rowEval18054 x
  · exact rowEval18055 x
  · exact rowEval18056 x
  · exact rowEval18057 x
  · exact rowEval18058 x
  · exact rowEval18059 x
  · exact rowEval18060 x
  · exact rowEval18061 x
  · exact rowEval18062 x
  · exact rowEval18063 x
  · exact rowEval18064 x
  · exact rowEval18065 x
  · exact rowEval18066 x
  · exact rowEval18067 x
  · exact rowEval18068 x

theorem entryEval21_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_3 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck21_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_3]

theorem entryCheck21_4 : entry21_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_4 k)) := by decide +kernel

theorem rowsSound21_4 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval18069 x
  · exact rowEval18070 x
  · exact rowEval18071 x
  · exact rowEval18072 x
  · exact rowEval18073 x
  · exact rowEval18074 x
  · exact rowEval18075 x
  · exact rowEval18076 x
  · exact rowEval18077 x
  · exact rowEval18078 x
  · exact rowEval18079 x
  · exact rowEval18080 x
  · exact rowEval18081 x
  · exact rowEval18082 x
  · exact rowEval18083 x
  · exact rowEval18084 x
  · exact rowEval18085 x
  · exact rowEval18086 x
  · exact rowEval18087 x
  · exact rowEval18088 x

theorem entryEval21_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_4 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck21_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_4]

theorem entryCheck21_5 : entry21_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_5 k)) := by decide +kernel

theorem rowsSound21_5 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval18089 x
  · exact rowEval18090 x
  · exact rowEval18091 x
  · exact rowEval18092 x
  · exact rowEval18093 x
  · exact rowEval18094 x
  · exact rowEval18095 x
  · exact rowEval18096 x
  · exact rowEval18097 x
  · exact rowEval18098 x
  · exact rowEval18099 x
  · exact rowEval18100 x
  · exact rowEval18101 x
  · exact rowEval18102 x
  · exact rowEval18103 x
  · exact rowEval18104 x
  · exact rowEval18105 x
  · exact rowEval18106 x
  · exact rowEval18107 x
  · exact rowEval18108 x

theorem entryEval21_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_5 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck21_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_5]

theorem entryCheck21_7 : entry21_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_7 k)) := by decide +kernel

theorem rowsSound21_7 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval18129 x
  · exact rowEval18130 x
  · exact rowEval18131 x
  · exact rowEval18132 x
  · exact rowEval18133 x
  · exact rowEval18134 x
  · exact rowEval18135 x
  · exact rowEval18136 x
  · exact rowEval18137 x
  · exact rowEval18138 x
  · exact rowEval18139 x
  · exact rowEval18140 x
  · exact rowEval18141 x
  · exact rowEval18142 x
  · exact rowEval18143 x
  · exact rowEval18144 x
  · exact rowEval18145 x
  · exact rowEval18146 x
  · exact rowEval18147 x
  · exact rowEval18148 x

theorem entryEval21_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_7 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck21_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_7]

theorem entryCheck21_8 : entry21_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_8 k)) := by decide +kernel

theorem rowsSound21_8 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval18149 x
  · exact rowEval18150 x
  · exact rowEval18151 x
  · exact rowEval18152 x
  · exact rowEval18153 x
  · exact rowEval18154 x
  · exact rowEval18155 x
  · exact rowEval18156 x
  · exact rowEval18157 x
  · exact rowEval18158 x
  · exact rowEval18159 x
  · exact rowEval18160 x
  · exact rowEval18161 x
  · exact rowEval18162 x
  · exact rowEval18163 x
  · exact rowEval18164 x
  · exact rowEval18165 x
  · exact rowEval18166 x
  · exact rowEval18167 x
  · exact rowEval18168 x

theorem entryEval21_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_8 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck21_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_8]

theorem entryCheck21_9 : entry21_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_9 k)) := by decide +kernel

theorem rowsSound21_9 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval18169 x
  · exact rowEval18170 x
  · exact rowEval18171 x
  · exact rowEval18172 x
  · exact rowEval18173 x
  · exact rowEval18174 x
  · exact rowEval18175 x
  · exact rowEval18176 x
  · exact rowEval18177 x
  · exact rowEval18178 x
  · exact rowEval18179 x
  · exact rowEval18180 x
  · exact rowEval18181 x
  · exact rowEval18182 x
  · exact rowEval18183 x
  · exact rowEval18184 x
  · exact rowEval18185 x
  · exact rowEval18186 x
  · exact rowEval18187 x
  · exact rowEval18188 x

theorem entryEval21_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_9 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck21_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_9]

theorem entryCheck21_17 : entry21_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_17 k)) := by decide +kernel

theorem rowsSound21_17 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval18329 x
  · exact rowEval18330 x
  · exact rowEval18331 x
  · exact rowEval18332 x
  · exact rowEval18333 x
  · exact rowEval18334 x
  · exact rowEval18335 x
  · exact rowEval18336 x
  · exact rowEval18337 x
  · exact rowEval18338 x
  · exact rowEval18339 x
  · exact rowEval18340 x
  · exact rowEval18341 x
  · exact rowEval18342 x
  · exact rowEval18343 x
  · exact rowEval18344 x
  · exact rowEval18345 x
  · exact rowEval18346 x
  · exact rowEval18347 x
  · exact rowEval18348 x

theorem entryEval21_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_17 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck21_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_17]

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

theorem entryCheck21_20 : entry21_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_20 k)) := by decide +kernel

theorem rowsSound21_20 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form20) x := by
  fin_cases k
  · exact rowEval18389 x
  · exact rowEval18390 x
  · exact rowEval18391 x
  · exact rowEval18392 x
  · exact rowEval18393 x
  · exact rowEval18394 x
  · exact rowEval18395 x
  · exact rowEval18396 x
  · exact rowEval18397 x
  · exact rowEval18398 x
  · exact rowEval18399 x
  · exact rowEval18400 x
  · exact rowEval18401 x
  · exact rowEval18402 x
  · exact rowEval18403 x
  · exact rowEval18404 x
  · exact rowEval18405 x
  · exact rowEval18406 x
  · exact rowEval18407 x
  · exact rowEval18408 x

theorem entryEval21_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_20 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form20 B := by
  rw [entryCheck21_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_20]

theorem entryCheck21_21 : entry21_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_21 k)) := by decide +kernel

theorem rowsSound21_21 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form21) x := by
  fin_cases k
  · exact rowEval18409 x
  · exact rowEval18410 x
  · exact rowEval18411 x
  · exact rowEval18412 x
  · exact rowEval18413 x
  · exact rowEval18414 x
  · exact rowEval18415 x
  · exact rowEval18416 x
  · exact rowEval18417 x
  · exact rowEval18418 x
  · exact rowEval18419 x
  · exact rowEval18420 x
  · exact rowEval18421 x
  · exact rowEval18422 x
  · exact rowEval18423 x
  · exact rowEval18424 x
  · exact rowEval18425 x
  · exact rowEval18426 x
  · exact rowEval18427 x
  · exact rowEval18428 x

theorem entryEval21_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_21 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form21 B := by
  rw [entryCheck21_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_21]

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

theorem entryEvalRow21_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 21 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 21).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval21_0 B hB
  · exact entryEval21_1 B hB
  · exact entryEval21_2 B hB
  · exact entryEval21_3 B hB
  · exact entryEval21_4 B hB
  · exact entryEval21_5 B hB
  · exact entryEval21_6_e B hB
  · exact entryEval21_7 B hB
  · exact entryEval21_8 B hB
  · exact entryEval21_9 B hB
  · exact entryEval21_10_e B hB
  · exact entryEval21_11_e B hB
  · exact entryEval21_12_e B hB
  · exact entryEval21_13_e B hB
  · exact entryEval21_14_e B hB
  · exact entryEval21_15_e B hB
  · exact entryEval21_16_e B hB
  · exact entryEval21_17 B hB
  · exact entryEval21_18_e B hB
  · exact entryEval21_19 B hB
  · exact entryEval21_20 B hB
  · exact entryEval21_21 B hB

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21_e_oai
