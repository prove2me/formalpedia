-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block0.polynomial_interpretation_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:18:26.205588+00:00
-- url     : https://prove2.me/submissions/5f6556ad-951c-439e-8b93-a088fc0b1c8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E042
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E054
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval4_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval4_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval4_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEvalRow0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEvalRow1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEvalRow2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEvalRow3_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
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

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

open scoped BigOperators

theorem weights_cast_0 (j : Fin 5) :
    (weights 0 j : ℚ) = GramData.Block0.Z 0 j := by
  revert j
  decide +kernel

theorem weights_cast_1 (j : Fin 5) :
    (weights 1 j : ℚ) = GramData.Block0.Z 1 j := by
  revert j
  decide +kernel

theorem weights_cast_2 (j : Fin 5) :
    (weights 2 j : ℚ) = GramData.Block0.Z 2 j := by
  revert j
  decide +kernel

theorem weights_cast_3 (j : Fin 5) :
    (weights 3 j : ℚ) = GramData.Block0.Z 3 j := by
  revert j
  decide +kernel

theorem weights_cast_4 (j : Fin 5) :
    (weights 4 j : ℚ) = GramData.Block0.Z 4 j := by
  revert j
  decide +kernel

theorem weights_cast (i j : Fin 5) :
    (weights i j : ℚ) = GramData.Block0.Z i j := by
  fin_cases i
  · exact weights_cast_0 j
  · exact weights_cast_1 j
  · exact weights_cast_2 j
  · exact weights_cast_3 j
  · exact weights_cast_4 j

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem node0_check : node0 =
    Integer.Sparse.merge (Integer.Sparse.scale (7856995) entry_0_0) (Integer.Sparse.scale (-2793048) entry_0_1) := by decide +kernel

theorem node0_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node0 x = (((7856995 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((-2793048 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) := by
  rw [node0_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node1_check : node1 =
    Integer.Sparse.merge (Integer.Sparse.scale (4076125) entry_0_3) (Integer.Sparse.scale (-23581960) entry_0_4) := by decide +kernel

theorem node1_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node1 x = (((4076125 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((-23581960 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x) := by
  rw [node1_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node2_check : node2 =
    Integer.Sparse.merge (Integer.Sparse.scale (8971673) entry_0_2) node1 := by decide +kernel

theorem node2_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node2 x = (((8971673 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((4076125 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((-23581960 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x)) := by
  rw [node2_check, Integer.Sparse.eval_merge]
  rw [node1_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node3_check : node3 =
    Integer.Sparse.merge node0 node2 := by decide +kernel

theorem node3_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node3 x = ((((7856995 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((-2793048 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((8971673 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((4076125 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((-23581960 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) := by
  rw [node3_check, Integer.Sparse.eval_merge]
  rw [node0_eval, node2_eval]

theorem node4_check : node4 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2793048) entry_1_0) (Integer.Sparse.scale (5486181) entry_1_1) := by decide +kernel

theorem node4_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node4 x = (((-2793048 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((5486181 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) := by
  rw [node4_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node5_check : node5 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2967341) entry_1_3) (Integer.Sparse.scale (9048932) entry_1_4) := by decide +kernel

theorem node5_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node5 x = (((-2967341 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((9048932 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x) := by
  rw [node5_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node6_check : node6 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1693736) entry_1_2) node5 := by decide +kernel

theorem node6_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node6 x = (((-1693736 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-2967341 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((9048932 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x)) := by
  rw [node6_check, Integer.Sparse.eval_merge]
  rw [node5_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node7_check : node7 =
    Integer.Sparse.merge node4 node6 := by decide +kernel

theorem node7_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node7 x = ((((-2793048 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((5486181 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((-1693736 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-2967341 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((9048932 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) := by
  rw [node7_check, Integer.Sparse.eval_merge]
  rw [node4_eval, node6_eval]

theorem node8_check : node8 =
    Integer.Sparse.merge (Integer.Sparse.scale (8971673) entry_2_0) (Integer.Sparse.scale (-1693736) entry_2_1) := by decide +kernel

theorem node8_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node8 x = (((8971673 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-1693736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) := by
  rw [node8_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node9_check : node9 =
    Integer.Sparse.merge (Integer.Sparse.scale (-242661) entry_2_3) (Integer.Sparse.scale (-37895129) entry_2_4) := by decide +kernel

theorem node9_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node9 x = (((-242661 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((-37895129 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x) := by
  rw [node9_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node10_check : node10 =
    Integer.Sparse.merge (Integer.Sparse.scale (37455549) entry_2_2) node9 := by decide +kernel

theorem node10_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node10 x = (((37455549 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((-242661 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((-37895129 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x)) := by
  rw [node10_check, Integer.Sparse.eval_merge]
  rw [node9_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node11_check : node11 =
    Integer.Sparse.merge node8 node10 := by decide +kernel

theorem node11_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node11 x = ((((8971673 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-1693736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((37455549 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((-242661 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((-37895129 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) := by
  rw [node11_check, Integer.Sparse.eval_merge]
  rw [node8_eval, node10_eval]

theorem node12_check : node12 =
    Integer.Sparse.merge (Integer.Sparse.scale (4076125) entry_3_0) (Integer.Sparse.scale (-2967341) entry_3_1) := by decide +kernel

theorem node12_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node12 x = (((4076125 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-2967341 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) := by
  rw [node12_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node13_check : node13 =
    Integer.Sparse.merge (Integer.Sparse.scale (7655001) entry_3_3) (Integer.Sparse.scale (-9254062) entry_3_4) := by decide +kernel

theorem node13_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node13 x = (((7655001 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-9254062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x) := by
  rw [node13_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node14_check : node14 =
    Integer.Sparse.merge (Integer.Sparse.scale (-242661) entry_3_2) node13 := by decide +kernel

theorem node14_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node14 x = (((-242661 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((7655001 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-9254062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x)) := by
  rw [node14_check, Integer.Sparse.eval_merge]
  rw [node13_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node15_check : node15 =
    Integer.Sparse.merge node12 node14 := by decide +kernel

theorem node15_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node15 x = ((((4076125 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-2967341 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((-242661 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((7655001 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-9254062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) := by
  rw [node15_check, Integer.Sparse.eval_merge]
  rw [node12_eval, node14_eval]

theorem node16_check : node16 =
    Integer.Sparse.merge (Integer.Sparse.scale (-23581960) entry_4_0) (Integer.Sparse.scale (9048932) entry_4_1) := by decide +kernel

theorem node16_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node16 x = (((-23581960 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((9048932 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) := by
  rw [node16_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node17_check : node17 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9254062) entry_4_3) (Integer.Sparse.scale (86753990) entry_4_4) := by decide +kernel

theorem node17_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node17 x = (((-9254062 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((86753990 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x) := by
  rw [node17_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node18_check : node18 =
    Integer.Sparse.merge (Integer.Sparse.scale (-37895129) entry_4_2) node17 := by decide +kernel

theorem node18_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node18 x = (((-37895129 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-9254062 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((86753990 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x)) := by
  rw [node18_check, Integer.Sparse.eval_merge]
  rw [node17_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node19_check : node19 =
    Integer.Sparse.merge node16 node18 := by decide +kernel

theorem node19_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x = ((((-23581960 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((9048932 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((-37895129 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-9254062 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((86753990 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) := by
  rw [node19_check, Integer.Sparse.eval_merge]
  rw [node16_eval, node18_eval]

theorem node20_check : node20 =
    Integer.Sparse.merge node3 node7 := by decide +kernel

theorem node20_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node20 x = (Integer.Sparse.eval node3 x + Integer.Sparse.eval node7 x) := by
  rw [node20_check, Integer.Sparse.eval_merge]

theorem node21_check : node21 =
    Integer.Sparse.merge node15 node19 := by decide +kernel

theorem node21_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node21 x = (Integer.Sparse.eval node15 x + Integer.Sparse.eval node19 x) := by
  rw [node21_check, Integer.Sparse.eval_merge]

theorem node22_check : node22 =
    Integer.Sparse.merge node11 node21 := by decide +kernel

theorem node22_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node22 x = (Integer.Sparse.eval node11 x + (Integer.Sparse.eval node15 x + Integer.Sparse.eval node19 x)) := by
  rw [node22_check, Integer.Sparse.eval_merge]
  rw [node21_eval]

theorem node23_check : node23 =
    Integer.Sparse.merge node20 node22 := by decide +kernel

theorem node23_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node23 x = ((Integer.Sparse.eval node3 x + Integer.Sparse.eval node7 x) + (Integer.Sparse.eval node11 x + (Integer.Sparse.eval node15 x + Integer.Sparse.eval node19 x))) := by
  rw [node23_check, Integer.Sparse.eval_merge]
  rw [node20_eval, node22_eval]

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced finite sums for assembling the exact Gram certificate. -/

open scoped BigOperators

namespace MUB6.Certificate.GramAssembly

theorem sum_expand_5 {R : Type*} [AddCommMonoid R] (F : Fin 5 → R) :
    (∑ i, F i) = ((F 0 + F 1) + (F 2 + (F 3 + F 4))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + 0))))) = ((F 0 + F 1) + (F 2 + (F 3 + F 4)))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node3 x =
      ∑ j : Fin 5, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node3_eval]
  exact (sum_expand_5 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node7 x =
      ∑ j : Fin 5, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node7_eval]
  exact (sum_expand_5 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node11 x =
      ∑ j : Fin 5, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node11_eval]
  exact (sum_expand_5 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node15 x =
      ∑ j : Fin 5, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node15_eval]
  exact (sum_expand_5 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x =
      ∑ j : Fin 5, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node19_eval]
  exact (sum_expand_5 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem rows_eval (i : Fin 5) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 5, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  fin_cases i
  · exact row_eval_0 x
  · exact row_eval_1 x
  · exact row_eval_2 x
  · exact row_eval_3 x
  · exact row_eval_4 x

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 5, ∑ j : Fin 5, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 5, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node23_eval]
      exact (sum_expand_5 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Reindex0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem entry_reindex_0_0 :
    Integer.Sparse.reindex key entry_0_0 = GramEntries.Block0.entries 0 0 := by
  decide +kernel

theorem entry_reindex_0_1 :
    Integer.Sparse.reindex key entry_0_1 = GramEntries.Block0.entries 0 1 := by
  decide +kernel

theorem entry_reindex_0_2 :
    Integer.Sparse.reindex key entry_0_2 = GramEntries.Block0.entries 0 2 := by
  decide +kernel

theorem entry_reindex_0_3 :
    Integer.Sparse.reindex key entry_0_3 = GramEntries.Block0.entries 0 3 := by
  decide +kernel

theorem entry_reindex_0_4 :
    Integer.Sparse.reindex key entry_0_4 = GramEntries.Block0.entries 0 4 := by
  decide +kernel

theorem entries_reindex_0 (j : Fin 5) :
    Integer.Sparse.reindex key (entries 0 j) = GramEntries.Block0.entries 0 j := by
  fin_cases j
  · exact entry_reindex_0_0
  · exact entry_reindex_0_1
  · exact entry_reindex_0_2
  · exact entry_reindex_0_3
  · exact entry_reindex_0_4

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Reindex1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem entry_reindex_1_0 :
    Integer.Sparse.reindex key entry_1_0 = GramEntries.Block0.entries 1 0 := by
  decide +kernel

theorem entry_reindex_1_1 :
    Integer.Sparse.reindex key entry_1_1 = GramEntries.Block0.entries 1 1 := by
  decide +kernel

theorem entry_reindex_1_2 :
    Integer.Sparse.reindex key entry_1_2 = GramEntries.Block0.entries 1 2 := by
  decide +kernel

theorem entry_reindex_1_3 :
    Integer.Sparse.reindex key entry_1_3 = GramEntries.Block0.entries 1 3 := by
  decide +kernel

theorem entry_reindex_1_4 :
    Integer.Sparse.reindex key entry_1_4 = GramEntries.Block0.entries 1 4 := by
  decide +kernel

theorem entries_reindex_1 (j : Fin 5) :
    Integer.Sparse.reindex key (entries 1 j) = GramEntries.Block0.entries 1 j := by
  fin_cases j
  · exact entry_reindex_1_0
  · exact entry_reindex_1_1
  · exact entry_reindex_1_2
  · exact entry_reindex_1_3
  · exact entry_reindex_1_4

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Reindex2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem entry_reindex_2_0 :
    Integer.Sparse.reindex key entry_2_0 = GramEntries.Block0.entries 2 0 := by
  decide +kernel

theorem entry_reindex_2_1 :
    Integer.Sparse.reindex key entry_2_1 = GramEntries.Block0.entries 2 1 := by
  decide +kernel

theorem entry_reindex_2_2 :
    Integer.Sparse.reindex key entry_2_2 = GramEntries.Block0.entries 2 2 := by
  decide +kernel

theorem entry_reindex_2_3 :
    Integer.Sparse.reindex key entry_2_3 = GramEntries.Block0.entries 2 3 := by
  decide +kernel

theorem entry_reindex_2_4 :
    Integer.Sparse.reindex key entry_2_4 = GramEntries.Block0.entries 2 4 := by
  decide +kernel

theorem entries_reindex_2 (j : Fin 5) :
    Integer.Sparse.reindex key (entries 2 j) = GramEntries.Block0.entries 2 j := by
  fin_cases j
  · exact entry_reindex_2_0
  · exact entry_reindex_2_1
  · exact entry_reindex_2_2
  · exact entry_reindex_2_3
  · exact entry_reindex_2_4

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Reindex3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem entry_reindex_3_0 :
    Integer.Sparse.reindex key entry_3_0 = GramEntries.Block0.entries 3 0 := by
  decide +kernel

theorem entry_reindex_3_1 :
    Integer.Sparse.reindex key entry_3_1 = GramEntries.Block0.entries 3 1 := by
  decide +kernel

theorem entry_reindex_3_2 :
    Integer.Sparse.reindex key entry_3_2 = GramEntries.Block0.entries 3 2 := by
  decide +kernel

theorem entry_reindex_3_3 :
    Integer.Sparse.reindex key entry_3_3 = GramEntries.Block0.entries 3 3 := by
  decide +kernel

theorem entry_reindex_3_4 :
    Integer.Sparse.reindex key entry_3_4 = GramEntries.Block0.entries 3 4 := by
  decide +kernel

theorem entries_reindex_3 (j : Fin 5) :
    Integer.Sparse.reindex key (entries 3 j) = GramEntries.Block0.entries 3 j := by
  fin_cases j
  · exact entry_reindex_3_0
  · exact entry_reindex_3_1
  · exact entry_reindex_3_2
  · exact entry_reindex_3_3
  · exact entry_reindex_3_4

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Reindex4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem entry_reindex_4_0 :
    Integer.Sparse.reindex key entry_4_0 = GramEntries.Block0.entries 4 0 := by
  decide +kernel

theorem entry_reindex_4_1 :
    Integer.Sparse.reindex key entry_4_1 = GramEntries.Block0.entries 4 1 := by
  decide +kernel

theorem entry_reindex_4_2 :
    Integer.Sparse.reindex key entry_4_2 = GramEntries.Block0.entries 4 2 := by
  decide +kernel

theorem entry_reindex_4_3 :
    Integer.Sparse.reindex key entry_4_3 = GramEntries.Block0.entries 4 3 := by
  decide +kernel

theorem entry_reindex_4_4 :
    Integer.Sparse.reindex key entry_4_4 = GramEntries.Block0.entries 4 4 := by
  decide +kernel

theorem entries_reindex_4 (j : Fin 5) :
    Integer.Sparse.reindex key (entries 4 j) = GramEntries.Block0.entries 4 j := by
  fin_cases j
  · exact entry_reindex_4_0
  · exact entry_reindex_4_1
  · exact entry_reindex_4_2
  · exact entry_reindex_4_3
  · exact entry_reindex_4_4

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

theorem entries_reindex (i j : Fin 5) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block0.entries i j := by
  fin_cases i
  · exact entries_reindex_0 j
  · exact entries_reindex_1 j
  · exact entries_reindex_2 j
  · exact entries_reindex_3 j
  · exact entries_reindex_4 j

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck462 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form1 = rawRow462 := by decide +kernel

theorem rowCheck462 : row462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow462 := by decide +kernel

theorem rowEval462 (x : Key → ℝ) : Integer.Sparse.eval row462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck462, Integer.Sparse.eval_collectBalanced, rawRowCheck462]

theorem rawRowCheck463 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form1 = rawRow463 := by decide +kernel

theorem rowCheck463 : row463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow463 := by decide +kernel

theorem rowEval463 (x : Key → ℝ) : Integer.Sparse.eval row463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck463, Integer.Sparse.eval_collectBalanced, rawRowCheck463]

theorem rawRowCheck464 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form1 = rawRow464 := by decide +kernel

theorem rowCheck464 : row464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow464 := by decide +kernel

theorem rowEval464 (x : Key → ℝ) : Integer.Sparse.eval row464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck464, Integer.Sparse.eval_collectBalanced, rawRowCheck464]

theorem rawRowCheck465 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form1 = rawRow465 := by decide +kernel

theorem rowCheck465 : row465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow465 := by decide +kernel

theorem rowEval465 (x : Key → ℝ) : Integer.Sparse.eval row465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck465, Integer.Sparse.eval_collectBalanced, rawRowCheck465]

theorem rawRowCheck466 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form1 = rawRow466 := by decide +kernel

theorem rowCheck466 : row466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow466 := by decide +kernel

theorem rowEval466 (x : Key → ℝ) : Integer.Sparse.eval row466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck466, Integer.Sparse.eval_collectBalanced, rawRowCheck466]

theorem rawRowCheck467 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form1 = rawRow467 := by decide +kernel

theorem rowCheck467 : row467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow467 := by decide +kernel

theorem rowEval467 (x : Key → ℝ) : Integer.Sparse.eval row467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck467, Integer.Sparse.eval_collectBalanced, rawRowCheck467]

theorem rawRowCheck468 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form1 = rawRow468 := by decide +kernel

theorem rowCheck468 : row468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow468 := by decide +kernel

theorem rowEval468 (x : Key → ℝ) : Integer.Sparse.eval row468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck468, Integer.Sparse.eval_collectBalanced, rawRowCheck468]

theorem rawRowCheck469 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form1 = rawRow469 := by decide +kernel

theorem rowCheck469 : row469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow469 := by decide +kernel

theorem rowEval469 (x : Key → ℝ) : Integer.Sparse.eval row469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck469, Integer.Sparse.eval_collectBalanced, rawRowCheck469]

theorem rawRowCheck470 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form1 = rawRow470 := by decide +kernel

theorem rowCheck470 : row470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow470 := by decide +kernel

theorem rowEval470 (x : Key → ℝ) : Integer.Sparse.eval row470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck470, Integer.Sparse.eval_collectBalanced, rawRowCheck470]

theorem rawRowCheck471 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form1 = rawRow471 := by decide +kernel

theorem rowCheck471 : row471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow471 := by decide +kernel

theorem rowEval471 (x : Key → ℝ) : Integer.Sparse.eval row471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck471, Integer.Sparse.eval_collectBalanced, rawRowCheck471]

theorem rawRowCheck472 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form1 = rawRow472 := by decide +kernel

theorem rowCheck472 : row472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow472 := by decide +kernel

theorem rowEval472 (x : Key → ℝ) : Integer.Sparse.eval row472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck472, Integer.Sparse.eval_collectBalanced, rawRowCheck472]

theorem rawRowCheck473 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form1 = rawRow473 := by decide +kernel

theorem rowCheck473 : row473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow473 := by decide +kernel

theorem rowEval473 (x : Key → ℝ) : Integer.Sparse.eval row473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck473, Integer.Sparse.eval_collectBalanced, rawRowCheck473]

theorem rawRowCheck474 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form1 = rawRow474 := by decide +kernel

theorem rowCheck474 : row474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow474 := by decide +kernel

theorem rowEval474 (x : Key → ℝ) : Integer.Sparse.eval row474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck474, Integer.Sparse.eval_collectBalanced, rawRowCheck474]

theorem rawRowCheck475 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form1 = rawRow475 := by decide +kernel

theorem rowCheck475 : row475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow475 := by decide +kernel

theorem rowEval475 (x : Key → ℝ) : Integer.Sparse.eval row475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck475, Integer.Sparse.eval_collectBalanced, rawRowCheck475]

theorem rawRowCheck476 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form1 = rawRow476 := by decide +kernel

theorem rowCheck476 : row476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow476 := by decide +kernel

theorem rowEval476 (x : Key → ℝ) : Integer.Sparse.eval row476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck476, Integer.Sparse.eval_collectBalanced, rawRowCheck476]

theorem rawRowCheck477 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form1 = rawRow477 := by decide +kernel

theorem rowCheck477 : row477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow477 := by decide +kernel

theorem rowEval477 (x : Key → ℝ) : Integer.Sparse.eval row477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck477, Integer.Sparse.eval_collectBalanced, rawRowCheck477]

theorem rawRowCheck478 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form1 = rawRow478 := by decide +kernel

theorem rowCheck478 : row478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow478 := by decide +kernel

theorem rowEval478 (x : Key → ℝ) : Integer.Sparse.eval row478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck478, Integer.Sparse.eval_collectBalanced, rawRowCheck478]

theorem rawRowCheck479 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form1 = rawRow479 := by decide +kernel

theorem rowCheck479 : row479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow479 := by decide +kernel

theorem rowEval479 (x : Key → ℝ) : Integer.Sparse.eval row479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck479, Integer.Sparse.eval_collectBalanced, rawRowCheck479]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck480 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form1 = rawRow480 := by decide +kernel

theorem rowCheck480 : row480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow480 := by decide +kernel

theorem rowEval480 (x : Key → ℝ) : Integer.Sparse.eval row480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck480, Integer.Sparse.eval_collectBalanced, rawRowCheck480]

theorem rawRowCheck481 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form1 = rawRow481 := by decide +kernel

theorem rowCheck481 : row481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow481 := by decide +kernel

theorem rowEval481 (x : Key → ℝ) : Integer.Sparse.eval row481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck481, Integer.Sparse.eval_collectBalanced, rawRowCheck481]

theorem rawRowCheck482 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form1 = rawRow482 := by decide +kernel

theorem rowCheck482 : row482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow482 := by decide +kernel

theorem rowEval482 (x : Key → ℝ) : Integer.Sparse.eval row482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck482, Integer.Sparse.eval_collectBalanced, rawRowCheck482]

theorem rawRowCheck483 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form1 = rawRow483 := by decide +kernel

theorem rowCheck483 : row483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow483 := by decide +kernel

theorem rowEval483 (x : Key → ℝ) : Integer.Sparse.eval row483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck483, Integer.Sparse.eval_collectBalanced, rawRowCheck483]

theorem rawRowCheck484 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form1 = rawRow484 := by decide +kernel

theorem rowCheck484 : row484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow484 := by decide +kernel

theorem rowEval484 (x : Key → ℝ) : Integer.Sparse.eval row484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck484, Integer.Sparse.eval_collectBalanced, rawRowCheck484]

theorem rawRowCheck485 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form1 = rawRow485 := by decide +kernel

theorem rowCheck485 : row485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow485 := by decide +kernel

theorem rowEval485 (x : Key → ℝ) : Integer.Sparse.eval row485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck485, Integer.Sparse.eval_collectBalanced, rawRowCheck485]

theorem rawRowCheck486 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow486 := by decide +kernel

theorem rowCheck486 : row486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow486 := by decide +kernel

theorem rowEval486 (x : Key → ℝ) : Integer.Sparse.eval row486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck486, Integer.Sparse.eval_collectBalanced, rawRowCheck486]

theorem rawRowCheck487 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow487 := by decide +kernel

theorem rowCheck487 : row487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow487 := by decide +kernel

theorem rowEval487 (x : Key → ℝ) : Integer.Sparse.eval row487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck487, Integer.Sparse.eval_collectBalanced, rawRowCheck487]

theorem rawRowCheck488 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form1 = rawRow488 := by decide +kernel

theorem rowCheck488 : row488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow488 := by decide +kernel

theorem rowEval488 (x : Key → ℝ) : Integer.Sparse.eval row488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck488, Integer.Sparse.eval_collectBalanced, rawRowCheck488]

theorem rawRowCheck489 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form1 = rawRow489 := by decide +kernel

theorem rowCheck489 : row489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow489 := by decide +kernel

theorem rowEval489 (x : Key → ℝ) : Integer.Sparse.eval row489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck489, Integer.Sparse.eval_collectBalanced, rawRowCheck489]

theorem rawRowCheck490 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form1 = rawRow490 := by decide +kernel

theorem rowCheck490 : row490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow490 := by decide +kernel

theorem rowEval490 (x : Key → ℝ) : Integer.Sparse.eval row490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck490, Integer.Sparse.eval_collectBalanced, rawRowCheck490]

theorem rawRowCheck491 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form1 = rawRow491 := by decide +kernel

theorem rowCheck491 : row491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow491 := by decide +kernel

theorem rowEval491 (x : Key → ℝ) : Integer.Sparse.eval row491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck491, Integer.Sparse.eval_collectBalanced, rawRowCheck491]

theorem rawRowCheck492 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form1 = rawRow492 := by decide +kernel

theorem rowCheck492 : row492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow492 := by decide +kernel

theorem rowEval492 (x : Key → ℝ) : Integer.Sparse.eval row492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck492, Integer.Sparse.eval_collectBalanced, rawRowCheck492]

theorem rawRowCheck493 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form1 = rawRow493 := by decide +kernel

theorem rowCheck493 : row493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow493 := by decide +kernel

theorem rowEval493 (x : Key → ℝ) : Integer.Sparse.eval row493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck493, Integer.Sparse.eval_collectBalanced, rawRowCheck493]

theorem rawRowCheck494 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form1 = rawRow494 := by decide +kernel

theorem rowCheck494 : row494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow494 := by decide +kernel

theorem rowEval494 (x : Key → ℝ) : Integer.Sparse.eval row494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck494, Integer.Sparse.eval_collectBalanced, rawRowCheck494]

theorem rawRowCheck495 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form1 = rawRow495 := by decide +kernel

theorem rowCheck495 : row495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow495 := by decide +kernel

theorem rowEval495 (x : Key → ℝ) : Integer.Sparse.eval row495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck495, Integer.Sparse.eval_collectBalanced, rawRowCheck495]

theorem rawRowCheck496 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form1 = rawRow496 := by decide +kernel

theorem rowCheck496 : row496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow496 := by decide +kernel

theorem rowEval496 (x : Key → ℝ) : Integer.Sparse.eval row496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck496, Integer.Sparse.eval_collectBalanced, rawRowCheck496]

theorem rawRowCheck497 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form1 = rawRow497 := by decide +kernel

theorem rowCheck497 : row497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow497 := by decide +kernel

theorem rowEval497 (x : Key → ℝ) : Integer.Sparse.eval row497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck497, Integer.Sparse.eval_collectBalanced, rawRowCheck497]

theorem rawRowCheck498 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form1 = rawRow498 := by decide +kernel

theorem rowCheck498 : row498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow498 := by decide +kernel

theorem rowEval498 (x : Key → ℝ) : Integer.Sparse.eval row498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck498, Integer.Sparse.eval_collectBalanced, rawRowCheck498]

theorem rawRowCheck499 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form1 = rawRow499 := by decide +kernel

theorem rowCheck499 : row499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow499 := by decide +kernel

theorem rowEval499 (x : Key → ℝ) : Integer.Sparse.eval row499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck499, Integer.Sparse.eval_collectBalanced, rawRowCheck499]

theorem rawRowCheck500 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form1 = rawRow500 := by decide +kernel

theorem rowCheck500 : row500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow500 := by decide +kernel

theorem rowEval500 (x : Key → ℝ) : Integer.Sparse.eval row500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck500, Integer.Sparse.eval_collectBalanced, rawRowCheck500]

theorem rawRowCheck501 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form1 = rawRow501 := by decide +kernel

theorem rowCheck501 : row501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow501 := by decide +kernel

theorem rowEval501 (x : Key → ℝ) : Integer.Sparse.eval row501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck501, Integer.Sparse.eval_collectBalanced, rawRowCheck501]

theorem rawRowCheck502 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form1 = rawRow502 := by decide +kernel

theorem rowCheck502 : row502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow502 := by decide +kernel

theorem rowEval502 (x : Key → ℝ) : Integer.Sparse.eval row502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck502, Integer.Sparse.eval_collectBalanced, rawRowCheck502]

theorem rawRowCheck503 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form1 = rawRow503 := by decide +kernel

theorem rowCheck503 : row503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow503 := by decide +kernel

theorem rowEval503 (x : Key → ℝ) : Integer.Sparse.eval row503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck503, Integer.Sparse.eval_collectBalanced, rawRowCheck503]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck588 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form4 = rawRow588 := by decide +kernel

theorem rowCheck588 : row588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow588 := by decide +kernel

theorem rowEval588 (x : Key → ℝ) : Integer.Sparse.eval row588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck588, Integer.Sparse.eval_collectBalanced, rawRowCheck588]

theorem rawRowCheck589 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form4 = rawRow589 := by decide +kernel

theorem rowCheck589 : row589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow589 := by decide +kernel

theorem rowEval589 (x : Key → ℝ) : Integer.Sparse.eval row589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck589, Integer.Sparse.eval_collectBalanced, rawRowCheck589]

theorem rawRowCheck590 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form4 = rawRow590 := by decide +kernel

theorem rowCheck590 : row590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow590 := by decide +kernel

theorem rowEval590 (x : Key → ℝ) : Integer.Sparse.eval row590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck590, Integer.Sparse.eval_collectBalanced, rawRowCheck590]

theorem rawRowCheck591 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form4 = rawRow591 := by decide +kernel

theorem rowCheck591 : row591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow591 := by decide +kernel

theorem rowEval591 (x : Key → ℝ) : Integer.Sparse.eval row591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck591, Integer.Sparse.eval_collectBalanced, rawRowCheck591]

theorem rawRowCheck592 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form4 = rawRow592 := by decide +kernel

theorem rowCheck592 : row592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow592 := by decide +kernel

theorem rowEval592 (x : Key → ℝ) : Integer.Sparse.eval row592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck592, Integer.Sparse.eval_collectBalanced, rawRowCheck592]

theorem rawRowCheck593 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form4 = rawRow593 := by decide +kernel

theorem rowCheck593 : row593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow593 := by decide +kernel

theorem rowEval593 (x : Key → ℝ) : Integer.Sparse.eval row593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck593, Integer.Sparse.eval_collectBalanced, rawRowCheck593]

theorem rawRowCheck594 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form4 = rawRow594 := by decide +kernel

theorem rowCheck594 : row594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow594 := by decide +kernel

theorem rowEval594 (x : Key → ℝ) : Integer.Sparse.eval row594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck594, Integer.Sparse.eval_collectBalanced, rawRowCheck594]

theorem rawRowCheck595 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form4 = rawRow595 := by decide +kernel

theorem rowCheck595 : row595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow595 := by decide +kernel

theorem rowEval595 (x : Key → ℝ) : Integer.Sparse.eval row595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck595, Integer.Sparse.eval_collectBalanced, rawRowCheck595]

theorem rawRowCheck596 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form4 = rawRow596 := by decide +kernel

theorem rowCheck596 : row596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow596 := by decide +kernel

theorem rowEval596 (x : Key → ℝ) : Integer.Sparse.eval row596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck596, Integer.Sparse.eval_collectBalanced, rawRowCheck596]

theorem rawRowCheck597 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form4 = rawRow597 := by decide +kernel

theorem rowCheck597 : row597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow597 := by decide +kernel

theorem rowEval597 (x : Key → ℝ) : Integer.Sparse.eval row597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck597, Integer.Sparse.eval_collectBalanced, rawRowCheck597]

theorem rawRowCheck598 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form4 = rawRow598 := by decide +kernel

theorem rowCheck598 : row598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow598 := by decide +kernel

theorem rowEval598 (x : Key → ℝ) : Integer.Sparse.eval row598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck598, Integer.Sparse.eval_collectBalanced, rawRowCheck598]

theorem rawRowCheck599 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form4 = rawRow599 := by decide +kernel

theorem rowCheck599 : row599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow599 := by decide +kernel

theorem rowEval599 (x : Key → ℝ) : Integer.Sparse.eval row599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck599, Integer.Sparse.eval_collectBalanced, rawRowCheck599]

theorem rawRowCheck600 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form4 = rawRow600 := by decide +kernel

theorem rowCheck600 : row600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow600 := by decide +kernel

theorem rowEval600 (x : Key → ℝ) : Integer.Sparse.eval row600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck600, Integer.Sparse.eval_collectBalanced, rawRowCheck600]

theorem rawRowCheck601 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form4 = rawRow601 := by decide +kernel

theorem rowCheck601 : row601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow601 := by decide +kernel

theorem rowEval601 (x : Key → ℝ) : Integer.Sparse.eval row601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck601, Integer.Sparse.eval_collectBalanced, rawRowCheck601]

theorem rawRowCheck602 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form4 = rawRow602 := by decide +kernel

theorem rowCheck602 : row602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow602 := by decide +kernel

theorem rowEval602 (x : Key → ℝ) : Integer.Sparse.eval row602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck602, Integer.Sparse.eval_collectBalanced, rawRowCheck602]

theorem rawRowCheck603 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form4 = rawRow603 := by decide +kernel

theorem rowCheck603 : row603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow603 := by decide +kernel

theorem rowEval603 (x : Key → ℝ) : Integer.Sparse.eval row603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck603, Integer.Sparse.eval_collectBalanced, rawRowCheck603]

theorem rawRowCheck604 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form4 = rawRow604 := by decide +kernel

theorem rowCheck604 : row604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow604 := by decide +kernel

theorem rowEval604 (x : Key → ℝ) : Integer.Sparse.eval row604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck604, Integer.Sparse.eval_collectBalanced, rawRowCheck604]

theorem rawRowCheck605 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form4 = rawRow605 := by decide +kernel

theorem rowCheck605 : row605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow605 := by decide +kernel

theorem rowEval605 (x : Key → ℝ) : Integer.Sparse.eval row605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck605, Integer.Sparse.eval_collectBalanced, rawRowCheck605]

theorem rawRowCheck606 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form4 = rawRow606 := by decide +kernel

theorem rowCheck606 : row606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow606 := by decide +kernel

theorem rowEval606 (x : Key → ℝ) : Integer.Sparse.eval row606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck606, Integer.Sparse.eval_collectBalanced, rawRowCheck606]

theorem rawRowCheck607 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form4 = rawRow607 := by decide +kernel

theorem rowCheck607 : row607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow607 := by decide +kernel

theorem rowEval607 (x : Key → ℝ) : Integer.Sparse.eval row607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck607, Integer.Sparse.eval_collectBalanced, rawRowCheck607]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck608 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form4 = rawRow608 := by decide +kernel

theorem rowCheck608 : row608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow608 := by decide +kernel

theorem rowEval608 (x : Key → ℝ) : Integer.Sparse.eval row608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck608, Integer.Sparse.eval_collectBalanced, rawRowCheck608]

theorem rawRowCheck609 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form4 = rawRow609 := by decide +kernel

theorem rowCheck609 : row609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow609 := by decide +kernel

theorem rowEval609 (x : Key → ℝ) : Integer.Sparse.eval row609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck609, Integer.Sparse.eval_collectBalanced, rawRowCheck609]

theorem rawRowCheck610 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form4 = rawRow610 := by decide +kernel

theorem rowCheck610 : row610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow610 := by decide +kernel

theorem rowEval610 (x : Key → ℝ) : Integer.Sparse.eval row610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck610, Integer.Sparse.eval_collectBalanced, rawRowCheck610]

theorem rawRowCheck611 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form4 = rawRow611 := by decide +kernel

theorem rowCheck611 : row611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow611 := by decide +kernel

theorem rowEval611 (x : Key → ℝ) : Integer.Sparse.eval row611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck611, Integer.Sparse.eval_collectBalanced, rawRowCheck611]

theorem rawRowCheck612 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form4 = rawRow612 := by decide +kernel

theorem rowCheck612 : row612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow612 := by decide +kernel

theorem rowEval612 (x : Key → ℝ) : Integer.Sparse.eval row612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck612, Integer.Sparse.eval_collectBalanced, rawRowCheck612]

theorem rawRowCheck613 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form4 = rawRow613 := by decide +kernel

theorem rowCheck613 : row613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow613 := by decide +kernel

theorem rowEval613 (x : Key → ℝ) : Integer.Sparse.eval row613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck613, Integer.Sparse.eval_collectBalanced, rawRowCheck613]

theorem rawRowCheck614 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form4 = rawRow614 := by decide +kernel

theorem rowCheck614 : row614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow614 := by decide +kernel

theorem rowEval614 (x : Key → ℝ) : Integer.Sparse.eval row614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck614, Integer.Sparse.eval_collectBalanced, rawRowCheck614]

theorem rawRowCheck615 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form4 = rawRow615 := by decide +kernel

theorem rowCheck615 : row615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow615 := by decide +kernel

theorem rowEval615 (x : Key → ℝ) : Integer.Sparse.eval row615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck615, Integer.Sparse.eval_collectBalanced, rawRowCheck615]

theorem rawRowCheck616 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form4 = rawRow616 := by decide +kernel

theorem rowCheck616 : row616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow616 := by decide +kernel

theorem rowEval616 (x : Key → ℝ) : Integer.Sparse.eval row616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck616, Integer.Sparse.eval_collectBalanced, rawRowCheck616]

theorem rawRowCheck617 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form4 = rawRow617 := by decide +kernel

theorem rowCheck617 : row617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow617 := by decide +kernel

theorem rowEval617 (x : Key → ℝ) : Integer.Sparse.eval row617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck617, Integer.Sparse.eval_collectBalanced, rawRowCheck617]

theorem rawRowCheck618 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form4 = rawRow618 := by decide +kernel

theorem rowCheck618 : row618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow618 := by decide +kernel

theorem rowEval618 (x : Key → ℝ) : Integer.Sparse.eval row618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck618, Integer.Sparse.eval_collectBalanced, rawRowCheck618]

theorem rawRowCheck619 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form4 = rawRow619 := by decide +kernel

theorem rowCheck619 : row619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow619 := by decide +kernel

theorem rowEval619 (x : Key → ℝ) : Integer.Sparse.eval row619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck619, Integer.Sparse.eval_collectBalanced, rawRowCheck619]

theorem rawRowCheck620 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form4 = rawRow620 := by decide +kernel

theorem rowCheck620 : row620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow620 := by decide +kernel

theorem rowEval620 (x : Key → ℝ) : Integer.Sparse.eval row620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck620, Integer.Sparse.eval_collectBalanced, rawRowCheck620]

theorem rawRowCheck621 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form4 = rawRow621 := by decide +kernel

theorem rowCheck621 : row621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow621 := by decide +kernel

theorem rowEval621 (x : Key → ℝ) : Integer.Sparse.eval row621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck621, Integer.Sparse.eval_collectBalanced, rawRowCheck621]

theorem rawRowCheck622 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form4 = rawRow622 := by decide +kernel

theorem rowCheck622 : row622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow622 := by decide +kernel

theorem rowEval622 (x : Key → ℝ) : Integer.Sparse.eval row622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck622, Integer.Sparse.eval_collectBalanced, rawRowCheck622]

theorem rawRowCheck623 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form4 = rawRow623 := by decide +kernel

theorem rowCheck623 : row623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow623 := by decide +kernel

theorem rowEval623 (x : Key → ℝ) : Integer.Sparse.eval row623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck623, Integer.Sparse.eval_collectBalanced, rawRowCheck623]

theorem rawRowCheck624 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form4 = rawRow624 := by decide +kernel

theorem rowCheck624 : row624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow624 := by decide +kernel

theorem rowEval624 (x : Key → ℝ) : Integer.Sparse.eval row624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck624, Integer.Sparse.eval_collectBalanced, rawRowCheck624]

theorem rawRowCheck625 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form4 = rawRow625 := by decide +kernel

theorem rowCheck625 : row625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow625 := by decide +kernel

theorem rowEval625 (x : Key → ℝ) : Integer.Sparse.eval row625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck625, Integer.Sparse.eval_collectBalanced, rawRowCheck625]

theorem rawRowCheck626 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form4 = rawRow626 := by decide +kernel

theorem rowCheck626 : row626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow626 := by decide +kernel

theorem rowEval626 (x : Key → ℝ) : Integer.Sparse.eval row626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck626, Integer.Sparse.eval_collectBalanced, rawRowCheck626]

theorem rawRowCheck627 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form4 = rawRow627 := by decide +kernel

theorem rowCheck627 : row627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow627 := by decide +kernel

theorem rowEval627 (x : Key → ℝ) : Integer.Sparse.eval row627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck627, Integer.Sparse.eval_collectBalanced, rawRowCheck627]

theorem rawRowCheck628 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form4 = rawRow628 := by decide +kernel

theorem rowCheck628 : row628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow628 := by decide +kernel

theorem rowEval628 (x : Key → ℝ) : Integer.Sparse.eval row628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck628, Integer.Sparse.eval_collectBalanced, rawRowCheck628]

theorem rawRowCheck629 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form4 = rawRow629 := by decide +kernel

theorem rowCheck629 : row629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow629 := by decide +kernel

theorem rowEval629 (x : Key → ℝ) : Integer.Sparse.eval row629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck629, Integer.Sparse.eval_collectBalanced, rawRowCheck629]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block0.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form4.terms k).tag (GramFunctions.Block0.form4.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval462 x
  · exact rowEval463 x
  · exact rowEval464 x
  · exact rowEval465 x
  · exact rowEval466 x
  · exact rowEval467 x
  · exact rowEval468 x
  · exact rowEval469 x
  · exact rowEval470 x
  · exact rowEval471 x
  · exact rowEval472 x
  · exact rowEval473 x
  · exact rowEval474 x
  · exact rowEval475 x
  · exact rowEval476 x
  · exact rowEval477 x
  · exact rowEval478 x
  · exact rowEval479 x
  · exact rowEval480 x
  · exact rowEval481 x
  · exact rowEval482 x
  · exact rowEval483 x
  · exact rowEval484 x
  · exact rowEval485 x
  · exact rowEval486 x
  · exact rowEval487 x
  · exact rowEval488 x
  · exact rowEval489 x
  · exact rowEval490 x
  · exact rowEval491 x
  · exact rowEval492 x
  · exact rowEval493 x
  · exact rowEval494 x
  · exact rowEval495 x
  · exact rowEval496 x
  · exact rowEval497 x
  · exact rowEval498 x
  · exact rowEval499 x
  · exact rowEval500 x
  · exact rowEval501 x
  · exact rowEval502 x
  · exact rowEval503 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block0.form4.mixedGram GramFunctions.Block0.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form4 GramFunctions.Block0.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block0.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form4.terms k).tag (GramFunctions.Block0.form4.terms k).charge GramFunctions.Block0.form4) x := by
  fin_cases k
  · exact rowEval588 x
  · exact rowEval589 x
  · exact rowEval590 x
  · exact rowEval591 x
  · exact rowEval592 x
  · exact rowEval593 x
  · exact rowEval594 x
  · exact rowEval595 x
  · exact rowEval596 x
  · exact rowEval597 x
  · exact rowEval598 x
  · exact rowEval599 x
  · exact rowEval600 x
  · exact rowEval601 x
  · exact rowEval602 x
  · exact rowEval603 x
  · exact rowEval604 x
  · exact rowEval605 x
  · exact rowEval606 x
  · exact rowEval607 x
  · exact rowEval608 x
  · exact rowEval609 x
  · exact rowEval610 x
  · exact rowEval611 x
  · exact rowEval612 x
  · exact rowEval613 x
  · exact rowEval614 x
  · exact rowEval615 x
  · exact rowEval616 x
  · exact rowEval617 x
  · exact rowEval618 x
  · exact rowEval619 x
  · exact rowEval620 x
  · exact rowEval621 x
  · exact rowEval622 x
  · exact rowEval623 x
  · exact rowEval624 x
  · exact rowEval625 x
  · exact rowEval626 x
  · exact rowEval627 x
  · exact rowEval628 x
  · exact rowEval629 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block0.form4.mixedGram GramFunctions.Block0.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form4 GramFunctions.Block0.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

theorem entryEvalRow4 (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 4).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval4_0_e B hB
  · exact entryEval4_1 B hB
  · exact entryEval4_2_e B hB
  · exact entryEval4_3_e B hB
  · exact entryEval4_4 B hB

theorem entryEval (i j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms i).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases i
  · exact entryEvalRow0_e j B hB
  · exact entryEvalRow1_e j B hB
  · exact entryEvalRow2_e j B hB
  · exact entryEvalRow3_e j B hB
  · exact entryEvalRow4 j B hB

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Semantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramAssembly.Block0

theorem indexed_entry_eval (i j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (fun k => GramNormalization.eval B (key k)) =
      (GramFunctions.Block0.forms i).mixedGram (GramFunctions.Block0.forms j) B := by
  have he := Integer.Sparse.eval_reindex key (entries i j) (GramNormalization.eval B)
  rw [entries_reindex] at he
  exact he.symm.trans (GramEntries.Block0.entryEval i j B hB)

theorem weights_real (i j : Fin 5) :
    (weights i j : ℝ) = realMatrix GramData.Block0.Z i j := by
  change (weights i j : ℝ) = (GramData.Block0.Z i j : ℝ)
  exact_mod_cast weights_cast i j

theorem polynomial_interpretation_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval polynomial (fun k => GramNormalization.eval B (key k)) =
      GramNonnegative.quadratic0 B := by
  rw [polynomial_eval]
  unfold GramNonnegative.quadratic0
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [indexed_entry_eval i j B hB, weights_real]

end MUB6.Certificate.GramAssembly.Block0

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block0.polynomial_interpretation_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block0.polynomial_interpretation_e_oai
