-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:28:10.292188+00:00
-- url     : https://prove2.me/submissions/76d62db2-a0a8-439b-8512-b4f37d386821

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E013
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_2_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1674 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form7 = rawRow1674 := by decide +kernel

theorem rowCheck1674 : row1674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1674 := by decide +kernel

theorem rowEval1674 (x : Key → ℝ) : Integer.Sparse.eval row1674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1674, Integer.Sparse.eval_collectBalanced, rawRowCheck1674]

theorem rawRowCheck1675 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form7 = rawRow1675 := by decide +kernel

theorem rowCheck1675 : row1675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1675 := by decide +kernel

theorem rowEval1675 (x : Key → ℝ) : Integer.Sparse.eval row1675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1675, Integer.Sparse.eval_collectBalanced, rawRowCheck1675]

theorem rawRowCheck1676 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form7 = rawRow1676 := by decide +kernel

theorem rowCheck1676 : row1676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1676 := by decide +kernel

theorem rowEval1676 (x : Key → ℝ) : Integer.Sparse.eval row1676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1676, Integer.Sparse.eval_collectBalanced, rawRowCheck1676]

theorem rawRowCheck1683 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form7 = rawRow1683 := by decide +kernel

theorem rowCheck1683 : row1683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1683 := by decide +kernel

theorem rowEval1683 (x : Key → ℝ) : Integer.Sparse.eval row1683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1683, Integer.Sparse.eval_collectBalanced, rawRowCheck1683]

theorem rawRowCheck1684 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form7 = rawRow1684 := by decide +kernel

theorem rowCheck1684 : row1684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1684 := by decide +kernel

theorem rowEval1684 (x : Key → ℝ) : Integer.Sparse.eval row1684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1684, Integer.Sparse.eval_collectBalanced, rawRowCheck1684]

theorem rawRowCheck1685 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form7 = rawRow1685 := by decide +kernel

theorem rowCheck1685 : row1685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1685 := by decide +kernel

theorem rowEval1685 (x : Key → ℝ) : Integer.Sparse.eval row1685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1685, Integer.Sparse.eval_collectBalanced, rawRowCheck1685]

theorem rawRowCheck1704 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form8 = rawRow1704 := by decide +kernel

theorem rowCheck1704 : row1704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1704 := by decide +kernel

theorem rowEval1704 (x : Key → ℝ) : Integer.Sparse.eval row1704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1704, Integer.Sparse.eval_collectBalanced, rawRowCheck1704]

theorem rawRowCheck1705 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form8 = rawRow1705 := by decide +kernel

theorem rowCheck1705 : row1705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1705 := by decide +kernel

theorem rowEval1705 (x : Key → ℝ) : Integer.Sparse.eval row1705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1705, Integer.Sparse.eval_collectBalanced, rawRowCheck1705]

theorem rawRowCheck1706 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form8 = rawRow1706 := by decide +kernel

theorem rowCheck1706 : row1706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1706 := by decide +kernel

theorem rowEval1706 (x : Key → ℝ) : Integer.Sparse.eval row1706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1706, Integer.Sparse.eval_collectBalanced, rawRowCheck1706]

theorem rawRowCheck1713 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form8 = rawRow1713 := by decide +kernel

theorem rowCheck1713 : row1713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1713 := by decide +kernel

theorem rowEval1713 (x : Key → ℝ) : Integer.Sparse.eval row1713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1713, Integer.Sparse.eval_collectBalanced, rawRowCheck1713]

theorem rawRowCheck1714 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form8 = rawRow1714 := by decide +kernel

theorem rowCheck1714 : row1714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1714 := by decide +kernel

theorem rowEval1714 (x : Key → ℝ) : Integer.Sparse.eval row1714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1714, Integer.Sparse.eval_collectBalanced, rawRowCheck1714]

theorem rawRowCheck1715 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form8 = rawRow1715 := by decide +kernel

theorem rowCheck1715 : row1715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1715 := by decide +kernel

theorem rowEval1715 (x : Key → ℝ) : Integer.Sparse.eval row1715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1715, Integer.Sparse.eval_collectBalanced, rawRowCheck1715]

theorem rawRowCheck1734 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form9 = rawRow1734 := by decide +kernel

theorem rowCheck1734 : row1734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1734 := by decide +kernel

theorem rowEval1734 (x : Key → ℝ) : Integer.Sparse.eval row1734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1734, Integer.Sparse.eval_collectBalanced, rawRowCheck1734]

theorem rawRowCheck1735 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form9 = rawRow1735 := by decide +kernel

theorem rowCheck1735 : row1735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1735 := by decide +kernel

theorem rowEval1735 (x : Key → ℝ) : Integer.Sparse.eval row1735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1735, Integer.Sparse.eval_collectBalanced, rawRowCheck1735]

theorem rawRowCheck1736 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form9 = rawRow1736 := by decide +kernel

theorem rowCheck1736 : row1736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1736 := by decide +kernel

theorem rowEval1736 (x : Key → ℝ) : Integer.Sparse.eval row1736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1736, Integer.Sparse.eval_collectBalanced, rawRowCheck1736]

theorem rawRowCheck1743 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form9 = rawRow1743 := by decide +kernel

theorem rowCheck1743 : row1743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1743 := by decide +kernel

theorem rowEval1743 (x : Key → ℝ) : Integer.Sparse.eval row1743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1743, Integer.Sparse.eval_collectBalanced, rawRowCheck1743]

theorem rawRowCheck1744 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form9 = rawRow1744 := by decide +kernel

theorem rowCheck1744 : row1744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1744 := by decide +kernel

theorem rowEval1744 (x : Key → ℝ) : Integer.Sparse.eval row1744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1744, Integer.Sparse.eval_collectBalanced, rawRowCheck1744]

theorem rawRowCheck1745 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form9 = rawRow1745 := by decide +kernel

theorem rowCheck1745 : row1745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1745 := by decide +kernel

theorem rowEval1745 (x : Key → ℝ) : Integer.Sparse.eval row1745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1745, Integer.Sparse.eval_collectBalanced, rawRowCheck1745]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck4842 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form1 = rawRow4842 := by decide +kernel

theorem rowCheck4842 : row4842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4842 := by decide +kernel

theorem rowEval4842 (x : Key → ℝ) : Integer.Sparse.eval row4842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4842, Integer.Sparse.eval_collectBalanced, rawRowCheck4842]

theorem rawRowCheck4843 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form1 = rawRow4843 := by decide +kernel

theorem rowCheck4843 : row4843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4843 := by decide +kernel

theorem rowEval4843 (x : Key → ℝ) : Integer.Sparse.eval row4843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4843, Integer.Sparse.eval_collectBalanced, rawRowCheck4843]

theorem rawRowCheck4844 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form1 = rawRow4844 := by decide +kernel

theorem rowCheck4844 : row4844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4844 := by decide +kernel

theorem rowEval4844 (x : Key → ℝ) : Integer.Sparse.eval row4844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4844, Integer.Sparse.eval_collectBalanced, rawRowCheck4844]

theorem rawRowCheck4845 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form1 = rawRow4845 := by decide +kernel

theorem rowCheck4845 : row4845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4845 := by decide +kernel

theorem rowEval4845 (x : Key → ℝ) : Integer.Sparse.eval row4845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4845, Integer.Sparse.eval_collectBalanced, rawRowCheck4845]

theorem rawRowCheck4846 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form1 = rawRow4846 := by decide +kernel

theorem rowCheck4846 : row4846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4846 := by decide +kernel

theorem rowEval4846 (x : Key → ℝ) : Integer.Sparse.eval row4846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4846, Integer.Sparse.eval_collectBalanced, rawRowCheck4846]

theorem rawRowCheck4847 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form1 = rawRow4847 := by decide +kernel

theorem rowCheck4847 : row4847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4847 := by decide +kernel

theorem rowEval4847 (x : Key → ℝ) : Integer.Sparse.eval row4847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4847, Integer.Sparse.eval_collectBalanced, rawRowCheck4847]

theorem rawRowCheck4848 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form1 = rawRow4848 := by decide +kernel

theorem rowCheck4848 : row4848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4848 := by decide +kernel

theorem rowEval4848 (x : Key → ℝ) : Integer.Sparse.eval row4848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4848, Integer.Sparse.eval_collectBalanced, rawRowCheck4848]

theorem rawRowCheck4849 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form1 = rawRow4849 := by decide +kernel

theorem rowCheck4849 : row4849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4849 := by decide +kernel

theorem rowEval4849 (x : Key → ℝ) : Integer.Sparse.eval row4849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4849, Integer.Sparse.eval_collectBalanced, rawRowCheck4849]

theorem rawRowCheck4850 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form1 = rawRow4850 := by decide +kernel

theorem rowCheck4850 : row4850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4850 := by decide +kernel

theorem rowEval4850 (x : Key → ℝ) : Integer.Sparse.eval row4850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4850, Integer.Sparse.eval_collectBalanced, rawRowCheck4850]

theorem rawRowCheck4851 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form1 = rawRow4851 := by decide +kernel

theorem rowCheck4851 : row4851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4851 := by decide +kernel

theorem rowEval4851 (x : Key → ℝ) : Integer.Sparse.eval row4851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4851, Integer.Sparse.eval_collectBalanced, rawRowCheck4851]

theorem rawRowCheck4852 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form1 = rawRow4852 := by decide +kernel

theorem rowCheck4852 : row4852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4852 := by decide +kernel

theorem rowEval4852 (x : Key → ℝ) : Integer.Sparse.eval row4852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4852, Integer.Sparse.eval_collectBalanced, rawRowCheck4852]

theorem rawRowCheck4853 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form1 = rawRow4853 := by decide +kernel

theorem rowCheck4853 : row4853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4853 := by decide +kernel

theorem rowEval4853 (x : Key → ℝ) : Integer.Sparse.eval row4853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4853, Integer.Sparse.eval_collectBalanced, rawRowCheck4853]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1494 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form1 = rawRow1494 := by decide +kernel

theorem rowCheck1494 : row1494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1494 := by decide +kernel

theorem rowEval1494 (x : Key → ℝ) : Integer.Sparse.eval row1494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1494, Integer.Sparse.eval_collectBalanced, rawRowCheck1494]

theorem rawRowCheck1495 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form1 = rawRow1495 := by decide +kernel

theorem rowCheck1495 : row1495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1495 := by decide +kernel

theorem rowEval1495 (x : Key → ℝ) : Integer.Sparse.eval row1495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1495, Integer.Sparse.eval_collectBalanced, rawRowCheck1495]

theorem rawRowCheck1496 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form1 = rawRow1496 := by decide +kernel

theorem rowCheck1496 : row1496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1496 := by decide +kernel

theorem rowEval1496 (x : Key → ℝ) : Integer.Sparse.eval row1496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1496, Integer.Sparse.eval_collectBalanced, rawRowCheck1496]

theorem rawRowCheck1503 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form1 = rawRow1503 := by decide +kernel

theorem rowCheck1503 : row1503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1503 := by decide +kernel

theorem rowEval1503 (x : Key → ℝ) : Integer.Sparse.eval row1503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1503, Integer.Sparse.eval_collectBalanced, rawRowCheck1503]

theorem rawRowCheck1504 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form1 = rawRow1504 := by decide +kernel

theorem rowCheck1504 : row1504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1504 := by decide +kernel

theorem rowEval1504 (x : Key → ℝ) : Integer.Sparse.eval row1504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1504, Integer.Sparse.eval_collectBalanced, rawRowCheck1504]

theorem rawRowCheck1505 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form1 = rawRow1505 := by decide +kernel

theorem rowCheck1505 : row1505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1505 := by decide +kernel

theorem rowEval1505 (x : Key → ℝ) : Integer.Sparse.eval row1505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1505, Integer.Sparse.eval_collectBalanced, rawRowCheck1505]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1554 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form3 = rawRow1554 := by decide +kernel

theorem rowCheck1554 : row1554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1554 := by decide +kernel

theorem rowEval1554 (x : Key → ℝ) : Integer.Sparse.eval row1554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1554, Integer.Sparse.eval_collectBalanced, rawRowCheck1554]

theorem rawRowCheck1555 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form3 = rawRow1555 := by decide +kernel

theorem rowCheck1555 : row1555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1555 := by decide +kernel

theorem rowEval1555 (x : Key → ℝ) : Integer.Sparse.eval row1555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1555, Integer.Sparse.eval_collectBalanced, rawRowCheck1555]

theorem rawRowCheck1556 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form3 = rawRow1556 := by decide +kernel

theorem rowCheck1556 : row1556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1556 := by decide +kernel

theorem rowEval1556 (x : Key → ℝ) : Integer.Sparse.eval row1556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1556, Integer.Sparse.eval_collectBalanced, rawRowCheck1556]

theorem rawRowCheck1563 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form3 = rawRow1563 := by decide +kernel

theorem rowCheck1563 : row1563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1563 := by decide +kernel

theorem rowEval1563 (x : Key → ℝ) : Integer.Sparse.eval row1563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1563, Integer.Sparse.eval_collectBalanced, rawRowCheck1563]

theorem rawRowCheck1564 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form3 = rawRow1564 := by decide +kernel

theorem rowCheck1564 : row1564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1564 := by decide +kernel

theorem rowEval1564 (x : Key → ℝ) : Integer.Sparse.eval row1564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1564, Integer.Sparse.eval_collectBalanced, rawRowCheck1564]

theorem rawRowCheck1565 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form3 = rawRow1565 := by decide +kernel

theorem rowCheck1565 : row1565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1565 := by decide +kernel

theorem rowEval1565 (x : Key → ℝ) : Integer.Sparse.eval row1565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1565, Integer.Sparse.eval_collectBalanced, rawRowCheck1565]

theorem rawRowCheck1584 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form4 = rawRow1584 := by decide +kernel

theorem rowCheck1584 : row1584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1584 := by decide +kernel

theorem rowEval1584 (x : Key → ℝ) : Integer.Sparse.eval row1584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1584, Integer.Sparse.eval_collectBalanced, rawRowCheck1584]

theorem rawRowCheck1585 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form4 = rawRow1585 := by decide +kernel

theorem rowCheck1585 : row1585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1585 := by decide +kernel

theorem rowEval1585 (x : Key → ℝ) : Integer.Sparse.eval row1585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1585, Integer.Sparse.eval_collectBalanced, rawRowCheck1585]

theorem rawRowCheck1586 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form4 = rawRow1586 := by decide +kernel

theorem rowCheck1586 : row1586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1586 := by decide +kernel

theorem rowEval1586 (x : Key → ℝ) : Integer.Sparse.eval row1586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1586, Integer.Sparse.eval_collectBalanced, rawRowCheck1586]

theorem rawRowCheck1593 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form4 = rawRow1593 := by decide +kernel

theorem rowCheck1593 : row1593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1593 := by decide +kernel

theorem rowEval1593 (x : Key → ℝ) : Integer.Sparse.eval row1593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1593, Integer.Sparse.eval_collectBalanced, rawRowCheck1593]

theorem rawRowCheck1594 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form4 = rawRow1594 := by decide +kernel

theorem rowCheck1594 : row1594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1594 := by decide +kernel

theorem rowEval1594 (x : Key → ℝ) : Integer.Sparse.eval row1594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1594, Integer.Sparse.eval_collectBalanced, rawRowCheck1594]

theorem rawRowCheck1595 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form4 = rawRow1595 := by decide +kernel

theorem rowCheck1595 : row1595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1595 := by decide +kernel

theorem rowEval1595 (x : Key → ℝ) : Integer.Sparse.eval row1595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1595, Integer.Sparse.eval_collectBalanced, rawRowCheck1595]

theorem rawRowCheck1614 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form5 = rawRow1614 := by decide +kernel

theorem rowCheck1614 : row1614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1614 := by decide +kernel

theorem rowEval1614 (x : Key → ℝ) : Integer.Sparse.eval row1614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1614, Integer.Sparse.eval_collectBalanced, rawRowCheck1614]

theorem rawRowCheck1615 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form5 = rawRow1615 := by decide +kernel

theorem rowCheck1615 : row1615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1615 := by decide +kernel

theorem rowEval1615 (x : Key → ℝ) : Integer.Sparse.eval row1615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1615, Integer.Sparse.eval_collectBalanced, rawRowCheck1615]

theorem rawRowCheck1616 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form5 = rawRow1616 := by decide +kernel

theorem rowCheck1616 : row1616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1616 := by decide +kernel

theorem rowEval1616 (x : Key → ℝ) : Integer.Sparse.eval row1616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1616, Integer.Sparse.eval_collectBalanced, rawRowCheck1616]

theorem rawRowCheck1623 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form5 = rawRow1623 := by decide +kernel

theorem rowCheck1623 : row1623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1623 := by decide +kernel

theorem rowEval1623 (x : Key → ℝ) : Integer.Sparse.eval row1623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1623, Integer.Sparse.eval_collectBalanced, rawRowCheck1623]

theorem rawRowCheck1624 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form5 = rawRow1624 := by decide +kernel

theorem rowCheck1624 : row1624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1624 := by decide +kernel

theorem rowEval1624 (x : Key → ℝ) : Integer.Sparse.eval row1624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1624, Integer.Sparse.eval_collectBalanced, rawRowCheck1624]

theorem rawRowCheck1625 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form5 = rawRow1625 := by decide +kernel

theorem rowCheck1625 : row1625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1625 := by decide +kernel

theorem rowEval1625 (x : Key → ℝ) : Integer.Sparse.eval row1625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1625, Integer.Sparse.eval_collectBalanced, rawRowCheck1625]

theorem rawRowCheck1644 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form6 = rawRow1644 := by decide +kernel

theorem rowCheck1644 : row1644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1644 := by decide +kernel

theorem rowEval1644 (x : Key → ℝ) : Integer.Sparse.eval row1644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1644, Integer.Sparse.eval_collectBalanced, rawRowCheck1644]

theorem rawRowCheck1645 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form6 = rawRow1645 := by decide +kernel

theorem rowCheck1645 : row1645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1645 := by decide +kernel

theorem rowEval1645 (x : Key → ℝ) : Integer.Sparse.eval row1645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1645, Integer.Sparse.eval_collectBalanced, rawRowCheck1645]

theorem rawRowCheck1646 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form6 = rawRow1646 := by decide +kernel

theorem rowCheck1646 : row1646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1646 := by decide +kernel

theorem rowEval1646 (x : Key → ℝ) : Integer.Sparse.eval row1646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1646, Integer.Sparse.eval_collectBalanced, rawRowCheck1646]

theorem rawRowCheck1653 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form6 = rawRow1653 := by decide +kernel

theorem rowCheck1653 : row1653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1653 := by decide +kernel

theorem rowEval1653 (x : Key → ℝ) : Integer.Sparse.eval row1653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1653, Integer.Sparse.eval_collectBalanced, rawRowCheck1653]

theorem rawRowCheck1654 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form6 = rawRow1654 := by decide +kernel

theorem rowCheck1654 : row1654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1654 := by decide +kernel

theorem rowEval1654 (x : Key → ℝ) : Integer.Sparse.eval row1654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1654, Integer.Sparse.eval_collectBalanced, rawRowCheck1654]

theorem rawRowCheck1655 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form6 = rawRow1655 := by decide +kernel

theorem rowCheck1655 : row1655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1655 := by decide +kernel

theorem rowEval1655 (x : Key → ℝ) : Integer.Sparse.eval row1655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1655, Integer.Sparse.eval_collectBalanced, rawRowCheck1655]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck4866 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form3 = rawRow4866 := by decide +kernel

theorem rowCheck4866 : row4866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4866 := by decide +kernel

theorem rowEval4866 (x : Key → ℝ) : Integer.Sparse.eval row4866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4866, Integer.Sparse.eval_collectBalanced, rawRowCheck4866]

theorem rawRowCheck4867 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form3 = rawRow4867 := by decide +kernel

theorem rowCheck4867 : row4867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4867 := by decide +kernel

theorem rowEval4867 (x : Key → ℝ) : Integer.Sparse.eval row4867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4867, Integer.Sparse.eval_collectBalanced, rawRowCheck4867]

theorem rawRowCheck4868 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form3 = rawRow4868 := by decide +kernel

theorem rowCheck4868 : row4868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4868 := by decide +kernel

theorem rowEval4868 (x : Key → ℝ) : Integer.Sparse.eval row4868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4868, Integer.Sparse.eval_collectBalanced, rawRowCheck4868]

theorem rawRowCheck4869 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form3 = rawRow4869 := by decide +kernel

theorem rowCheck4869 : row4869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4869 := by decide +kernel

theorem rowEval4869 (x : Key → ℝ) : Integer.Sparse.eval row4869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4869, Integer.Sparse.eval_collectBalanced, rawRowCheck4869]

theorem rawRowCheck4870 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form3 = rawRow4870 := by decide +kernel

theorem rowCheck4870 : row4870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4870 := by decide +kernel

theorem rowEval4870 (x : Key → ℝ) : Integer.Sparse.eval row4870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4870, Integer.Sparse.eval_collectBalanced, rawRowCheck4870]

theorem rawRowCheck4871 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form3 = rawRow4871 := by decide +kernel

theorem rowCheck4871 : row4871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4871 := by decide +kernel

theorem rowEval4871 (x : Key → ℝ) : Integer.Sparse.eval row4871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4871, Integer.Sparse.eval_collectBalanced, rawRowCheck4871]

theorem rawRowCheck4872 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form3 = rawRow4872 := by decide +kernel

theorem rowCheck4872 : row4872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4872 := by decide +kernel

theorem rowEval4872 (x : Key → ℝ) : Integer.Sparse.eval row4872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4872, Integer.Sparse.eval_collectBalanced, rawRowCheck4872]

theorem rawRowCheck4873 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form3 = rawRow4873 := by decide +kernel

theorem rowCheck4873 : row4873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4873 := by decide +kernel

theorem rowEval4873 (x : Key → ℝ) : Integer.Sparse.eval row4873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4873, Integer.Sparse.eval_collectBalanced, rawRowCheck4873]

theorem rawRowCheck4874 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form3 = rawRow4874 := by decide +kernel

theorem rowCheck4874 : row4874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4874 := by decide +kernel

theorem rowEval4874 (x : Key → ℝ) : Integer.Sparse.eval row4874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4874, Integer.Sparse.eval_collectBalanced, rawRowCheck4874]

theorem rawRowCheck4875 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form3 = rawRow4875 := by decide +kernel

theorem rowCheck4875 : row4875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4875 := by decide +kernel

theorem rowEval4875 (x : Key → ℝ) : Integer.Sparse.eval row4875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4875, Integer.Sparse.eval_collectBalanced, rawRowCheck4875]

theorem rawRowCheck4876 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form3 = rawRow4876 := by decide +kernel

theorem rowCheck4876 : row4876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4876 := by decide +kernel

theorem rowEval4876 (x : Key → ℝ) : Integer.Sparse.eval row4876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4876, Integer.Sparse.eval_collectBalanced, rawRowCheck4876]

theorem rawRowCheck4877 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form3 = rawRow4877 := by decide +kernel

theorem rowCheck4877 : row4877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4877 := by decide +kernel

theorem rowEval4877 (x : Key → ℝ) : Integer.Sparse.eval row4877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4877, Integer.Sparse.eval_collectBalanced, rawRowCheck4877]

theorem rawRowCheck4878 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form4 = rawRow4878 := by decide +kernel

theorem rowCheck4878 : row4878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4878 := by decide +kernel

theorem rowEval4878 (x : Key → ℝ) : Integer.Sparse.eval row4878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4878, Integer.Sparse.eval_collectBalanced, rawRowCheck4878]

theorem rawRowCheck4879 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form4 = rawRow4879 := by decide +kernel

theorem rowCheck4879 : row4879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4879 := by decide +kernel

theorem rowEval4879 (x : Key → ℝ) : Integer.Sparse.eval row4879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4879, Integer.Sparse.eval_collectBalanced, rawRowCheck4879]

theorem rawRowCheck4880 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form4 = rawRow4880 := by decide +kernel

theorem rowCheck4880 : row4880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4880 := by decide +kernel

theorem rowEval4880 (x : Key → ℝ) : Integer.Sparse.eval row4880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4880, Integer.Sparse.eval_collectBalanced, rawRowCheck4880]

theorem rawRowCheck4881 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form4 = rawRow4881 := by decide +kernel

theorem rowCheck4881 : row4881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4881 := by decide +kernel

theorem rowEval4881 (x : Key → ℝ) : Integer.Sparse.eval row4881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4881, Integer.Sparse.eval_collectBalanced, rawRowCheck4881]

theorem rawRowCheck4882 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form4 = rawRow4882 := by decide +kernel

theorem rowCheck4882 : row4882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4882 := by decide +kernel

theorem rowEval4882 (x : Key → ℝ) : Integer.Sparse.eval row4882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4882, Integer.Sparse.eval_collectBalanced, rawRowCheck4882]

theorem rawRowCheck4883 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form4 = rawRow4883 := by decide +kernel

theorem rowCheck4883 : row4883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4883 := by decide +kernel

theorem rowEval4883 (x : Key → ℝ) : Integer.Sparse.eval row4883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4883, Integer.Sparse.eval_collectBalanced, rawRowCheck4883]

theorem rawRowCheck4884 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form4 = rawRow4884 := by decide +kernel

theorem rowCheck4884 : row4884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4884 := by decide +kernel

theorem rowEval4884 (x : Key → ℝ) : Integer.Sparse.eval row4884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4884, Integer.Sparse.eval_collectBalanced, rawRowCheck4884]

theorem rawRowCheck4885 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form4 = rawRow4885 := by decide +kernel

theorem rowCheck4885 : row4885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4885 := by decide +kernel

theorem rowEval4885 (x : Key → ℝ) : Integer.Sparse.eval row4885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4885, Integer.Sparse.eval_collectBalanced, rawRowCheck4885]

theorem rawRowCheck4886 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form4 = rawRow4886 := by decide +kernel

theorem rowCheck4886 : row4886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4886 := by decide +kernel

theorem rowEval4886 (x : Key → ℝ) : Integer.Sparse.eval row4886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4886, Integer.Sparse.eval_collectBalanced, rawRowCheck4886]

theorem rawRowCheck4887 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form4 = rawRow4887 := by decide +kernel

theorem rowCheck4887 : row4887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4887 := by decide +kernel

theorem rowEval4887 (x : Key → ℝ) : Integer.Sparse.eval row4887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4887, Integer.Sparse.eval_collectBalanced, rawRowCheck4887]

theorem rawRowCheck4888 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form4 = rawRow4888 := by decide +kernel

theorem rowCheck4888 : row4888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4888 := by decide +kernel

theorem rowEval4888 (x : Key → ℝ) : Integer.Sparse.eval row4888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4888, Integer.Sparse.eval_collectBalanced, rawRowCheck4888]

theorem rawRowCheck4889 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form4 = rawRow4889 := by decide +kernel

theorem rowCheck4889 : row4889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4889 := by decide +kernel

theorem rowEval4889 (x : Key → ℝ) : Integer.Sparse.eval row4889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4889, Integer.Sparse.eval_collectBalanced, rawRowCheck4889]

theorem rawRowCheck4890 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form5 = rawRow4890 := by decide +kernel

theorem rowCheck4890 : row4890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4890 := by decide +kernel

theorem rowEval4890 (x : Key → ℝ) : Integer.Sparse.eval row4890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4890, Integer.Sparse.eval_collectBalanced, rawRowCheck4890]

theorem rawRowCheck4891 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form5 = rawRow4891 := by decide +kernel

theorem rowCheck4891 : row4891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4891 := by decide +kernel

theorem rowEval4891 (x : Key → ℝ) : Integer.Sparse.eval row4891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4891, Integer.Sparse.eval_collectBalanced, rawRowCheck4891]

theorem rawRowCheck4892 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form5 = rawRow4892 := by decide +kernel

theorem rowCheck4892 : row4892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4892 := by decide +kernel

theorem rowEval4892 (x : Key → ℝ) : Integer.Sparse.eval row4892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4892, Integer.Sparse.eval_collectBalanced, rawRowCheck4892]

theorem rawRowCheck4893 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form5 = rawRow4893 := by decide +kernel

theorem rowCheck4893 : row4893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4893 := by decide +kernel

theorem rowEval4893 (x : Key → ℝ) : Integer.Sparse.eval row4893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4893, Integer.Sparse.eval_collectBalanced, rawRowCheck4893]

theorem rawRowCheck4894 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form5 = rawRow4894 := by decide +kernel

theorem rowCheck4894 : row4894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4894 := by decide +kernel

theorem rowEval4894 (x : Key → ℝ) : Integer.Sparse.eval row4894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4894, Integer.Sparse.eval_collectBalanced, rawRowCheck4894]

theorem rawRowCheck4895 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form5 = rawRow4895 := by decide +kernel

theorem rowCheck4895 : row4895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4895 := by decide +kernel

theorem rowEval4895 (x : Key → ℝ) : Integer.Sparse.eval row4895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4895, Integer.Sparse.eval_collectBalanced, rawRowCheck4895]

theorem rawRowCheck4896 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form5 = rawRow4896 := by decide +kernel

theorem rowCheck4896 : row4896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4896 := by decide +kernel

theorem rowEval4896 (x : Key → ℝ) : Integer.Sparse.eval row4896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4896, Integer.Sparse.eval_collectBalanced, rawRowCheck4896]

theorem rawRowCheck4897 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form5 = rawRow4897 := by decide +kernel

theorem rowCheck4897 : row4897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4897 := by decide +kernel

theorem rowEval4897 (x : Key → ℝ) : Integer.Sparse.eval row4897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4897, Integer.Sparse.eval_collectBalanced, rawRowCheck4897]

theorem rawRowCheck4898 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form5 = rawRow4898 := by decide +kernel

theorem rowCheck4898 : row4898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4898 := by decide +kernel

theorem rowEval4898 (x : Key → ℝ) : Integer.Sparse.eval row4898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4898, Integer.Sparse.eval_collectBalanced, rawRowCheck4898]

theorem rawRowCheck4899 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form5 = rawRow4899 := by decide +kernel

theorem rowCheck4899 : row4899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4899 := by decide +kernel

theorem rowEval4899 (x : Key → ℝ) : Integer.Sparse.eval row4899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4899, Integer.Sparse.eval_collectBalanced, rawRowCheck4899]

theorem rawRowCheck4900 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form5 = rawRow4900 := by decide +kernel

theorem rowCheck4900 : row4900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4900 := by decide +kernel

theorem rowEval4900 (x : Key → ℝ) : Integer.Sparse.eval row4900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4900, Integer.Sparse.eval_collectBalanced, rawRowCheck4900]

theorem rawRowCheck4901 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form5 = rawRow4901 := by decide +kernel

theorem rowCheck4901 : row4901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4901 := by decide +kernel

theorem rowEval4901 (x : Key → ℝ) : Integer.Sparse.eval row4901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4901, Integer.Sparse.eval_collectBalanced, rawRowCheck4901]

theorem rawRowCheck4902 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form6 = rawRow4902 := by decide +kernel

theorem rowCheck4902 : row4902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4902 := by decide +kernel

theorem rowEval4902 (x : Key → ℝ) : Integer.Sparse.eval row4902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4902, Integer.Sparse.eval_collectBalanced, rawRowCheck4902]

theorem rawRowCheck4903 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form6 = rawRow4903 := by decide +kernel

theorem rowCheck4903 : row4903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4903 := by decide +kernel

theorem rowEval4903 (x : Key → ℝ) : Integer.Sparse.eval row4903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4903, Integer.Sparse.eval_collectBalanced, rawRowCheck4903]

theorem rawRowCheck4904 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form6 = rawRow4904 := by decide +kernel

theorem rowCheck4904 : row4904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4904 := by decide +kernel

theorem rowEval4904 (x : Key → ℝ) : Integer.Sparse.eval row4904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4904, Integer.Sparse.eval_collectBalanced, rawRowCheck4904]

theorem rawRowCheck4905 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form6 = rawRow4905 := by decide +kernel

theorem rowCheck4905 : row4905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4905 := by decide +kernel

theorem rowEval4905 (x : Key → ℝ) : Integer.Sparse.eval row4905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4905, Integer.Sparse.eval_collectBalanced, rawRowCheck4905]

theorem rawRowCheck4906 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form6 = rawRow4906 := by decide +kernel

theorem rowCheck4906 : row4906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4906 := by decide +kernel

theorem rowEval4906 (x : Key → ℝ) : Integer.Sparse.eval row4906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4906, Integer.Sparse.eval_collectBalanced, rawRowCheck4906]

theorem rawRowCheck4907 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form6 = rawRow4907 := by decide +kernel

theorem rowCheck4907 : row4907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4907 := by decide +kernel

theorem rowEval4907 (x : Key → ℝ) : Integer.Sparse.eval row4907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4907, Integer.Sparse.eval_collectBalanced, rawRowCheck4907]

theorem rawRowCheck4908 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form6 = rawRow4908 := by decide +kernel

theorem rowCheck4908 : row4908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4908 := by decide +kernel

theorem rowEval4908 (x : Key → ℝ) : Integer.Sparse.eval row4908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4908, Integer.Sparse.eval_collectBalanced, rawRowCheck4908]

theorem rawRowCheck4909 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form6 = rawRow4909 := by decide +kernel

theorem rowCheck4909 : row4909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4909 := by decide +kernel

theorem rowEval4909 (x : Key → ℝ) : Integer.Sparse.eval row4909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4909, Integer.Sparse.eval_collectBalanced, rawRowCheck4909]

theorem rawRowCheck4910 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form6 = rawRow4910 := by decide +kernel

theorem rowCheck4910 : row4910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4910 := by decide +kernel

theorem rowEval4910 (x : Key → ℝ) : Integer.Sparse.eval row4910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4910, Integer.Sparse.eval_collectBalanced, rawRowCheck4910]

theorem rawRowCheck4911 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form6 = rawRow4911 := by decide +kernel

theorem rowCheck4911 : row4911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4911 := by decide +kernel

theorem rowEval4911 (x : Key → ℝ) : Integer.Sparse.eval row4911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4911, Integer.Sparse.eval_collectBalanced, rawRowCheck4911]

theorem rawRowCheck4912 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form6 = rawRow4912 := by decide +kernel

theorem rowCheck4912 : row4912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4912 := by decide +kernel

theorem rowEval4912 (x : Key → ℝ) : Integer.Sparse.eval row4912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4912, Integer.Sparse.eval_collectBalanced, rawRowCheck4912]

theorem rawRowCheck4913 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form6 = rawRow4913 := by decide +kernel

theorem rowCheck4913 : row4913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4913 := by decide +kernel

theorem rowEval4913 (x : Key → ℝ) : Integer.Sparse.eval row4913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4913, Integer.Sparse.eval_collectBalanced, rawRowCheck4913]

theorem rawRowCheck4914 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form7 = rawRow4914 := by decide +kernel

theorem rowCheck4914 : row4914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4914 := by decide +kernel

theorem rowEval4914 (x : Key → ℝ) : Integer.Sparse.eval row4914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4914, Integer.Sparse.eval_collectBalanced, rawRowCheck4914]

theorem rawRowCheck4915 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form7 = rawRow4915 := by decide +kernel

theorem rowCheck4915 : row4915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4915 := by decide +kernel

theorem rowEval4915 (x : Key → ℝ) : Integer.Sparse.eval row4915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4915, Integer.Sparse.eval_collectBalanced, rawRowCheck4915]

theorem rawRowCheck4916 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form7 = rawRow4916 := by decide +kernel

theorem rowCheck4916 : row4916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4916 := by decide +kernel

theorem rowEval4916 (x : Key → ℝ) : Integer.Sparse.eval row4916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4916, Integer.Sparse.eval_collectBalanced, rawRowCheck4916]

theorem rawRowCheck4917 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form7 = rawRow4917 := by decide +kernel

theorem rowCheck4917 : row4917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4917 := by decide +kernel

theorem rowEval4917 (x : Key → ℝ) : Integer.Sparse.eval row4917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4917, Integer.Sparse.eval_collectBalanced, rawRowCheck4917]

theorem rawRowCheck4918 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form7 = rawRow4918 := by decide +kernel

theorem rowCheck4918 : row4918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4918 := by decide +kernel

theorem rowEval4918 (x : Key → ℝ) : Integer.Sparse.eval row4918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4918, Integer.Sparse.eval_collectBalanced, rawRowCheck4918]

theorem rawRowCheck4919 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form7 = rawRow4919 := by decide +kernel

theorem rowCheck4919 : row4919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4919 := by decide +kernel

theorem rowEval4919 (x : Key → ℝ) : Integer.Sparse.eval row4919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4919, Integer.Sparse.eval_collectBalanced, rawRowCheck4919]

theorem rawRowCheck4920 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form7 = rawRow4920 := by decide +kernel

theorem rowCheck4920 : row4920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4920 := by decide +kernel

theorem rowEval4920 (x : Key → ℝ) : Integer.Sparse.eval row4920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4920, Integer.Sparse.eval_collectBalanced, rawRowCheck4920]

theorem rawRowCheck4921 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form7 = rawRow4921 := by decide +kernel

theorem rowCheck4921 : row4921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4921 := by decide +kernel

theorem rowEval4921 (x : Key → ℝ) : Integer.Sparse.eval row4921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4921, Integer.Sparse.eval_collectBalanced, rawRowCheck4921]

theorem rawRowCheck4922 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form7 = rawRow4922 := by decide +kernel

theorem rowCheck4922 : row4922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4922 := by decide +kernel

theorem rowEval4922 (x : Key → ℝ) : Integer.Sparse.eval row4922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4922, Integer.Sparse.eval_collectBalanced, rawRowCheck4922]

theorem rawRowCheck4923 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form7 = rawRow4923 := by decide +kernel

theorem rowCheck4923 : row4923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4923 := by decide +kernel

theorem rowEval4923 (x : Key → ℝ) : Integer.Sparse.eval row4923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4923, Integer.Sparse.eval_collectBalanced, rawRowCheck4923]

theorem rawRowCheck4924 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form7 = rawRow4924 := by decide +kernel

theorem rowCheck4924 : row4924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4924 := by decide +kernel

theorem rowEval4924 (x : Key → ℝ) : Integer.Sparse.eval row4924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4924, Integer.Sparse.eval_collectBalanced, rawRowCheck4924]

theorem rawRowCheck4925 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form7 = rawRow4925 := by decide +kernel

theorem rowCheck4925 : row4925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4925 := by decide +kernel

theorem rowEval4925 (x : Key → ℝ) : Integer.Sparse.eval row4925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4925, Integer.Sparse.eval_collectBalanced, rawRowCheck4925]

theorem rawRowCheck4926 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form8 = rawRow4926 := by decide +kernel

theorem rowCheck4926 : row4926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4926 := by decide +kernel

theorem rowEval4926 (x : Key → ℝ) : Integer.Sparse.eval row4926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4926, Integer.Sparse.eval_collectBalanced, rawRowCheck4926]

theorem rawRowCheck4927 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form8 = rawRow4927 := by decide +kernel

theorem rowCheck4927 : row4927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4927 := by decide +kernel

theorem rowEval4927 (x : Key → ℝ) : Integer.Sparse.eval row4927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4927, Integer.Sparse.eval_collectBalanced, rawRowCheck4927]

theorem rawRowCheck4928 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form8 = rawRow4928 := by decide +kernel

theorem rowCheck4928 : row4928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4928 := by decide +kernel

theorem rowEval4928 (x : Key → ℝ) : Integer.Sparse.eval row4928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4928, Integer.Sparse.eval_collectBalanced, rawRowCheck4928]

theorem rawRowCheck4929 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form8 = rawRow4929 := by decide +kernel

theorem rowCheck4929 : row4929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4929 := by decide +kernel

theorem rowEval4929 (x : Key → ℝ) : Integer.Sparse.eval row4929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4929, Integer.Sparse.eval_collectBalanced, rawRowCheck4929]

theorem rawRowCheck4930 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form8 = rawRow4930 := by decide +kernel

theorem rowCheck4930 : row4930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4930 := by decide +kernel

theorem rowEval4930 (x : Key → ℝ) : Integer.Sparse.eval row4930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4930, Integer.Sparse.eval_collectBalanced, rawRowCheck4930]

theorem rawRowCheck4931 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form8 = rawRow4931 := by decide +kernel

theorem rowCheck4931 : row4931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4931 := by decide +kernel

theorem rowEval4931 (x : Key → ℝ) : Integer.Sparse.eval row4931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4931, Integer.Sparse.eval_collectBalanced, rawRowCheck4931]

theorem rawRowCheck4932 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form8 = rawRow4932 := by decide +kernel

theorem rowCheck4932 : row4932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4932 := by decide +kernel

theorem rowEval4932 (x : Key → ℝ) : Integer.Sparse.eval row4932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4932, Integer.Sparse.eval_collectBalanced, rawRowCheck4932]

theorem rawRowCheck4933 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form8 = rawRow4933 := by decide +kernel

theorem rowCheck4933 : row4933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4933 := by decide +kernel

theorem rowEval4933 (x : Key → ℝ) : Integer.Sparse.eval row4933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4933, Integer.Sparse.eval_collectBalanced, rawRowCheck4933]

theorem rawRowCheck4934 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form8 = rawRow4934 := by decide +kernel

theorem rowCheck4934 : row4934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4934 := by decide +kernel

theorem rowEval4934 (x : Key → ℝ) : Integer.Sparse.eval row4934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4934, Integer.Sparse.eval_collectBalanced, rawRowCheck4934]

theorem rawRowCheck4935 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form8 = rawRow4935 := by decide +kernel

theorem rowCheck4935 : row4935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4935 := by decide +kernel

theorem rowEval4935 (x : Key → ℝ) : Integer.Sparse.eval row4935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4935, Integer.Sparse.eval_collectBalanced, rawRowCheck4935]

theorem rawRowCheck4936 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form8 = rawRow4936 := by decide +kernel

theorem rowCheck4936 : row4936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4936 := by decide +kernel

theorem rowEval4936 (x : Key → ℝ) : Integer.Sparse.eval row4936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4936, Integer.Sparse.eval_collectBalanced, rawRowCheck4936]

theorem rawRowCheck4937 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form8 = rawRow4937 := by decide +kernel

theorem rowCheck4937 : row4937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4937 := by decide +kernel

theorem rowEval4937 (x : Key → ℝ) : Integer.Sparse.eval row4937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4937, Integer.Sparse.eval_collectBalanced, rawRowCheck4937]

theorem rawRowCheck4938 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form9 = rawRow4938 := by decide +kernel

theorem rowCheck4938 : row4938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4938 := by decide +kernel

theorem rowEval4938 (x : Key → ℝ) : Integer.Sparse.eval row4938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4938, Integer.Sparse.eval_collectBalanced, rawRowCheck4938]

theorem rawRowCheck4939 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form9 = rawRow4939 := by decide +kernel

theorem rowCheck4939 : row4939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4939 := by decide +kernel

theorem rowEval4939 (x : Key → ℝ) : Integer.Sparse.eval row4939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4939, Integer.Sparse.eval_collectBalanced, rawRowCheck4939]

theorem rawRowCheck4940 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form9 = rawRow4940 := by decide +kernel

theorem rowCheck4940 : row4940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4940 := by decide +kernel

theorem rowEval4940 (x : Key → ℝ) : Integer.Sparse.eval row4940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4940, Integer.Sparse.eval_collectBalanced, rawRowCheck4940]

theorem rawRowCheck4941 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form9 = rawRow4941 := by decide +kernel

theorem rowCheck4941 : row4941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4941 := by decide +kernel

theorem rowEval4941 (x : Key → ℝ) : Integer.Sparse.eval row4941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4941, Integer.Sparse.eval_collectBalanced, rawRowCheck4941]

theorem rawRowCheck4942 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form9 = rawRow4942 := by decide +kernel

theorem rowCheck4942 : row4942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4942 := by decide +kernel

theorem rowEval4942 (x : Key → ℝ) : Integer.Sparse.eval row4942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4942, Integer.Sparse.eval_collectBalanced, rawRowCheck4942]

theorem rawRowCheck4943 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form9 = rawRow4943 := by decide +kernel

theorem rowCheck4943 : row4943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4943 := by decide +kernel

theorem rowEval4943 (x : Key → ℝ) : Integer.Sparse.eval row4943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4943, Integer.Sparse.eval_collectBalanced, rawRowCheck4943]

theorem rawRowCheck4944 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form9 = rawRow4944 := by decide +kernel

theorem rowCheck4944 : row4944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4944 := by decide +kernel

theorem rowEval4944 (x : Key → ℝ) : Integer.Sparse.eval row4944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4944, Integer.Sparse.eval_collectBalanced, rawRowCheck4944]

theorem rawRowCheck4945 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form9 = rawRow4945 := by decide +kernel

theorem rowCheck4945 : row4945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4945 := by decide +kernel

theorem rowEval4945 (x : Key → ℝ) : Integer.Sparse.eval row4945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4945, Integer.Sparse.eval_collectBalanced, rawRowCheck4945]

theorem rawRowCheck4946 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form9 = rawRow4946 := by decide +kernel

theorem rowCheck4946 : row4946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4946 := by decide +kernel

theorem rowEval4946 (x : Key → ℝ) : Integer.Sparse.eval row4946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4946, Integer.Sparse.eval_collectBalanced, rawRowCheck4946]

theorem rawRowCheck4947 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form9 = rawRow4947 := by decide +kernel

theorem rowCheck4947 : row4947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4947 := by decide +kernel

theorem rowEval4947 (x : Key → ℝ) : Integer.Sparse.eval row4947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4947, Integer.Sparse.eval_collectBalanced, rawRowCheck4947]

theorem rawRowCheck4948 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form9 = rawRow4948 := by decide +kernel

theorem rowCheck4948 : row4948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4948 := by decide +kernel

theorem rowEval4948 (x : Key → ℝ) : Integer.Sparse.eval row4948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4948, Integer.Sparse.eval_collectBalanced, rawRowCheck4948]

theorem rawRowCheck4949 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form9 = rawRow4949 := by decide +kernel

theorem rowCheck4949 : row4949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4949 := by decide +kernel

theorem rowEval4949 (x : Key → ℝ) : Integer.Sparse.eval row4949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4949, Integer.Sparse.eval_collectBalanced, rawRowCheck4949]

theorem rawRowCheck4950 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form10 = rawRow4950 := by decide +kernel

theorem rowCheck4950 : row4950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4950 := by decide +kernel

theorem rowEval4950 (x : Key → ℝ) : Integer.Sparse.eval row4950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4950, Integer.Sparse.eval_collectBalanced, rawRowCheck4950]

theorem rawRowCheck4951 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form10 = rawRow4951 := by decide +kernel

theorem rowCheck4951 : row4951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4951 := by decide +kernel

theorem rowEval4951 (x : Key → ℝ) : Integer.Sparse.eval row4951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4951, Integer.Sparse.eval_collectBalanced, rawRowCheck4951]

theorem rawRowCheck4952 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form10 = rawRow4952 := by decide +kernel

theorem rowCheck4952 : row4952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4952 := by decide +kernel

theorem rowEval4952 (x : Key → ℝ) : Integer.Sparse.eval row4952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4952, Integer.Sparse.eval_collectBalanced, rawRowCheck4952]

theorem rawRowCheck4953 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form10 = rawRow4953 := by decide +kernel

theorem rowCheck4953 : row4953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4953 := by decide +kernel

theorem rowEval4953 (x : Key → ℝ) : Integer.Sparse.eval row4953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4953, Integer.Sparse.eval_collectBalanced, rawRowCheck4953]

theorem rawRowCheck4954 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form10 = rawRow4954 := by decide +kernel

theorem rowCheck4954 : row4954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4954 := by decide +kernel

theorem rowEval4954 (x : Key → ℝ) : Integer.Sparse.eval row4954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4954, Integer.Sparse.eval_collectBalanced, rawRowCheck4954]

theorem rawRowCheck4955 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form10 = rawRow4955 := by decide +kernel

theorem rowCheck4955 : row4955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4955 := by decide +kernel

theorem rowEval4955 (x : Key → ℝ) : Integer.Sparse.eval row4955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4955, Integer.Sparse.eval_collectBalanced, rawRowCheck4955]

theorem rawRowCheck4956 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form10 = rawRow4956 := by decide +kernel

theorem rowCheck4956 : row4956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4956 := by decide +kernel

theorem rowEval4956 (x : Key → ℝ) : Integer.Sparse.eval row4956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4956, Integer.Sparse.eval_collectBalanced, rawRowCheck4956]

theorem rawRowCheck4957 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form10 = rawRow4957 := by decide +kernel

theorem rowCheck4957 : row4957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4957 := by decide +kernel

theorem rowEval4957 (x : Key → ℝ) : Integer.Sparse.eval row4957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4957, Integer.Sparse.eval_collectBalanced, rawRowCheck4957]

theorem rawRowCheck4958 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form10 = rawRow4958 := by decide +kernel

theorem rowCheck4958 : row4958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4958 := by decide +kernel

theorem rowEval4958 (x : Key → ℝ) : Integer.Sparse.eval row4958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4958, Integer.Sparse.eval_collectBalanced, rawRowCheck4958]

theorem rawRowCheck4959 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form10 = rawRow4959 := by decide +kernel

theorem rowCheck4959 : row4959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4959 := by decide +kernel

theorem rowEval4959 (x : Key → ℝ) : Integer.Sparse.eval row4959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4959, Integer.Sparse.eval_collectBalanced, rawRowCheck4959]

theorem rawRowCheck4960 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form10 = rawRow4960 := by decide +kernel

theorem rowCheck4960 : row4960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4960 := by decide +kernel

theorem rowEval4960 (x : Key → ℝ) : Integer.Sparse.eval row4960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4960, Integer.Sparse.eval_collectBalanced, rawRowCheck4960]

theorem rawRowCheck4961 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form10 = rawRow4961 := by decide +kernel

theorem rowCheck4961 : row4961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4961 := by decide +kernel

theorem rowEval4961 (x : Key → ℝ) : Integer.Sparse.eval row4961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4961, Integer.Sparse.eval_collectBalanced, rawRowCheck4961]

theorem rawRowCheck4962 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form10 = rawRow4962 := by decide +kernel

theorem rowCheck4962 : row4962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4962 := by decide +kernel

theorem rowEval4962 (x : Key → ℝ) : Integer.Sparse.eval row4962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4962, Integer.Sparse.eval_collectBalanced, rawRowCheck4962]

theorem rawRowCheck4963 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form10 = rawRow4963 := by decide +kernel

theorem rowCheck4963 : row4963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4963 := by decide +kernel

theorem rowEval4963 (x : Key → ℝ) : Integer.Sparse.eval row4963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4963, Integer.Sparse.eval_collectBalanced, rawRowCheck4963]

theorem rawRowCheck4964 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form10 = rawRow4964 := by decide +kernel

theorem rowCheck4964 : row4964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4964 := by decide +kernel

theorem rowEval4964 (x : Key → ℝ) : Integer.Sparse.eval row4964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4964, Integer.Sparse.eval_collectBalanced, rawRowCheck4964]

theorem rawRowCheck4965 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form10 = rawRow4965 := by decide +kernel

theorem rowCheck4965 : row4965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4965 := by decide +kernel

theorem rowEval4965 (x : Key → ℝ) : Integer.Sparse.eval row4965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4965, Integer.Sparse.eval_collectBalanced, rawRowCheck4965]

theorem rawRowCheck4966 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form10 = rawRow4966 := by decide +kernel

theorem rowCheck4966 : row4966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4966 := by decide +kernel

theorem rowEval4966 (x : Key → ℝ) : Integer.Sparse.eval row4966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4966, Integer.Sparse.eval_collectBalanced, rawRowCheck4966]

theorem rawRowCheck4967 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form10 = rawRow4967 := by decide +kernel

theorem rowCheck4967 : row4967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4967 := by decide +kernel

theorem rowEval4967 (x : Key → ℝ) : Integer.Sparse.eval row4967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4967, Integer.Sparse.eval_collectBalanced, rawRowCheck4967]

theorem rawRowCheck4968 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form11 = rawRow4968 := by decide +kernel

theorem rowCheck4968 : row4968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4968 := by decide +kernel

theorem rowEval4968 (x : Key → ℝ) : Integer.Sparse.eval row4968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4968, Integer.Sparse.eval_collectBalanced, rawRowCheck4968]

theorem rawRowCheck4969 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form11 = rawRow4969 := by decide +kernel

theorem rowCheck4969 : row4969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4969 := by decide +kernel

theorem rowEval4969 (x : Key → ℝ) : Integer.Sparse.eval row4969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4969, Integer.Sparse.eval_collectBalanced, rawRowCheck4969]

theorem rawRowCheck4970 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form11 = rawRow4970 := by decide +kernel

theorem rowCheck4970 : row4970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4970 := by decide +kernel

theorem rowEval4970 (x : Key → ℝ) : Integer.Sparse.eval row4970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4970, Integer.Sparse.eval_collectBalanced, rawRowCheck4970]

theorem rawRowCheck4971 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form11 = rawRow4971 := by decide +kernel

theorem rowCheck4971 : row4971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4971 := by decide +kernel

theorem rowEval4971 (x : Key → ℝ) : Integer.Sparse.eval row4971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4971, Integer.Sparse.eval_collectBalanced, rawRowCheck4971]

theorem rawRowCheck4972 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form11 = rawRow4972 := by decide +kernel

theorem rowCheck4972 : row4972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4972 := by decide +kernel

theorem rowEval4972 (x : Key → ℝ) : Integer.Sparse.eval row4972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4972, Integer.Sparse.eval_collectBalanced, rawRowCheck4972]

theorem rawRowCheck4973 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form11 = rawRow4973 := by decide +kernel

theorem rowCheck4973 : row4973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4973 := by decide +kernel

theorem rowEval4973 (x : Key → ℝ) : Integer.Sparse.eval row4973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4973, Integer.Sparse.eval_collectBalanced, rawRowCheck4973]

theorem rawRowCheck4974 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form11 = rawRow4974 := by decide +kernel

theorem rowCheck4974 : row4974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4974 := by decide +kernel

theorem rowEval4974 (x : Key → ℝ) : Integer.Sparse.eval row4974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4974, Integer.Sparse.eval_collectBalanced, rawRowCheck4974]

theorem rawRowCheck4975 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form11 = rawRow4975 := by decide +kernel

theorem rowCheck4975 : row4975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4975 := by decide +kernel

theorem rowEval4975 (x : Key → ℝ) : Integer.Sparse.eval row4975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4975, Integer.Sparse.eval_collectBalanced, rawRowCheck4975]

theorem rawRowCheck4976 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form11 = rawRow4976 := by decide +kernel

theorem rowCheck4976 : row4976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4976 := by decide +kernel

theorem rowEval4976 (x : Key → ℝ) : Integer.Sparse.eval row4976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4976, Integer.Sparse.eval_collectBalanced, rawRowCheck4976]

theorem rawRowCheck4977 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form11 = rawRow4977 := by decide +kernel

theorem rowCheck4977 : row4977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4977 := by decide +kernel

theorem rowEval4977 (x : Key → ℝ) : Integer.Sparse.eval row4977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4977, Integer.Sparse.eval_collectBalanced, rawRowCheck4977]

theorem rawRowCheck4978 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form11 = rawRow4978 := by decide +kernel

theorem rowCheck4978 : row4978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4978 := by decide +kernel

theorem rowEval4978 (x : Key → ℝ) : Integer.Sparse.eval row4978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4978, Integer.Sparse.eval_collectBalanced, rawRowCheck4978]

theorem rawRowCheck4979 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form11 = rawRow4979 := by decide +kernel

theorem rowCheck4979 : row4979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4979 := by decide +kernel

theorem rowEval4979 (x : Key → ℝ) : Integer.Sparse.eval row4979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4979, Integer.Sparse.eval_collectBalanced, rawRowCheck4979]

theorem rawRowCheck4980 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form11 = rawRow4980 := by decide +kernel

theorem rowCheck4980 : row4980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4980 := by decide +kernel

theorem rowEval4980 (x : Key → ℝ) : Integer.Sparse.eval row4980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4980, Integer.Sparse.eval_collectBalanced, rawRowCheck4980]

theorem rawRowCheck4981 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form11 = rawRow4981 := by decide +kernel

theorem rowCheck4981 : row4981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4981 := by decide +kernel

theorem rowEval4981 (x : Key → ℝ) : Integer.Sparse.eval row4981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4981, Integer.Sparse.eval_collectBalanced, rawRowCheck4981]

theorem rawRowCheck4982 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form11 = rawRow4982 := by decide +kernel

theorem rowCheck4982 : row4982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4982 := by decide +kernel

theorem rowEval4982 (x : Key → ℝ) : Integer.Sparse.eval row4982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4982, Integer.Sparse.eval_collectBalanced, rawRowCheck4982]

theorem rawRowCheck4983 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form11 = rawRow4983 := by decide +kernel

theorem rowCheck4983 : row4983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4983 := by decide +kernel

theorem rowEval4983 (x : Key → ℝ) : Integer.Sparse.eval row4983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4983, Integer.Sparse.eval_collectBalanced, rawRowCheck4983]

theorem rawRowCheck4984 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form11 = rawRow4984 := by decide +kernel

theorem rowCheck4984 : row4984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4984 := by decide +kernel

theorem rowEval4984 (x : Key → ℝ) : Integer.Sparse.eval row4984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4984, Integer.Sparse.eval_collectBalanced, rawRowCheck4984]

theorem rawRowCheck4985 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form11 = rawRow4985 := by decide +kernel

theorem rowCheck4985 : row4985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4985 := by decide +kernel

theorem rowEval4985 (x : Key → ℝ) : Integer.Sparse.eval row4985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4985, Integer.Sparse.eval_collectBalanced, rawRowCheck4985]

theorem rawRowCheck4986 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form12 = rawRow4986 := by decide +kernel

theorem rowCheck4986 : row4986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4986 := by decide +kernel

theorem rowEval4986 (x : Key → ℝ) : Integer.Sparse.eval row4986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4986, Integer.Sparse.eval_collectBalanced, rawRowCheck4986]

theorem rawRowCheck4987 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form12 = rawRow4987 := by decide +kernel

theorem rowCheck4987 : row4987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4987 := by decide +kernel

theorem rowEval4987 (x : Key → ℝ) : Integer.Sparse.eval row4987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4987, Integer.Sparse.eval_collectBalanced, rawRowCheck4987]

theorem rawRowCheck4988 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form12 = rawRow4988 := by decide +kernel

theorem rowCheck4988 : row4988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4988 := by decide +kernel

theorem rowEval4988 (x : Key → ℝ) : Integer.Sparse.eval row4988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4988, Integer.Sparse.eval_collectBalanced, rawRowCheck4988]

theorem rawRowCheck4989 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form12 = rawRow4989 := by decide +kernel

theorem rowCheck4989 : row4989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4989 := by decide +kernel

theorem rowEval4989 (x : Key → ℝ) : Integer.Sparse.eval row4989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4989, Integer.Sparse.eval_collectBalanced, rawRowCheck4989]

theorem rawRowCheck4990 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form12 = rawRow4990 := by decide +kernel

theorem rowCheck4990 : row4990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4990 := by decide +kernel

theorem rowEval4990 (x : Key → ℝ) : Integer.Sparse.eval row4990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4990, Integer.Sparse.eval_collectBalanced, rawRowCheck4990]

theorem rawRowCheck4991 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form12 = rawRow4991 := by decide +kernel

theorem rowCheck4991 : row4991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4991 := by decide +kernel

theorem rowEval4991 (x : Key → ℝ) : Integer.Sparse.eval row4991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4991, Integer.Sparse.eval_collectBalanced, rawRowCheck4991]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck4992 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form12 = rawRow4992 := by decide +kernel

theorem rowCheck4992 : row4992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4992 := by decide +kernel

theorem rowEval4992 (x : Key → ℝ) : Integer.Sparse.eval row4992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4992, Integer.Sparse.eval_collectBalanced, rawRowCheck4992]

theorem rawRowCheck4993 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form12 = rawRow4993 := by decide +kernel

theorem rowCheck4993 : row4993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4993 := by decide +kernel

theorem rowEval4993 (x : Key → ℝ) : Integer.Sparse.eval row4993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4993, Integer.Sparse.eval_collectBalanced, rawRowCheck4993]

theorem rawRowCheck4994 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form12 = rawRow4994 := by decide +kernel

theorem rowCheck4994 : row4994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4994 := by decide +kernel

theorem rowEval4994 (x : Key → ℝ) : Integer.Sparse.eval row4994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4994, Integer.Sparse.eval_collectBalanced, rawRowCheck4994]

theorem rawRowCheck4995 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form12 = rawRow4995 := by decide +kernel

theorem rowCheck4995 : row4995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4995 := by decide +kernel

theorem rowEval4995 (x : Key → ℝ) : Integer.Sparse.eval row4995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4995, Integer.Sparse.eval_collectBalanced, rawRowCheck4995]

theorem rawRowCheck4996 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form12 = rawRow4996 := by decide +kernel

theorem rowCheck4996 : row4996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4996 := by decide +kernel

theorem rowEval4996 (x : Key → ℝ) : Integer.Sparse.eval row4996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4996, Integer.Sparse.eval_collectBalanced, rawRowCheck4996]

theorem rawRowCheck4997 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form12 = rawRow4997 := by decide +kernel

theorem rowCheck4997 : row4997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4997 := by decide +kernel

theorem rowEval4997 (x : Key → ℝ) : Integer.Sparse.eval row4997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4997, Integer.Sparse.eval_collectBalanced, rawRowCheck4997]

theorem rawRowCheck4998 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form12 = rawRow4998 := by decide +kernel

theorem rowCheck4998 : row4998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4998 := by decide +kernel

theorem rowEval4998 (x : Key → ℝ) : Integer.Sparse.eval row4998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4998, Integer.Sparse.eval_collectBalanced, rawRowCheck4998]

theorem rawRowCheck4999 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form12 = rawRow4999 := by decide +kernel

theorem rowCheck4999 : row4999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4999 := by decide +kernel

theorem rowEval4999 (x : Key → ℝ) : Integer.Sparse.eval row4999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4999, Integer.Sparse.eval_collectBalanced, rawRowCheck4999]

theorem rawRowCheck5000 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form12 = rawRow5000 := by decide +kernel

theorem rowCheck5000 : row5000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5000 := by decide +kernel

theorem rowEval5000 (x : Key → ℝ) : Integer.Sparse.eval row5000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5000, Integer.Sparse.eval_collectBalanced, rawRowCheck5000]

theorem rawRowCheck5001 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form12 = rawRow5001 := by decide +kernel

theorem rowCheck5001 : row5001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5001 := by decide +kernel

theorem rowEval5001 (x : Key → ℝ) : Integer.Sparse.eval row5001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5001, Integer.Sparse.eval_collectBalanced, rawRowCheck5001]

theorem rawRowCheck5002 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form12 = rawRow5002 := by decide +kernel

theorem rowCheck5002 : row5002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5002 := by decide +kernel

theorem rowEval5002 (x : Key → ℝ) : Integer.Sparse.eval row5002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5002, Integer.Sparse.eval_collectBalanced, rawRowCheck5002]

theorem rawRowCheck5003 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form12 = rawRow5003 := by decide +kernel

theorem rowCheck5003 : row5003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5003 := by decide +kernel

theorem rowEval5003 (x : Key → ℝ) : Integer.Sparse.eval row5003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck5003, Integer.Sparse.eval_collectBalanced, rawRowCheck5003]

theorem rawRowCheck5004 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form13 = rawRow5004 := by decide +kernel

theorem rowCheck5004 : row5004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5004 := by decide +kernel

theorem rowEval5004 (x : Key → ℝ) : Integer.Sparse.eval row5004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5004, Integer.Sparse.eval_collectBalanced, rawRowCheck5004]

theorem rawRowCheck5005 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form13 = rawRow5005 := by decide +kernel

theorem rowCheck5005 : row5005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5005 := by decide +kernel

theorem rowEval5005 (x : Key → ℝ) : Integer.Sparse.eval row5005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5005, Integer.Sparse.eval_collectBalanced, rawRowCheck5005]

theorem rawRowCheck5006 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form13 = rawRow5006 := by decide +kernel

theorem rowCheck5006 : row5006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5006 := by decide +kernel

theorem rowEval5006 (x : Key → ℝ) : Integer.Sparse.eval row5006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck5006, Integer.Sparse.eval_collectBalanced, rawRowCheck5006]

theorem rawRowCheck5007 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form13 = rawRow5007 := by decide +kernel

theorem rowCheck5007 : row5007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5007 := by decide +kernel

theorem rowEval5007 (x : Key → ℝ) : Integer.Sparse.eval row5007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5007, Integer.Sparse.eval_collectBalanced, rawRowCheck5007]

theorem rawRowCheck5008 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form13 = rawRow5008 := by decide +kernel

theorem rowCheck5008 : row5008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5008 := by decide +kernel

theorem rowEval5008 (x : Key → ℝ) : Integer.Sparse.eval row5008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5008, Integer.Sparse.eval_collectBalanced, rawRowCheck5008]

theorem rawRowCheck5009 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form13 = rawRow5009 := by decide +kernel

theorem rowCheck5009 : row5009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5009 := by decide +kernel

theorem rowEval5009 (x : Key → ℝ) : Integer.Sparse.eval row5009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5009, Integer.Sparse.eval_collectBalanced, rawRowCheck5009]

theorem rawRowCheck5010 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form13 = rawRow5010 := by decide +kernel

theorem rowCheck5010 : row5010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5010 := by decide +kernel

theorem rowEval5010 (x : Key → ℝ) : Integer.Sparse.eval row5010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5010, Integer.Sparse.eval_collectBalanced, rawRowCheck5010]

theorem rawRowCheck5011 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form13 = rawRow5011 := by decide +kernel

theorem rowCheck5011 : row5011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5011 := by decide +kernel

theorem rowEval5011 (x : Key → ℝ) : Integer.Sparse.eval row5011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5011, Integer.Sparse.eval_collectBalanced, rawRowCheck5011]

theorem rawRowCheck5012 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form13 = rawRow5012 := by decide +kernel

theorem rowCheck5012 : row5012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5012 := by decide +kernel

theorem rowEval5012 (x : Key → ℝ) : Integer.Sparse.eval row5012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck5012, Integer.Sparse.eval_collectBalanced, rawRowCheck5012]

theorem rawRowCheck5013 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form13 = rawRow5013 := by decide +kernel

theorem rowCheck5013 : row5013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5013 := by decide +kernel

theorem rowEval5013 (x : Key → ℝ) : Integer.Sparse.eval row5013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5013, Integer.Sparse.eval_collectBalanced, rawRowCheck5013]

theorem rawRowCheck5014 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form13 = rawRow5014 := by decide +kernel

theorem rowCheck5014 : row5014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5014 := by decide +kernel

theorem rowEval5014 (x : Key → ℝ) : Integer.Sparse.eval row5014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5014, Integer.Sparse.eval_collectBalanced, rawRowCheck5014]

theorem rawRowCheck5015 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form13 = rawRow5015 := by decide +kernel

theorem rowCheck5015 : row5015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5015 := by decide +kernel

theorem rowEval5015 (x : Key → ℝ) : Integer.Sparse.eval row5015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck5015, Integer.Sparse.eval_collectBalanced, rawRowCheck5015]

theorem rawRowCheck5016 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form13 = rawRow5016 := by decide +kernel

theorem rowCheck5016 : row5016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5016 := by decide +kernel

theorem rowEval5016 (x : Key → ℝ) : Integer.Sparse.eval row5016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5016, Integer.Sparse.eval_collectBalanced, rawRowCheck5016]

theorem rawRowCheck5017 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form13 = rawRow5017 := by decide +kernel

theorem rowCheck5017 : row5017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5017 := by decide +kernel

theorem rowEval5017 (x : Key → ℝ) : Integer.Sparse.eval row5017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5017, Integer.Sparse.eval_collectBalanced, rawRowCheck5017]

theorem rawRowCheck5018 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form13 = rawRow5018 := by decide +kernel

theorem rowCheck5018 : row5018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5018 := by decide +kernel

theorem rowEval5018 (x : Key → ℝ) : Integer.Sparse.eval row5018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5018, Integer.Sparse.eval_collectBalanced, rawRowCheck5018]

theorem rawRowCheck5019 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form13 = rawRow5019 := by decide +kernel

theorem rowCheck5019 : row5019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5019 := by decide +kernel

theorem rowEval5019 (x : Key → ℝ) : Integer.Sparse.eval row5019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5019, Integer.Sparse.eval_collectBalanced, rawRowCheck5019]

theorem rawRowCheck5020 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form13 = rawRow5020 := by decide +kernel

theorem rowCheck5020 : row5020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5020 := by decide +kernel

theorem rowEval5020 (x : Key → ℝ) : Integer.Sparse.eval row5020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5020, Integer.Sparse.eval_collectBalanced, rawRowCheck5020]

theorem rawRowCheck5021 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form13 = rawRow5021 := by decide +kernel

theorem rowCheck5021 : row5021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5021 := by decide +kernel

theorem rowEval5021 (x : Key → ℝ) : Integer.Sparse.eval row5021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck5021, Integer.Sparse.eval_collectBalanced, rawRowCheck5021]

theorem rawRowCheck5022 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form14 = rawRow5022 := by decide +kernel

theorem rowCheck5022 : row5022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5022 := by decide +kernel

theorem rowEval5022 (x : Key → ℝ) : Integer.Sparse.eval row5022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5022, Integer.Sparse.eval_collectBalanced, rawRowCheck5022]

theorem rawRowCheck5023 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form14 = rawRow5023 := by decide +kernel

theorem rowCheck5023 : row5023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5023 := by decide +kernel

theorem rowEval5023 (x : Key → ℝ) : Integer.Sparse.eval row5023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5023, Integer.Sparse.eval_collectBalanced, rawRowCheck5023]

theorem rawRowCheck5024 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form14 = rawRow5024 := by decide +kernel

theorem rowCheck5024 : row5024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5024 := by decide +kernel

theorem rowEval5024 (x : Key → ℝ) : Integer.Sparse.eval row5024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck5024, Integer.Sparse.eval_collectBalanced, rawRowCheck5024]

theorem rawRowCheck5025 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form14 = rawRow5025 := by decide +kernel

theorem rowCheck5025 : row5025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5025 := by decide +kernel

theorem rowEval5025 (x : Key → ℝ) : Integer.Sparse.eval row5025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5025, Integer.Sparse.eval_collectBalanced, rawRowCheck5025]

theorem rawRowCheck5026 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form14 = rawRow5026 := by decide +kernel

theorem rowCheck5026 : row5026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5026 := by decide +kernel

theorem rowEval5026 (x : Key → ℝ) : Integer.Sparse.eval row5026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5026, Integer.Sparse.eval_collectBalanced, rawRowCheck5026]

theorem rawRowCheck5027 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form14 = rawRow5027 := by decide +kernel

theorem rowCheck5027 : row5027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5027 := by decide +kernel

theorem rowEval5027 (x : Key → ℝ) : Integer.Sparse.eval row5027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5027, Integer.Sparse.eval_collectBalanced, rawRowCheck5027]

theorem rawRowCheck5028 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form14 = rawRow5028 := by decide +kernel

theorem rowCheck5028 : row5028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5028 := by decide +kernel

theorem rowEval5028 (x : Key → ℝ) : Integer.Sparse.eval row5028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5028, Integer.Sparse.eval_collectBalanced, rawRowCheck5028]

theorem rawRowCheck5029 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form14 = rawRow5029 := by decide +kernel

theorem rowCheck5029 : row5029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5029 := by decide +kernel

theorem rowEval5029 (x : Key → ℝ) : Integer.Sparse.eval row5029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5029, Integer.Sparse.eval_collectBalanced, rawRowCheck5029]

theorem rawRowCheck5030 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form14 = rawRow5030 := by decide +kernel

theorem rowCheck5030 : row5030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5030 := by decide +kernel

theorem rowEval5030 (x : Key → ℝ) : Integer.Sparse.eval row5030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck5030, Integer.Sparse.eval_collectBalanced, rawRowCheck5030]

theorem rawRowCheck5031 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form14 = rawRow5031 := by decide +kernel

theorem rowCheck5031 : row5031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5031 := by decide +kernel

theorem rowEval5031 (x : Key → ℝ) : Integer.Sparse.eval row5031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5031, Integer.Sparse.eval_collectBalanced, rawRowCheck5031]

theorem rawRowCheck5032 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form14 = rawRow5032 := by decide +kernel

theorem rowCheck5032 : row5032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5032 := by decide +kernel

theorem rowEval5032 (x : Key → ℝ) : Integer.Sparse.eval row5032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5032, Integer.Sparse.eval_collectBalanced, rawRowCheck5032]

theorem rawRowCheck5033 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form14 = rawRow5033 := by decide +kernel

theorem rowCheck5033 : row5033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5033 := by decide +kernel

theorem rowEval5033 (x : Key → ℝ) : Integer.Sparse.eval row5033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck5033, Integer.Sparse.eval_collectBalanced, rawRowCheck5033]

theorem rawRowCheck5034 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form14 = rawRow5034 := by decide +kernel

theorem rowCheck5034 : row5034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5034 := by decide +kernel

theorem rowEval5034 (x : Key → ℝ) : Integer.Sparse.eval row5034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5034, Integer.Sparse.eval_collectBalanced, rawRowCheck5034]

theorem rawRowCheck5035 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form14 = rawRow5035 := by decide +kernel

theorem rowCheck5035 : row5035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5035 := by decide +kernel

theorem rowEval5035 (x : Key → ℝ) : Integer.Sparse.eval row5035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5035, Integer.Sparse.eval_collectBalanced, rawRowCheck5035]

theorem rawRowCheck5036 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form14 = rawRow5036 := by decide +kernel

theorem rowCheck5036 : row5036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5036 := by decide +kernel

theorem rowEval5036 (x : Key → ℝ) : Integer.Sparse.eval row5036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5036, Integer.Sparse.eval_collectBalanced, rawRowCheck5036]

theorem rawRowCheck5037 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form14 = rawRow5037 := by decide +kernel

theorem rowCheck5037 : row5037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5037 := by decide +kernel

theorem rowEval5037 (x : Key → ℝ) : Integer.Sparse.eval row5037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5037, Integer.Sparse.eval_collectBalanced, rawRowCheck5037]

theorem rawRowCheck5038 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form14 = rawRow5038 := by decide +kernel

theorem rowCheck5038 : row5038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5038 := by decide +kernel

theorem rowEval5038 (x : Key → ℝ) : Integer.Sparse.eval row5038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5038, Integer.Sparse.eval_collectBalanced, rawRowCheck5038]

theorem rawRowCheck5039 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form14 = rawRow5039 := by decide +kernel

theorem rowCheck5039 : row5039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5039 := by decide +kernel

theorem rowEval5039 (x : Key → ℝ) : Integer.Sparse.eval row5039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck5039, Integer.Sparse.eval_collectBalanced, rawRowCheck5039]

theorem rawRowCheck5058 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form16 = rawRow5058 := by decide +kernel

theorem rowCheck5058 : row5058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5058 := by decide +kernel

theorem rowEval5058 (x : Key → ℝ) : Integer.Sparse.eval row5058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5058, Integer.Sparse.eval_collectBalanced, rawRowCheck5058]

theorem rawRowCheck5059 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form16 = rawRow5059 := by decide +kernel

theorem rowCheck5059 : row5059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5059 := by decide +kernel

theorem rowEval5059 (x : Key → ℝ) : Integer.Sparse.eval row5059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5059, Integer.Sparse.eval_collectBalanced, rawRowCheck5059]

theorem rawRowCheck5060 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form16 = rawRow5060 := by decide +kernel

theorem rowCheck5060 : row5060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5060 := by decide +kernel

theorem rowEval5060 (x : Key → ℝ) : Integer.Sparse.eval row5060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck5060, Integer.Sparse.eval_collectBalanced, rawRowCheck5060]

theorem rawRowCheck5061 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form16 = rawRow5061 := by decide +kernel

theorem rowCheck5061 : row5061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5061 := by decide +kernel

theorem rowEval5061 (x : Key → ℝ) : Integer.Sparse.eval row5061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5061, Integer.Sparse.eval_collectBalanced, rawRowCheck5061]

theorem rawRowCheck5062 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form16 = rawRow5062 := by decide +kernel

theorem rowCheck5062 : row5062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5062 := by decide +kernel

theorem rowEval5062 (x : Key → ℝ) : Integer.Sparse.eval row5062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5062, Integer.Sparse.eval_collectBalanced, rawRowCheck5062]

theorem rawRowCheck5063 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form16 = rawRow5063 := by decide +kernel

theorem rowCheck5063 : row5063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5063 := by decide +kernel

theorem rowEval5063 (x : Key → ℝ) : Integer.Sparse.eval row5063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5063, Integer.Sparse.eval_collectBalanced, rawRowCheck5063]

theorem rawRowCheck5064 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form16 = rawRow5064 := by decide +kernel

theorem rowCheck5064 : row5064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5064 := by decide +kernel

theorem rowEval5064 (x : Key → ℝ) : Integer.Sparse.eval row5064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5064, Integer.Sparse.eval_collectBalanced, rawRowCheck5064]

theorem rawRowCheck5065 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form16 = rawRow5065 := by decide +kernel

theorem rowCheck5065 : row5065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5065 := by decide +kernel

theorem rowEval5065 (x : Key → ℝ) : Integer.Sparse.eval row5065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5065, Integer.Sparse.eval_collectBalanced, rawRowCheck5065]

theorem rawRowCheck5066 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form16 = rawRow5066 := by decide +kernel

theorem rowCheck5066 : row5066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5066 := by decide +kernel

theorem rowEval5066 (x : Key → ℝ) : Integer.Sparse.eval row5066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck5066, Integer.Sparse.eval_collectBalanced, rawRowCheck5066]

theorem rawRowCheck5067 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form16 = rawRow5067 := by decide +kernel

theorem rowCheck5067 : row5067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5067 := by decide +kernel

theorem rowEval5067 (x : Key → ℝ) : Integer.Sparse.eval row5067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5067, Integer.Sparse.eval_collectBalanced, rawRowCheck5067]

theorem rawRowCheck5068 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form16 = rawRow5068 := by decide +kernel

theorem rowCheck5068 : row5068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5068 := by decide +kernel

theorem rowEval5068 (x : Key → ℝ) : Integer.Sparse.eval row5068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5068, Integer.Sparse.eval_collectBalanced, rawRowCheck5068]

theorem rawRowCheck5069 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form16 = rawRow5069 := by decide +kernel

theorem rowCheck5069 : row5069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5069 := by decide +kernel

theorem rowEval5069 (x : Key → ℝ) : Integer.Sparse.eval row5069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck5069, Integer.Sparse.eval_collectBalanced, rawRowCheck5069]

theorem rawRowCheck5070 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form16 = rawRow5070 := by decide +kernel

theorem rowCheck5070 : row5070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5070 := by decide +kernel

theorem rowEval5070 (x : Key → ℝ) : Integer.Sparse.eval row5070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5070, Integer.Sparse.eval_collectBalanced, rawRowCheck5070]

theorem rawRowCheck5071 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form16 = rawRow5071 := by decide +kernel

theorem rowCheck5071 : row5071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5071 := by decide +kernel

theorem rowEval5071 (x : Key → ℝ) : Integer.Sparse.eval row5071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5071, Integer.Sparse.eval_collectBalanced, rawRowCheck5071]

theorem rawRowCheck5072 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form16 = rawRow5072 := by decide +kernel

theorem rowCheck5072 : row5072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5072 := by decide +kernel

theorem rowEval5072 (x : Key → ℝ) : Integer.Sparse.eval row5072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5072, Integer.Sparse.eval_collectBalanced, rawRowCheck5072]

theorem rawRowCheck5073 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form16 = rawRow5073 := by decide +kernel

theorem rowCheck5073 : row5073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5073 := by decide +kernel

theorem rowEval5073 (x : Key → ℝ) : Integer.Sparse.eval row5073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5073, Integer.Sparse.eval_collectBalanced, rawRowCheck5073]

theorem rawRowCheck5074 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form16 = rawRow5074 := by decide +kernel

theorem rowCheck5074 : row5074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5074 := by decide +kernel

theorem rowEval5074 (x : Key → ℝ) : Integer.Sparse.eval row5074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5074, Integer.Sparse.eval_collectBalanced, rawRowCheck5074]

theorem rawRowCheck5075 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form16 = rawRow5075 := by decide +kernel

theorem rowCheck5075 : row5075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5075 := by decide +kernel

theorem rowEval5075 (x : Key → ℝ) : Integer.Sparse.eval row5075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck5075, Integer.Sparse.eval_collectBalanced, rawRowCheck5075]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck20_1 : entry20_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_1 k)) := by decide +kernel

theorem rowsSound20_1 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval4842 x
  · exact rowEval4843 x
  · exact rowEval4844 x
  · exact rowEval1494 x
  · exact rowEval1495 x
  · exact rowEval1496 x
  · exact rowEval4845 x
  · exact rowEval4846 x
  · exact rowEval4847 x
  · exact rowEval4848 x
  · exact rowEval4849 x
  · exact rowEval4850 x
  · exact rowEval1503 x
  · exact rowEval1504 x
  · exact rowEval1505 x
  · exact rowEval4851 x
  · exact rowEval4852 x
  · exact rowEval4853 x

theorem entryEval20_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_1 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck20_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_1]

theorem entryCheck20_3 : entry20_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_3 k)) := by decide +kernel

theorem rowsSound20_3 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval4866 x
  · exact rowEval4867 x
  · exact rowEval4868 x
  · exact rowEval1554 x
  · exact rowEval1555 x
  · exact rowEval1556 x
  · exact rowEval4869 x
  · exact rowEval4870 x
  · exact rowEval4871 x
  · exact rowEval4872 x
  · exact rowEval4873 x
  · exact rowEval4874 x
  · exact rowEval1563 x
  · exact rowEval1564 x
  · exact rowEval1565 x
  · exact rowEval4875 x
  · exact rowEval4876 x
  · exact rowEval4877 x

theorem entryEval20_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_3 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck20_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_3]

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval4878 x
  · exact rowEval4879 x
  · exact rowEval4880 x
  · exact rowEval1584 x
  · exact rowEval1585 x
  · exact rowEval1586 x
  · exact rowEval4881 x
  · exact rowEval4882 x
  · exact rowEval4883 x
  · exact rowEval4884 x
  · exact rowEval4885 x
  · exact rowEval4886 x
  · exact rowEval1593 x
  · exact rowEval1594 x
  · exact rowEval1595 x
  · exact rowEval4887 x
  · exact rowEval4888 x
  · exact rowEval4889 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

theorem entryCheck20_5 : entry20_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_5 k)) := by decide +kernel

theorem rowsSound20_5 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval4890 x
  · exact rowEval4891 x
  · exact rowEval4892 x
  · exact rowEval1614 x
  · exact rowEval1615 x
  · exact rowEval1616 x
  · exact rowEval4893 x
  · exact rowEval4894 x
  · exact rowEval4895 x
  · exact rowEval4896 x
  · exact rowEval4897 x
  · exact rowEval4898 x
  · exact rowEval1623 x
  · exact rowEval1624 x
  · exact rowEval1625 x
  · exact rowEval4899 x
  · exact rowEval4900 x
  · exact rowEval4901 x

theorem entryEval20_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_5 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck20_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_5]

theorem entryCheck20_6 : entry20_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_6 k)) := by decide +kernel

theorem rowsSound20_6 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval4902 x
  · exact rowEval4903 x
  · exact rowEval4904 x
  · exact rowEval1644 x
  · exact rowEval1645 x
  · exact rowEval1646 x
  · exact rowEval4905 x
  · exact rowEval4906 x
  · exact rowEval4907 x
  · exact rowEval4908 x
  · exact rowEval4909 x
  · exact rowEval4910 x
  · exact rowEval1653 x
  · exact rowEval1654 x
  · exact rowEval1655 x
  · exact rowEval4911 x
  · exact rowEval4912 x
  · exact rowEval4913 x

theorem entryEval20_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_6 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck20_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_6]

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval4914 x
  · exact rowEval4915 x
  · exact rowEval4916 x
  · exact rowEval1674 x
  · exact rowEval1675 x
  · exact rowEval1676 x
  · exact rowEval4917 x
  · exact rowEval4918 x
  · exact rowEval4919 x
  · exact rowEval4920 x
  · exact rowEval4921 x
  · exact rowEval4922 x
  · exact rowEval1683 x
  · exact rowEval1684 x
  · exact rowEval1685 x
  · exact rowEval4923 x
  · exact rowEval4924 x
  · exact rowEval4925 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

theorem entryCheck20_8 : entry20_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_8 k)) := by decide +kernel

theorem rowsSound20_8 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval4926 x
  · exact rowEval4927 x
  · exact rowEval4928 x
  · exact rowEval1704 x
  · exact rowEval1705 x
  · exact rowEval1706 x
  · exact rowEval4929 x
  · exact rowEval4930 x
  · exact rowEval4931 x
  · exact rowEval4932 x
  · exact rowEval4933 x
  · exact rowEval4934 x
  · exact rowEval1713 x
  · exact rowEval1714 x
  · exact rowEval1715 x
  · exact rowEval4935 x
  · exact rowEval4936 x
  · exact rowEval4937 x

theorem entryEval20_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_8 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck20_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_8]

theorem entryCheck20_9 : entry20_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_9 k)) := by decide +kernel

theorem rowsSound20_9 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval4938 x
  · exact rowEval4939 x
  · exact rowEval4940 x
  · exact rowEval1734 x
  · exact rowEval1735 x
  · exact rowEval1736 x
  · exact rowEval4941 x
  · exact rowEval4942 x
  · exact rowEval4943 x
  · exact rowEval4944 x
  · exact rowEval4945 x
  · exact rowEval4946 x
  · exact rowEval1743 x
  · exact rowEval1744 x
  · exact rowEval1745 x
  · exact rowEval4947 x
  · exact rowEval4948 x
  · exact rowEval4949 x

theorem entryEval20_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_9 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck20_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_9]

theorem entryCheck20_10 : entry20_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_10 k)) := by decide +kernel

theorem rowsSound20_10 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval4950 x
  · exact rowEval4951 x
  · exact rowEval4952 x
  · exact rowEval4953 x
  · exact rowEval4954 x
  · exact rowEval4955 x
  · exact rowEval4956 x
  · exact rowEval4957 x
  · exact rowEval4958 x
  · exact rowEval4959 x
  · exact rowEval4960 x
  · exact rowEval4961 x
  · exact rowEval4962 x
  · exact rowEval4963 x
  · exact rowEval4964 x
  · exact rowEval4965 x
  · exact rowEval4966 x
  · exact rowEval4967 x

theorem entryEval20_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_10 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck20_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_10]

theorem entryCheck20_11 : entry20_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_11 k)) := by decide +kernel

theorem rowsSound20_11 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval4968 x
  · exact rowEval4969 x
  · exact rowEval4970 x
  · exact rowEval4971 x
  · exact rowEval4972 x
  · exact rowEval4973 x
  · exact rowEval4974 x
  · exact rowEval4975 x
  · exact rowEval4976 x
  · exact rowEval4977 x
  · exact rowEval4978 x
  · exact rowEval4979 x
  · exact rowEval4980 x
  · exact rowEval4981 x
  · exact rowEval4982 x
  · exact rowEval4983 x
  · exact rowEval4984 x
  · exact rowEval4985 x

theorem entryEval20_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_11 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck20_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_11]

theorem entryCheck20_12 : entry20_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_12 k)) := by decide +kernel

theorem rowsSound20_12 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval4986 x
  · exact rowEval4987 x
  · exact rowEval4988 x
  · exact rowEval4989 x
  · exact rowEval4990 x
  · exact rowEval4991 x
  · exact rowEval4992 x
  · exact rowEval4993 x
  · exact rowEval4994 x
  · exact rowEval4995 x
  · exact rowEval4996 x
  · exact rowEval4997 x
  · exact rowEval4998 x
  · exact rowEval4999 x
  · exact rowEval5000 x
  · exact rowEval5001 x
  · exact rowEval5002 x
  · exact rowEval5003 x

theorem entryEval20_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_12 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck20_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_12]

theorem entryCheck20_13 : entry20_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_13 k)) := by decide +kernel

theorem rowsSound20_13 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval5004 x
  · exact rowEval5005 x
  · exact rowEval5006 x
  · exact rowEval5007 x
  · exact rowEval5008 x
  · exact rowEval5009 x
  · exact rowEval5010 x
  · exact rowEval5011 x
  · exact rowEval5012 x
  · exact rowEval5013 x
  · exact rowEval5014 x
  · exact rowEval5015 x
  · exact rowEval5016 x
  · exact rowEval5017 x
  · exact rowEval5018 x
  · exact rowEval5019 x
  · exact rowEval5020 x
  · exact rowEval5021 x

theorem entryEval20_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_13 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck20_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_13]

theorem entryCheck20_14 : entry20_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_14 k)) := by decide +kernel

theorem rowsSound20_14 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval5022 x
  · exact rowEval5023 x
  · exact rowEval5024 x
  · exact rowEval5025 x
  · exact rowEval5026 x
  · exact rowEval5027 x
  · exact rowEval5028 x
  · exact rowEval5029 x
  · exact rowEval5030 x
  · exact rowEval5031 x
  · exact rowEval5032 x
  · exact rowEval5033 x
  · exact rowEval5034 x
  · exact rowEval5035 x
  · exact rowEval5036 x
  · exact rowEval5037 x
  · exact rowEval5038 x
  · exact rowEval5039 x

theorem entryEval20_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_14 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck20_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_14]

theorem entryCheck20_16 : entry20_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_16 k)) := by decide +kernel

theorem rowsSound20_16 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval5058 x
  · exact rowEval5059 x
  · exact rowEval5060 x
  · exact rowEval5061 x
  · exact rowEval5062 x
  · exact rowEval5063 x
  · exact rowEval5064 x
  · exact rowEval5065 x
  · exact rowEval5066 x
  · exact rowEval5067 x
  · exact rowEval5068 x
  · exact rowEval5069 x
  · exact rowEval5070 x
  · exact rowEval5071 x
  · exact rowEval5072 x
  · exact rowEval5073 x
  · exact rowEval5074 x
  · exact rowEval5075 x

theorem entryEval20_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_16 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck20_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_16]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

theorem entryEvalRow20_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 20 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 20).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval20_0_e B hB
  · exact entryEval20_1 B hB
  · exact entryEval20_2_e B hB
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
  · exact entryEval20_15_e B hB
  · exact entryEval20_16 B hB
  · exact entryEval20_17_e B hB
  · exact entryEval20_18_e B hB
  · exact entryEval20_19_e B hB
  · exact entryEval20_20_e B hB

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e_oai
