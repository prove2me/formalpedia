-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:17:58.061656+00:00
-- url     : https://prove2.me/submissions/11ea744e-1e04-4a8f-9d68-1c37b5ce97e1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_26_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval26_9_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12563 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form1 = rawRow12563 := by decide +kernel

theorem rowCheck12563 : row12563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12563 := by decide +kernel

theorem rowEval12563 (x : Key → ℝ) : Integer.Sparse.eval row12563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12563, Integer.Sparse.eval_collectBalanced, rawRowCheck12563]

theorem rawRowCheck12564 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form1 = rawRow12564 := by decide +kernel

theorem rowCheck12564 : row12564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12564 := by decide +kernel

theorem rowEval12564 (x : Key → ℝ) : Integer.Sparse.eval row12564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12564, Integer.Sparse.eval_collectBalanced, rawRowCheck12564]

theorem rawRowCheck12565 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form1 = rawRow12565 := by decide +kernel

theorem rowCheck12565 : row12565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12565 := by decide +kernel

theorem rowEval12565 (x : Key → ℝ) : Integer.Sparse.eval row12565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12565, Integer.Sparse.eval_collectBalanced, rawRowCheck12565]

theorem rawRowCheck12566 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form1 = rawRow12566 := by decide +kernel

theorem rowCheck12566 : row12566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12566 := by decide +kernel

theorem rowEval12566 (x : Key → ℝ) : Integer.Sparse.eval row12566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12566, Integer.Sparse.eval_collectBalanced, rawRowCheck12566]

theorem rawRowCheck12567 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form1 = rawRow12567 := by decide +kernel

theorem rowCheck12567 : row12567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12567 := by decide +kernel

theorem rowEval12567 (x : Key → ℝ) : Integer.Sparse.eval row12567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12567, Integer.Sparse.eval_collectBalanced, rawRowCheck12567]

theorem rawRowCheck12568 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form1 = rawRow12568 := by decide +kernel

theorem rowCheck12568 : row12568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12568 := by decide +kernel

theorem rowEval12568 (x : Key → ℝ) : Integer.Sparse.eval row12568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12568, Integer.Sparse.eval_collectBalanced, rawRowCheck12568]

theorem rawRowCheck12569 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form1 = rawRow12569 := by decide +kernel

theorem rowCheck12569 : row12569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12569 := by decide +kernel

theorem rowEval12569 (x : Key → ℝ) : Integer.Sparse.eval row12569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12569, Integer.Sparse.eval_collectBalanced, rawRowCheck12569]

theorem rawRowCheck12570 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form1 = rawRow12570 := by decide +kernel

theorem rowCheck12570 : row12570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12570 := by decide +kernel

theorem rowEval12570 (x : Key → ℝ) : Integer.Sparse.eval row12570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12570, Integer.Sparse.eval_collectBalanced, rawRowCheck12570]

theorem rawRowCheck12571 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form1 = rawRow12571 := by decide +kernel

theorem rowCheck12571 : row12571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12571 := by decide +kernel

theorem rowEval12571 (x : Key → ℝ) : Integer.Sparse.eval row12571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12571, Integer.Sparse.eval_collectBalanced, rawRowCheck12571]

theorem rawRowCheck12572 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form1 = rawRow12572 := by decide +kernel

theorem rowCheck12572 : row12572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12572 := by decide +kernel

theorem rowEval12572 (x : Key → ℝ) : Integer.Sparse.eval row12572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12572, Integer.Sparse.eval_collectBalanced, rawRowCheck12572]

theorem rawRowCheck12573 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form1 = rawRow12573 := by decide +kernel

theorem rowCheck12573 : row12573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12573 := by decide +kernel

theorem rowEval12573 (x : Key → ℝ) : Integer.Sparse.eval row12573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12573, Integer.Sparse.eval_collectBalanced, rawRowCheck12573]

theorem rawRowCheck12574 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form1 = rawRow12574 := by decide +kernel

theorem rowCheck12574 : row12574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12574 := by decide +kernel

theorem rowEval12574 (x : Key → ℝ) : Integer.Sparse.eval row12574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12574, Integer.Sparse.eval_collectBalanced, rawRowCheck12574]

theorem rawRowCheck12575 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form1 = rawRow12575 := by decide +kernel

theorem rowCheck12575 : row12575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12575 := by decide +kernel

theorem rowEval12575 (x : Key → ℝ) : Integer.Sparse.eval row12575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12575, Integer.Sparse.eval_collectBalanced, rawRowCheck12575]

theorem rawRowCheck12576 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form1 = rawRow12576 := by decide +kernel

theorem rowCheck12576 : row12576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12576 := by decide +kernel

theorem rowEval12576 (x : Key → ℝ) : Integer.Sparse.eval row12576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12576, Integer.Sparse.eval_collectBalanced, rawRowCheck12576]

theorem rawRowCheck12577 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form1 = rawRow12577 := by decide +kernel

theorem rowCheck12577 : row12577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12577 := by decide +kernel

theorem rowEval12577 (x : Key → ℝ) : Integer.Sparse.eval row12577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12577, Integer.Sparse.eval_collectBalanced, rawRowCheck12577]

theorem rawRowCheck12578 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form1 = rawRow12578 := by decide +kernel

theorem rowCheck12578 : row12578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12578 := by decide +kernel

theorem rowEval12578 (x : Key → ℝ) : Integer.Sparse.eval row12578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12578, Integer.Sparse.eval_collectBalanced, rawRowCheck12578]

theorem rawRowCheck12579 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form1 = rawRow12579 := by decide +kernel

theorem rowCheck12579 : row12579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12579 := by decide +kernel

theorem rowEval12579 (x : Key → ℝ) : Integer.Sparse.eval row12579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12579, Integer.Sparse.eval_collectBalanced, rawRowCheck12579]

theorem rawRowCheck12580 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form1 = rawRow12580 := by decide +kernel

theorem rowCheck12580 : row12580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12580 := by decide +kernel

theorem rowEval12580 (x : Key → ℝ) : Integer.Sparse.eval row12580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12580, Integer.Sparse.eval_collectBalanced, rawRowCheck12580]

theorem rawRowCheck12581 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form1 = rawRow12581 := by decide +kernel

theorem rowCheck12581 : row12581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12581 := by decide +kernel

theorem rowEval12581 (x : Key → ℝ) : Integer.Sparse.eval row12581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12581, Integer.Sparse.eval_collectBalanced, rawRowCheck12581]

theorem rawRowCheck12582 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form1 = rawRow12582 := by decide +kernel

theorem rowCheck12582 : row12582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12582 := by decide +kernel

theorem rowEval12582 (x : Key → ℝ) : Integer.Sparse.eval row12582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12582, Integer.Sparse.eval_collectBalanced, rawRowCheck12582]

theorem rawRowCheck12583 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form1 = rawRow12583 := by decide +kernel

theorem rowCheck12583 : row12583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12583 := by decide +kernel

theorem rowEval12583 (x : Key → ℝ) : Integer.Sparse.eval row12583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12583, Integer.Sparse.eval_collectBalanced, rawRowCheck12583]

theorem rawRowCheck12584 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow12584 := by decide +kernel

theorem rowCheck12584 : row12584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12584 := by decide +kernel

theorem rowEval12584 (x : Key → ℝ) : Integer.Sparse.eval row12584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12584, Integer.Sparse.eval_collectBalanced, rawRowCheck12584]

theorem rawRowCheck12585 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow12585 := by decide +kernel

theorem rowCheck12585 : row12585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12585 := by decide +kernel

theorem rowEval12585 (x : Key → ℝ) : Integer.Sparse.eval row12585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12585, Integer.Sparse.eval_collectBalanced, rawRowCheck12585]

theorem rawRowCheck12586 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow12586 := by decide +kernel

theorem rowCheck12586 : row12586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12586 := by decide +kernel

theorem rowEval12586 (x : Key → ℝ) : Integer.Sparse.eval row12586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12586, Integer.Sparse.eval_collectBalanced, rawRowCheck12586]

theorem rawRowCheck12587 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form2 = rawRow12587 := by decide +kernel

theorem rowCheck12587 : row12587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12587 := by decide +kernel

theorem rowEval12587 (x : Key → ℝ) : Integer.Sparse.eval row12587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12587, Integer.Sparse.eval_collectBalanced, rawRowCheck12587]

theorem rawRowCheck12588 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form2 = rawRow12588 := by decide +kernel

theorem rowCheck12588 : row12588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12588 := by decide +kernel

theorem rowEval12588 (x : Key → ℝ) : Integer.Sparse.eval row12588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12588, Integer.Sparse.eval_collectBalanced, rawRowCheck12588]

theorem rawRowCheck12589 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form2 = rawRow12589 := by decide +kernel

theorem rowCheck12589 : row12589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12589 := by decide +kernel

theorem rowEval12589 (x : Key → ℝ) : Integer.Sparse.eval row12589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12589, Integer.Sparse.eval_collectBalanced, rawRowCheck12589]

theorem rawRowCheck12590 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form2 = rawRow12590 := by decide +kernel

theorem rowCheck12590 : row12590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12590 := by decide +kernel

theorem rowEval12590 (x : Key → ℝ) : Integer.Sparse.eval row12590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12590, Integer.Sparse.eval_collectBalanced, rawRowCheck12590]

theorem rawRowCheck12591 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form2 = rawRow12591 := by decide +kernel

theorem rowCheck12591 : row12591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12591 := by decide +kernel

theorem rowEval12591 (x : Key → ℝ) : Integer.Sparse.eval row12591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12591, Integer.Sparse.eval_collectBalanced, rawRowCheck12591]

theorem rawRowCheck12592 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form2 = rawRow12592 := by decide +kernel

theorem rowCheck12592 : row12592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12592 := by decide +kernel

theorem rowEval12592 (x : Key → ℝ) : Integer.Sparse.eval row12592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12592, Integer.Sparse.eval_collectBalanced, rawRowCheck12592]

theorem rawRowCheck12593 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form2 = rawRow12593 := by decide +kernel

theorem rowCheck12593 : row12593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12593 := by decide +kernel

theorem rowEval12593 (x : Key → ℝ) : Integer.Sparse.eval row12593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12593, Integer.Sparse.eval_collectBalanced, rawRowCheck12593]

theorem rawRowCheck12594 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form2 = rawRow12594 := by decide +kernel

theorem rowCheck12594 : row12594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12594 := by decide +kernel

theorem rowEval12594 (x : Key → ℝ) : Integer.Sparse.eval row12594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12594, Integer.Sparse.eval_collectBalanced, rawRowCheck12594]

theorem rawRowCheck12595 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form2 = rawRow12595 := by decide +kernel

theorem rowCheck12595 : row12595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12595 := by decide +kernel

theorem rowEval12595 (x : Key → ℝ) : Integer.Sparse.eval row12595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12595, Integer.Sparse.eval_collectBalanced, rawRowCheck12595]

theorem rawRowCheck12596 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form2 = rawRow12596 := by decide +kernel

theorem rowCheck12596 : row12596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12596 := by decide +kernel

theorem rowEval12596 (x : Key → ℝ) : Integer.Sparse.eval row12596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12596, Integer.Sparse.eval_collectBalanced, rawRowCheck12596]

theorem rawRowCheck12597 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form2 = rawRow12597 := by decide +kernel

theorem rowCheck12597 : row12597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12597 := by decide +kernel

theorem rowEval12597 (x : Key → ℝ) : Integer.Sparse.eval row12597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12597, Integer.Sparse.eval_collectBalanced, rawRowCheck12597]

theorem rawRowCheck12598 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form2 = rawRow12598 := by decide +kernel

theorem rowCheck12598 : row12598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12598 := by decide +kernel

theorem rowEval12598 (x : Key → ℝ) : Integer.Sparse.eval row12598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12598, Integer.Sparse.eval_collectBalanced, rawRowCheck12598]

theorem rawRowCheck12599 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form2 = rawRow12599 := by decide +kernel

theorem rowCheck12599 : row12599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12599 := by decide +kernel

theorem rowEval12599 (x : Key → ℝ) : Integer.Sparse.eval row12599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12599, Integer.Sparse.eval_collectBalanced, rawRowCheck12599]

theorem rawRowCheck12600 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form2 = rawRow12600 := by decide +kernel

theorem rowCheck12600 : row12600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12600 := by decide +kernel

theorem rowEval12600 (x : Key → ℝ) : Integer.Sparse.eval row12600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12600, Integer.Sparse.eval_collectBalanced, rawRowCheck12600]

theorem rawRowCheck12601 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form2 = rawRow12601 := by decide +kernel

theorem rowCheck12601 : row12601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12601 := by decide +kernel

theorem rowEval12601 (x : Key → ℝ) : Integer.Sparse.eval row12601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12601, Integer.Sparse.eval_collectBalanced, rawRowCheck12601]

theorem rawRowCheck12602 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form2 = rawRow12602 := by decide +kernel

theorem rowCheck12602 : row12602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12602 := by decide +kernel

theorem rowEval12602 (x : Key → ℝ) : Integer.Sparse.eval row12602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12602, Integer.Sparse.eval_collectBalanced, rawRowCheck12602]

theorem rawRowCheck12603 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form2 = rawRow12603 := by decide +kernel

theorem rowCheck12603 : row12603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12603 := by decide +kernel

theorem rowEval12603 (x : Key → ℝ) : Integer.Sparse.eval row12603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12603, Integer.Sparse.eval_collectBalanced, rawRowCheck12603]

theorem rawRowCheck12604 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form2 = rawRow12604 := by decide +kernel

theorem rowCheck12604 : row12604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12604 := by decide +kernel

theorem rowEval12604 (x : Key → ℝ) : Integer.Sparse.eval row12604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12604, Integer.Sparse.eval_collectBalanced, rawRowCheck12604]

theorem rawRowCheck12605 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form2 = rawRow12605 := by decide +kernel

theorem rowCheck12605 : row12605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12605 := by decide +kernel

theorem rowEval12605 (x : Key → ℝ) : Integer.Sparse.eval row12605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12605, Integer.Sparse.eval_collectBalanced, rawRowCheck12605]

theorem rawRowCheck12606 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form2 = rawRow12606 := by decide +kernel

theorem rowCheck12606 : row12606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12606 := by decide +kernel

theorem rowEval12606 (x : Key → ℝ) : Integer.Sparse.eval row12606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12606, Integer.Sparse.eval_collectBalanced, rawRowCheck12606]

theorem rawRowCheck12607 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form2 = rawRow12607 := by decide +kernel

theorem rowCheck12607 : row12607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12607 := by decide +kernel

theorem rowEval12607 (x : Key → ℝ) : Integer.Sparse.eval row12607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12607, Integer.Sparse.eval_collectBalanced, rawRowCheck12607]

theorem rawRowCheck12608 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow12608 := by decide +kernel

theorem rowCheck12608 : row12608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12608 := by decide +kernel

theorem rowEval12608 (x : Key → ℝ) : Integer.Sparse.eval row12608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12608, Integer.Sparse.eval_collectBalanced, rawRowCheck12608]

theorem rawRowCheck12609 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow12609 := by decide +kernel

theorem rowCheck12609 : row12609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12609 := by decide +kernel

theorem rowEval12609 (x : Key → ℝ) : Integer.Sparse.eval row12609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12609, Integer.Sparse.eval_collectBalanced, rawRowCheck12609]

theorem rawRowCheck12610 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow12610 := by decide +kernel

theorem rowCheck12610 : row12610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12610 := by decide +kernel

theorem rowEval12610 (x : Key → ℝ) : Integer.Sparse.eval row12610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12610, Integer.Sparse.eval_collectBalanced, rawRowCheck12610]

theorem rawRowCheck12611 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form3 = rawRow12611 := by decide +kernel

theorem rowCheck12611 : row12611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12611 := by decide +kernel

theorem rowEval12611 (x : Key → ℝ) : Integer.Sparse.eval row12611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12611, Integer.Sparse.eval_collectBalanced, rawRowCheck12611]

theorem rawRowCheck12612 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form3 = rawRow12612 := by decide +kernel

theorem rowCheck12612 : row12612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12612 := by decide +kernel

theorem rowEval12612 (x : Key → ℝ) : Integer.Sparse.eval row12612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12612, Integer.Sparse.eval_collectBalanced, rawRowCheck12612]

theorem rawRowCheck12613 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form3 = rawRow12613 := by decide +kernel

theorem rowCheck12613 : row12613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12613 := by decide +kernel

theorem rowEval12613 (x : Key → ℝ) : Integer.Sparse.eval row12613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12613, Integer.Sparse.eval_collectBalanced, rawRowCheck12613]

theorem rawRowCheck12614 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form3 = rawRow12614 := by decide +kernel

theorem rowCheck12614 : row12614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12614 := by decide +kernel

theorem rowEval12614 (x : Key → ℝ) : Integer.Sparse.eval row12614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12614, Integer.Sparse.eval_collectBalanced, rawRowCheck12614]

theorem rawRowCheck12615 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form3 = rawRow12615 := by decide +kernel

theorem rowCheck12615 : row12615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12615 := by decide +kernel

theorem rowEval12615 (x : Key → ℝ) : Integer.Sparse.eval row12615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12615, Integer.Sparse.eval_collectBalanced, rawRowCheck12615]

theorem rawRowCheck12616 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form3 = rawRow12616 := by decide +kernel

theorem rowCheck12616 : row12616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12616 := by decide +kernel

theorem rowEval12616 (x : Key → ℝ) : Integer.Sparse.eval row12616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12616, Integer.Sparse.eval_collectBalanced, rawRowCheck12616]

theorem rawRowCheck12617 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form3 = rawRow12617 := by decide +kernel

theorem rowCheck12617 : row12617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12617 := by decide +kernel

theorem rowEval12617 (x : Key → ℝ) : Integer.Sparse.eval row12617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12617, Integer.Sparse.eval_collectBalanced, rawRowCheck12617]

theorem rawRowCheck12618 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form3 = rawRow12618 := by decide +kernel

theorem rowCheck12618 : row12618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12618 := by decide +kernel

theorem rowEval12618 (x : Key → ℝ) : Integer.Sparse.eval row12618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12618, Integer.Sparse.eval_collectBalanced, rawRowCheck12618]

theorem rawRowCheck12619 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form3 = rawRow12619 := by decide +kernel

theorem rowCheck12619 : row12619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12619 := by decide +kernel

theorem rowEval12619 (x : Key → ℝ) : Integer.Sparse.eval row12619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12619, Integer.Sparse.eval_collectBalanced, rawRowCheck12619]

theorem rawRowCheck12620 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form3 = rawRow12620 := by decide +kernel

theorem rowCheck12620 : row12620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12620 := by decide +kernel

theorem rowEval12620 (x : Key → ℝ) : Integer.Sparse.eval row12620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12620, Integer.Sparse.eval_collectBalanced, rawRowCheck12620]

theorem rawRowCheck12621 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form3 = rawRow12621 := by decide +kernel

theorem rowCheck12621 : row12621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12621 := by decide +kernel

theorem rowEval12621 (x : Key → ℝ) : Integer.Sparse.eval row12621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12621, Integer.Sparse.eval_collectBalanced, rawRowCheck12621]

theorem rawRowCheck12622 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form3 = rawRow12622 := by decide +kernel

theorem rowCheck12622 : row12622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12622 := by decide +kernel

theorem rowEval12622 (x : Key → ℝ) : Integer.Sparse.eval row12622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12622, Integer.Sparse.eval_collectBalanced, rawRowCheck12622]

theorem rawRowCheck12623 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form3 = rawRow12623 := by decide +kernel

theorem rowCheck12623 : row12623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12623 := by decide +kernel

theorem rowEval12623 (x : Key → ℝ) : Integer.Sparse.eval row12623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12623, Integer.Sparse.eval_collectBalanced, rawRowCheck12623]

theorem rawRowCheck12624 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form3 = rawRow12624 := by decide +kernel

theorem rowCheck12624 : row12624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12624 := by decide +kernel

theorem rowEval12624 (x : Key → ℝ) : Integer.Sparse.eval row12624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12624, Integer.Sparse.eval_collectBalanced, rawRowCheck12624]

theorem rawRowCheck12625 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form3 = rawRow12625 := by decide +kernel

theorem rowCheck12625 : row12625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12625 := by decide +kernel

theorem rowEval12625 (x : Key → ℝ) : Integer.Sparse.eval row12625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12625, Integer.Sparse.eval_collectBalanced, rawRowCheck12625]

theorem rawRowCheck12626 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form3 = rawRow12626 := by decide +kernel

theorem rowCheck12626 : row12626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12626 := by decide +kernel

theorem rowEval12626 (x : Key → ℝ) : Integer.Sparse.eval row12626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12626, Integer.Sparse.eval_collectBalanced, rawRowCheck12626]

theorem rawRowCheck12627 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form3 = rawRow12627 := by decide +kernel

theorem rowCheck12627 : row12627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12627 := by decide +kernel

theorem rowEval12627 (x : Key → ℝ) : Integer.Sparse.eval row12627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12627, Integer.Sparse.eval_collectBalanced, rawRowCheck12627]

theorem rawRowCheck12628 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form3 = rawRow12628 := by decide +kernel

theorem rowCheck12628 : row12628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12628 := by decide +kernel

theorem rowEval12628 (x : Key → ℝ) : Integer.Sparse.eval row12628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12628, Integer.Sparse.eval_collectBalanced, rawRowCheck12628]

theorem rawRowCheck12629 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form3 = rawRow12629 := by decide +kernel

theorem rowCheck12629 : row12629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12629 := by decide +kernel

theorem rowEval12629 (x : Key → ℝ) : Integer.Sparse.eval row12629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12629, Integer.Sparse.eval_collectBalanced, rawRowCheck12629]

theorem rawRowCheck12630 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form3 = rawRow12630 := by decide +kernel

theorem rowCheck12630 : row12630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12630 := by decide +kernel

theorem rowEval12630 (x : Key → ℝ) : Integer.Sparse.eval row12630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12630, Integer.Sparse.eval_collectBalanced, rawRowCheck12630]

theorem rawRowCheck12631 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form3 = rawRow12631 := by decide +kernel

theorem rowCheck12631 : row12631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12631 := by decide +kernel

theorem rowEval12631 (x : Key → ℝ) : Integer.Sparse.eval row12631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12631, Integer.Sparse.eval_collectBalanced, rawRowCheck12631]

theorem rawRowCheck12632 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow12632 := by decide +kernel

theorem rowCheck12632 : row12632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12632 := by decide +kernel

theorem rowEval12632 (x : Key → ℝ) : Integer.Sparse.eval row12632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12632, Integer.Sparse.eval_collectBalanced, rawRowCheck12632]

theorem rawRowCheck12633 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow12633 := by decide +kernel

theorem rowCheck12633 : row12633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12633 := by decide +kernel

theorem rowEval12633 (x : Key → ℝ) : Integer.Sparse.eval row12633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12633, Integer.Sparse.eval_collectBalanced, rawRowCheck12633]

theorem rawRowCheck12634 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow12634 := by decide +kernel

theorem rowCheck12634 : row12634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12634 := by decide +kernel

theorem rowEval12634 (x : Key → ℝ) : Integer.Sparse.eval row12634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12634, Integer.Sparse.eval_collectBalanced, rawRowCheck12634]

theorem rawRowCheck12635 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form4 = rawRow12635 := by decide +kernel

theorem rowCheck12635 : row12635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12635 := by decide +kernel

theorem rowEval12635 (x : Key → ℝ) : Integer.Sparse.eval row12635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12635, Integer.Sparse.eval_collectBalanced, rawRowCheck12635]

theorem rawRowCheck12636 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form4 = rawRow12636 := by decide +kernel

theorem rowCheck12636 : row12636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12636 := by decide +kernel

theorem rowEval12636 (x : Key → ℝ) : Integer.Sparse.eval row12636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12636, Integer.Sparse.eval_collectBalanced, rawRowCheck12636]

theorem rawRowCheck12637 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form4 = rawRow12637 := by decide +kernel

theorem rowCheck12637 : row12637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12637 := by decide +kernel

theorem rowEval12637 (x : Key → ℝ) : Integer.Sparse.eval row12637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12637, Integer.Sparse.eval_collectBalanced, rawRowCheck12637]

theorem rawRowCheck12638 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form4 = rawRow12638 := by decide +kernel

theorem rowCheck12638 : row12638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12638 := by decide +kernel

theorem rowEval12638 (x : Key → ℝ) : Integer.Sparse.eval row12638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12638, Integer.Sparse.eval_collectBalanced, rawRowCheck12638]

theorem rawRowCheck12639 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form4 = rawRow12639 := by decide +kernel

theorem rowCheck12639 : row12639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12639 := by decide +kernel

theorem rowEval12639 (x : Key → ℝ) : Integer.Sparse.eval row12639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12639, Integer.Sparse.eval_collectBalanced, rawRowCheck12639]

theorem rawRowCheck12640 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form4 = rawRow12640 := by decide +kernel

theorem rowCheck12640 : row12640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12640 := by decide +kernel

theorem rowEval12640 (x : Key → ℝ) : Integer.Sparse.eval row12640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12640, Integer.Sparse.eval_collectBalanced, rawRowCheck12640]

theorem rawRowCheck12641 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form4 = rawRow12641 := by decide +kernel

theorem rowCheck12641 : row12641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12641 := by decide +kernel

theorem rowEval12641 (x : Key → ℝ) : Integer.Sparse.eval row12641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12641, Integer.Sparse.eval_collectBalanced, rawRowCheck12641]

theorem rawRowCheck12642 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form4 = rawRow12642 := by decide +kernel

theorem rowCheck12642 : row12642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12642 := by decide +kernel

theorem rowEval12642 (x : Key → ℝ) : Integer.Sparse.eval row12642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12642, Integer.Sparse.eval_collectBalanced, rawRowCheck12642]

theorem rawRowCheck12643 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form4 = rawRow12643 := by decide +kernel

theorem rowCheck12643 : row12643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12643 := by decide +kernel

theorem rowEval12643 (x : Key → ℝ) : Integer.Sparse.eval row12643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12643, Integer.Sparse.eval_collectBalanced, rawRowCheck12643]

theorem rawRowCheck12644 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form4 = rawRow12644 := by decide +kernel

theorem rowCheck12644 : row12644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12644 := by decide +kernel

theorem rowEval12644 (x : Key → ℝ) : Integer.Sparse.eval row12644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12644, Integer.Sparse.eval_collectBalanced, rawRowCheck12644]

theorem rawRowCheck12645 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form4 = rawRow12645 := by decide +kernel

theorem rowCheck12645 : row12645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12645 := by decide +kernel

theorem rowEval12645 (x : Key → ℝ) : Integer.Sparse.eval row12645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12645, Integer.Sparse.eval_collectBalanced, rawRowCheck12645]

theorem rawRowCheck12646 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form4 = rawRow12646 := by decide +kernel

theorem rowCheck12646 : row12646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12646 := by decide +kernel

theorem rowEval12646 (x : Key → ℝ) : Integer.Sparse.eval row12646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12646, Integer.Sparse.eval_collectBalanced, rawRowCheck12646]

theorem rawRowCheck12647 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form4 = rawRow12647 := by decide +kernel

theorem rowCheck12647 : row12647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12647 := by decide +kernel

theorem rowEval12647 (x : Key → ℝ) : Integer.Sparse.eval row12647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12647, Integer.Sparse.eval_collectBalanced, rawRowCheck12647]

theorem rawRowCheck12648 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form4 = rawRow12648 := by decide +kernel

theorem rowCheck12648 : row12648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12648 := by decide +kernel

theorem rowEval12648 (x : Key → ℝ) : Integer.Sparse.eval row12648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12648, Integer.Sparse.eval_collectBalanced, rawRowCheck12648]

theorem rawRowCheck12649 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form4 = rawRow12649 := by decide +kernel

theorem rowCheck12649 : row12649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12649 := by decide +kernel

theorem rowEval12649 (x : Key → ℝ) : Integer.Sparse.eval row12649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12649, Integer.Sparse.eval_collectBalanced, rawRowCheck12649]

theorem rawRowCheck12650 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form4 = rawRow12650 := by decide +kernel

theorem rowCheck12650 : row12650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12650 := by decide +kernel

theorem rowEval12650 (x : Key → ℝ) : Integer.Sparse.eval row12650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12650, Integer.Sparse.eval_collectBalanced, rawRowCheck12650]

theorem rawRowCheck12651 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form4 = rawRow12651 := by decide +kernel

theorem rowCheck12651 : row12651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12651 := by decide +kernel

theorem rowEval12651 (x : Key → ℝ) : Integer.Sparse.eval row12651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12651, Integer.Sparse.eval_collectBalanced, rawRowCheck12651]

theorem rawRowCheck12652 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form4 = rawRow12652 := by decide +kernel

theorem rowCheck12652 : row12652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12652 := by decide +kernel

theorem rowEval12652 (x : Key → ℝ) : Integer.Sparse.eval row12652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12652, Integer.Sparse.eval_collectBalanced, rawRowCheck12652]

theorem rawRowCheck12653 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form4 = rawRow12653 := by decide +kernel

theorem rowCheck12653 : row12653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12653 := by decide +kernel

theorem rowEval12653 (x : Key → ℝ) : Integer.Sparse.eval row12653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12653, Integer.Sparse.eval_collectBalanced, rawRowCheck12653]

theorem rawRowCheck12654 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form4 = rawRow12654 := by decide +kernel

theorem rowCheck12654 : row12654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12654 := by decide +kernel

theorem rowEval12654 (x : Key → ℝ) : Integer.Sparse.eval row12654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12654, Integer.Sparse.eval_collectBalanced, rawRowCheck12654]

theorem rawRowCheck12655 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form4 = rawRow12655 := by decide +kernel

theorem rowCheck12655 : row12655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12655 := by decide +kernel

theorem rowEval12655 (x : Key → ℝ) : Integer.Sparse.eval row12655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12655, Integer.Sparse.eval_collectBalanced, rawRowCheck12655]

theorem rawRowCheck12656 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow12656 := by decide +kernel

theorem rowCheck12656 : row12656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12656 := by decide +kernel

theorem rowEval12656 (x : Key → ℝ) : Integer.Sparse.eval row12656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12656, Integer.Sparse.eval_collectBalanced, rawRowCheck12656]

theorem rawRowCheck12657 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow12657 := by decide +kernel

theorem rowCheck12657 : row12657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12657 := by decide +kernel

theorem rowEval12657 (x : Key → ℝ) : Integer.Sparse.eval row12657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12657, Integer.Sparse.eval_collectBalanced, rawRowCheck12657]

theorem rawRowCheck12658 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow12658 := by decide +kernel

theorem rowCheck12658 : row12658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12658 := by decide +kernel

theorem rowEval12658 (x : Key → ℝ) : Integer.Sparse.eval row12658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12658, Integer.Sparse.eval_collectBalanced, rawRowCheck12658]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12683 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form6 = rawRow12683 := by decide +kernel

theorem rowCheck12683 : row12683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12683 := by decide +kernel

theorem rowEval12683 (x : Key → ℝ) : Integer.Sparse.eval row12683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12683, Integer.Sparse.eval_collectBalanced, rawRowCheck12683]

theorem rawRowCheck12684 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form6 = rawRow12684 := by decide +kernel

theorem rowCheck12684 : row12684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12684 := by decide +kernel

theorem rowEval12684 (x : Key → ℝ) : Integer.Sparse.eval row12684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12684, Integer.Sparse.eval_collectBalanced, rawRowCheck12684]

theorem rawRowCheck12685 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form6 = rawRow12685 := by decide +kernel

theorem rowCheck12685 : row12685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12685 := by decide +kernel

theorem rowEval12685 (x : Key → ℝ) : Integer.Sparse.eval row12685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12685, Integer.Sparse.eval_collectBalanced, rawRowCheck12685]

theorem rawRowCheck12686 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form6 = rawRow12686 := by decide +kernel

theorem rowCheck12686 : row12686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12686 := by decide +kernel

theorem rowEval12686 (x : Key → ℝ) : Integer.Sparse.eval row12686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12686, Integer.Sparse.eval_collectBalanced, rawRowCheck12686]

theorem rawRowCheck12687 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form6 = rawRow12687 := by decide +kernel

theorem rowCheck12687 : row12687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12687 := by decide +kernel

theorem rowEval12687 (x : Key → ℝ) : Integer.Sparse.eval row12687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12687, Integer.Sparse.eval_collectBalanced, rawRowCheck12687]

theorem rawRowCheck12688 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form6 = rawRow12688 := by decide +kernel

theorem rowCheck12688 : row12688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12688 := by decide +kernel

theorem rowEval12688 (x : Key → ℝ) : Integer.Sparse.eval row12688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12688, Integer.Sparse.eval_collectBalanced, rawRowCheck12688]

theorem rawRowCheck12689 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form6 = rawRow12689 := by decide +kernel

theorem rowCheck12689 : row12689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12689 := by decide +kernel

theorem rowEval12689 (x : Key → ℝ) : Integer.Sparse.eval row12689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12689, Integer.Sparse.eval_collectBalanced, rawRowCheck12689]

theorem rawRowCheck12690 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form6 = rawRow12690 := by decide +kernel

theorem rowCheck12690 : row12690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12690 := by decide +kernel

theorem rowEval12690 (x : Key → ℝ) : Integer.Sparse.eval row12690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12690, Integer.Sparse.eval_collectBalanced, rawRowCheck12690]

theorem rawRowCheck12691 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form6 = rawRow12691 := by decide +kernel

theorem rowCheck12691 : row12691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12691 := by decide +kernel

theorem rowEval12691 (x : Key → ℝ) : Integer.Sparse.eval row12691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12691, Integer.Sparse.eval_collectBalanced, rawRowCheck12691]

theorem rawRowCheck12692 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form6 = rawRow12692 := by decide +kernel

theorem rowCheck12692 : row12692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12692 := by decide +kernel

theorem rowEval12692 (x : Key → ℝ) : Integer.Sparse.eval row12692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12692, Integer.Sparse.eval_collectBalanced, rawRowCheck12692]

theorem rawRowCheck12693 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form6 = rawRow12693 := by decide +kernel

theorem rowCheck12693 : row12693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12693 := by decide +kernel

theorem rowEval12693 (x : Key → ℝ) : Integer.Sparse.eval row12693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12693, Integer.Sparse.eval_collectBalanced, rawRowCheck12693]

theorem rawRowCheck12694 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form6 = rawRow12694 := by decide +kernel

theorem rowCheck12694 : row12694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12694 := by decide +kernel

theorem rowEval12694 (x : Key → ℝ) : Integer.Sparse.eval row12694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12694, Integer.Sparse.eval_collectBalanced, rawRowCheck12694]

theorem rawRowCheck12695 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form6 = rawRow12695 := by decide +kernel

theorem rowCheck12695 : row12695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12695 := by decide +kernel

theorem rowEval12695 (x : Key → ℝ) : Integer.Sparse.eval row12695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12695, Integer.Sparse.eval_collectBalanced, rawRowCheck12695]

theorem rawRowCheck12696 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form6 = rawRow12696 := by decide +kernel

theorem rowCheck12696 : row12696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12696 := by decide +kernel

theorem rowEval12696 (x : Key → ℝ) : Integer.Sparse.eval row12696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12696, Integer.Sparse.eval_collectBalanced, rawRowCheck12696]

theorem rawRowCheck12697 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form6 = rawRow12697 := by decide +kernel

theorem rowCheck12697 : row12697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12697 := by decide +kernel

theorem rowEval12697 (x : Key → ℝ) : Integer.Sparse.eval row12697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12697, Integer.Sparse.eval_collectBalanced, rawRowCheck12697]

theorem rawRowCheck12698 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form6 = rawRow12698 := by decide +kernel

theorem rowCheck12698 : row12698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12698 := by decide +kernel

theorem rowEval12698 (x : Key → ℝ) : Integer.Sparse.eval row12698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12698, Integer.Sparse.eval_collectBalanced, rawRowCheck12698]

theorem rawRowCheck12699 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form6 = rawRow12699 := by decide +kernel

theorem rowCheck12699 : row12699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12699 := by decide +kernel

theorem rowEval12699 (x : Key → ℝ) : Integer.Sparse.eval row12699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12699, Integer.Sparse.eval_collectBalanced, rawRowCheck12699]

theorem rawRowCheck12700 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form6 = rawRow12700 := by decide +kernel

theorem rowCheck12700 : row12700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12700 := by decide +kernel

theorem rowEval12700 (x : Key → ℝ) : Integer.Sparse.eval row12700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12700, Integer.Sparse.eval_collectBalanced, rawRowCheck12700]

theorem rawRowCheck12701 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form6 = rawRow12701 := by decide +kernel

theorem rowCheck12701 : row12701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12701 := by decide +kernel

theorem rowEval12701 (x : Key → ℝ) : Integer.Sparse.eval row12701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12701, Integer.Sparse.eval_collectBalanced, rawRowCheck12701]

theorem rawRowCheck12702 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form6 = rawRow12702 := by decide +kernel

theorem rowCheck12702 : row12702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12702 := by decide +kernel

theorem rowEval12702 (x : Key → ℝ) : Integer.Sparse.eval row12702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12702, Integer.Sparse.eval_collectBalanced, rawRowCheck12702]

theorem rawRowCheck12703 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form6 = rawRow12703 := by decide +kernel

theorem rowCheck12703 : row12703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12703 := by decide +kernel

theorem rowEval12703 (x : Key → ℝ) : Integer.Sparse.eval row12703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12703, Integer.Sparse.eval_collectBalanced, rawRowCheck12703]

theorem rawRowCheck12704 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow12704 := by decide +kernel

theorem rowCheck12704 : row12704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12704 := by decide +kernel

theorem rowEval12704 (x : Key → ℝ) : Integer.Sparse.eval row12704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12704, Integer.Sparse.eval_collectBalanced, rawRowCheck12704]

theorem rawRowCheck12705 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow12705 := by decide +kernel

theorem rowCheck12705 : row12705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12705 := by decide +kernel

theorem rowEval12705 (x : Key → ℝ) : Integer.Sparse.eval row12705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12705, Integer.Sparse.eval_collectBalanced, rawRowCheck12705]

theorem rawRowCheck12706 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow12706 := by decide +kernel

theorem rowCheck12706 : row12706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12706 := by decide +kernel

theorem rowEval12706 (x : Key → ℝ) : Integer.Sparse.eval row12706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12706, Integer.Sparse.eval_collectBalanced, rawRowCheck12706]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck12803 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form11 = rawRow12803 := by decide +kernel

theorem rowCheck12803 : row12803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12803 := by decide +kernel

theorem rowEval12803 (x : Key → ℝ) : Integer.Sparse.eval row12803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12803, Integer.Sparse.eval_collectBalanced, rawRowCheck12803]

theorem rawRowCheck12804 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form11 = rawRow12804 := by decide +kernel

theorem rowCheck12804 : row12804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12804 := by decide +kernel

theorem rowEval12804 (x : Key → ℝ) : Integer.Sparse.eval row12804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12804, Integer.Sparse.eval_collectBalanced, rawRowCheck12804]

theorem rawRowCheck12805 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form11 = rawRow12805 := by decide +kernel

theorem rowCheck12805 : row12805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12805 := by decide +kernel

theorem rowEval12805 (x : Key → ℝ) : Integer.Sparse.eval row12805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12805, Integer.Sparse.eval_collectBalanced, rawRowCheck12805]

theorem rawRowCheck12806 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form11 = rawRow12806 := by decide +kernel

theorem rowCheck12806 : row12806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12806 := by decide +kernel

theorem rowEval12806 (x : Key → ℝ) : Integer.Sparse.eval row12806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12806, Integer.Sparse.eval_collectBalanced, rawRowCheck12806]

theorem rawRowCheck12807 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form11 = rawRow12807 := by decide +kernel

theorem rowCheck12807 : row12807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12807 := by decide +kernel

theorem rowEval12807 (x : Key → ℝ) : Integer.Sparse.eval row12807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12807, Integer.Sparse.eval_collectBalanced, rawRowCheck12807]

theorem rawRowCheck12808 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form11 = rawRow12808 := by decide +kernel

theorem rowCheck12808 : row12808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12808 := by decide +kernel

theorem rowEval12808 (x : Key → ℝ) : Integer.Sparse.eval row12808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12808, Integer.Sparse.eval_collectBalanced, rawRowCheck12808]

theorem rawRowCheck12809 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form11 = rawRow12809 := by decide +kernel

theorem rowCheck12809 : row12809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12809 := by decide +kernel

theorem rowEval12809 (x : Key → ℝ) : Integer.Sparse.eval row12809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12809, Integer.Sparse.eval_collectBalanced, rawRowCheck12809]

theorem rawRowCheck12810 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form11 = rawRow12810 := by decide +kernel

theorem rowCheck12810 : row12810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12810 := by decide +kernel

theorem rowEval12810 (x : Key → ℝ) : Integer.Sparse.eval row12810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12810, Integer.Sparse.eval_collectBalanced, rawRowCheck12810]

theorem rawRowCheck12811 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form11 = rawRow12811 := by decide +kernel

theorem rowCheck12811 : row12811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12811 := by decide +kernel

theorem rowEval12811 (x : Key → ℝ) : Integer.Sparse.eval row12811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12811, Integer.Sparse.eval_collectBalanced, rawRowCheck12811]

theorem rawRowCheck12812 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form11 = rawRow12812 := by decide +kernel

theorem rowCheck12812 : row12812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12812 := by decide +kernel

theorem rowEval12812 (x : Key → ℝ) : Integer.Sparse.eval row12812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12812, Integer.Sparse.eval_collectBalanced, rawRowCheck12812]

theorem rawRowCheck12813 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form11 = rawRow12813 := by decide +kernel

theorem rowCheck12813 : row12813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12813 := by decide +kernel

theorem rowEval12813 (x : Key → ℝ) : Integer.Sparse.eval row12813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12813, Integer.Sparse.eval_collectBalanced, rawRowCheck12813]

theorem rawRowCheck12814 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form11 = rawRow12814 := by decide +kernel

theorem rowCheck12814 : row12814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12814 := by decide +kernel

theorem rowEval12814 (x : Key → ℝ) : Integer.Sparse.eval row12814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12814, Integer.Sparse.eval_collectBalanced, rawRowCheck12814]

theorem rawRowCheck12815 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form11 = rawRow12815 := by decide +kernel

theorem rowCheck12815 : row12815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12815 := by decide +kernel

theorem rowEval12815 (x : Key → ℝ) : Integer.Sparse.eval row12815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12815, Integer.Sparse.eval_collectBalanced, rawRowCheck12815]

theorem rawRowCheck12816 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form11 = rawRow12816 := by decide +kernel

theorem rowCheck12816 : row12816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12816 := by decide +kernel

theorem rowEval12816 (x : Key → ℝ) : Integer.Sparse.eval row12816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12816, Integer.Sparse.eval_collectBalanced, rawRowCheck12816]

theorem rawRowCheck12817 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form11 = rawRow12817 := by decide +kernel

theorem rowCheck12817 : row12817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12817 := by decide +kernel

theorem rowEval12817 (x : Key → ℝ) : Integer.Sparse.eval row12817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12817, Integer.Sparse.eval_collectBalanced, rawRowCheck12817]

theorem rawRowCheck12818 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form11 = rawRow12818 := by decide +kernel

theorem rowCheck12818 : row12818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12818 := by decide +kernel

theorem rowEval12818 (x : Key → ℝ) : Integer.Sparse.eval row12818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12818, Integer.Sparse.eval_collectBalanced, rawRowCheck12818]

theorem rawRowCheck12819 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form11 = rawRow12819 := by decide +kernel

theorem rowCheck12819 : row12819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12819 := by decide +kernel

theorem rowEval12819 (x : Key → ℝ) : Integer.Sparse.eval row12819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12819, Integer.Sparse.eval_collectBalanced, rawRowCheck12819]

theorem rawRowCheck12820 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form11 = rawRow12820 := by decide +kernel

theorem rowCheck12820 : row12820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12820 := by decide +kernel

theorem rowEval12820 (x : Key → ℝ) : Integer.Sparse.eval row12820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12820, Integer.Sparse.eval_collectBalanced, rawRowCheck12820]

theorem rawRowCheck12821 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form11 = rawRow12821 := by decide +kernel

theorem rowCheck12821 : row12821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12821 := by decide +kernel

theorem rowEval12821 (x : Key → ℝ) : Integer.Sparse.eval row12821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12821, Integer.Sparse.eval_collectBalanced, rawRowCheck12821]

theorem rawRowCheck12822 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form11 = rawRow12822 := by decide +kernel

theorem rowCheck12822 : row12822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12822 := by decide +kernel

theorem rowEval12822 (x : Key → ℝ) : Integer.Sparse.eval row12822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12822, Integer.Sparse.eval_collectBalanced, rawRowCheck12822]

theorem rawRowCheck12823 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form11 = rawRow12823 := by decide +kernel

theorem rowCheck12823 : row12823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12823 := by decide +kernel

theorem rowEval12823 (x : Key → ℝ) : Integer.Sparse.eval row12823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12823, Integer.Sparse.eval_collectBalanced, rawRowCheck12823]

theorem rawRowCheck12824 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form11 = rawRow12824 := by decide +kernel

theorem rowCheck12824 : row12824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12824 := by decide +kernel

theorem rowEval12824 (x : Key → ℝ) : Integer.Sparse.eval row12824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12824, Integer.Sparse.eval_collectBalanced, rawRowCheck12824]

theorem rawRowCheck12825 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form11 = rawRow12825 := by decide +kernel

theorem rowCheck12825 : row12825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12825 := by decide +kernel

theorem rowEval12825 (x : Key → ℝ) : Integer.Sparse.eval row12825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12825, Integer.Sparse.eval_collectBalanced, rawRowCheck12825]

theorem rawRowCheck12826 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form11 = rawRow12826 := by decide +kernel

theorem rowCheck12826 : row12826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12826 := by decide +kernel

theorem rowEval12826 (x : Key → ℝ) : Integer.Sparse.eval row12826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12826, Integer.Sparse.eval_collectBalanced, rawRowCheck12826]

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

theorem rawRowCheck12851 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form13 = rawRow12851 := by decide +kernel

theorem rowCheck12851 : row12851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12851 := by decide +kernel

theorem rowEval12851 (x : Key → ℝ) : Integer.Sparse.eval row12851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12851, Integer.Sparse.eval_collectBalanced, rawRowCheck12851]

theorem rawRowCheck12852 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form13 = rawRow12852 := by decide +kernel

theorem rowCheck12852 : row12852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12852 := by decide +kernel

theorem rowEval12852 (x : Key → ℝ) : Integer.Sparse.eval row12852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12852, Integer.Sparse.eval_collectBalanced, rawRowCheck12852]

theorem rawRowCheck12853 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form13 = rawRow12853 := by decide +kernel

theorem rowCheck12853 : row12853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12853 := by decide +kernel

theorem rowEval12853 (x : Key → ℝ) : Integer.Sparse.eval row12853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12853, Integer.Sparse.eval_collectBalanced, rawRowCheck12853]

theorem rawRowCheck12854 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form13 = rawRow12854 := by decide +kernel

theorem rowCheck12854 : row12854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12854 := by decide +kernel

theorem rowEval12854 (x : Key → ℝ) : Integer.Sparse.eval row12854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12854, Integer.Sparse.eval_collectBalanced, rawRowCheck12854]

theorem rawRowCheck12855 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form13 = rawRow12855 := by decide +kernel

theorem rowCheck12855 : row12855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12855 := by decide +kernel

theorem rowEval12855 (x : Key → ℝ) : Integer.Sparse.eval row12855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12855, Integer.Sparse.eval_collectBalanced, rawRowCheck12855]

theorem rawRowCheck12856 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form13 = rawRow12856 := by decide +kernel

theorem rowCheck12856 : row12856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12856 := by decide +kernel

theorem rowEval12856 (x : Key → ℝ) : Integer.Sparse.eval row12856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12856, Integer.Sparse.eval_collectBalanced, rawRowCheck12856]

theorem rawRowCheck12857 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form13 = rawRow12857 := by decide +kernel

theorem rowCheck12857 : row12857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12857 := by decide +kernel

theorem rowEval12857 (x : Key → ℝ) : Integer.Sparse.eval row12857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12857, Integer.Sparse.eval_collectBalanced, rawRowCheck12857]

theorem rawRowCheck12858 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form13 = rawRow12858 := by decide +kernel

theorem rowCheck12858 : row12858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12858 := by decide +kernel

theorem rowEval12858 (x : Key → ℝ) : Integer.Sparse.eval row12858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12858, Integer.Sparse.eval_collectBalanced, rawRowCheck12858]

theorem rawRowCheck12859 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form13 = rawRow12859 := by decide +kernel

theorem rowCheck12859 : row12859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12859 := by decide +kernel

theorem rowEval12859 (x : Key → ℝ) : Integer.Sparse.eval row12859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12859, Integer.Sparse.eval_collectBalanced, rawRowCheck12859]

theorem rawRowCheck12860 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form13 = rawRow12860 := by decide +kernel

theorem rowCheck12860 : row12860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12860 := by decide +kernel

theorem rowEval12860 (x : Key → ℝ) : Integer.Sparse.eval row12860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12860, Integer.Sparse.eval_collectBalanced, rawRowCheck12860]

theorem rawRowCheck12861 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form13 = rawRow12861 := by decide +kernel

theorem rowCheck12861 : row12861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12861 := by decide +kernel

theorem rowEval12861 (x : Key → ℝ) : Integer.Sparse.eval row12861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12861, Integer.Sparse.eval_collectBalanced, rawRowCheck12861]

theorem rawRowCheck12862 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form13 = rawRow12862 := by decide +kernel

theorem rowCheck12862 : row12862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12862 := by decide +kernel

theorem rowEval12862 (x : Key → ℝ) : Integer.Sparse.eval row12862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12862, Integer.Sparse.eval_collectBalanced, rawRowCheck12862]

theorem rawRowCheck12863 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form13 = rawRow12863 := by decide +kernel

theorem rowCheck12863 : row12863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12863 := by decide +kernel

theorem rowEval12863 (x : Key → ℝ) : Integer.Sparse.eval row12863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12863, Integer.Sparse.eval_collectBalanced, rawRowCheck12863]

theorem rawRowCheck12864 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form13 = rawRow12864 := by decide +kernel

theorem rowCheck12864 : row12864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12864 := by decide +kernel

theorem rowEval12864 (x : Key → ℝ) : Integer.Sparse.eval row12864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12864, Integer.Sparse.eval_collectBalanced, rawRowCheck12864]

theorem rawRowCheck12865 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form13 = rawRow12865 := by decide +kernel

theorem rowCheck12865 : row12865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12865 := by decide +kernel

theorem rowEval12865 (x : Key → ℝ) : Integer.Sparse.eval row12865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12865, Integer.Sparse.eval_collectBalanced, rawRowCheck12865]

theorem rawRowCheck12866 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form13 = rawRow12866 := by decide +kernel

theorem rowCheck12866 : row12866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12866 := by decide +kernel

theorem rowEval12866 (x : Key → ℝ) : Integer.Sparse.eval row12866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12866, Integer.Sparse.eval_collectBalanced, rawRowCheck12866]

theorem rawRowCheck12867 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form13 = rawRow12867 := by decide +kernel

theorem rowCheck12867 : row12867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12867 := by decide +kernel

theorem rowEval12867 (x : Key → ℝ) : Integer.Sparse.eval row12867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12867, Integer.Sparse.eval_collectBalanced, rawRowCheck12867]

theorem rawRowCheck12868 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form13 = rawRow12868 := by decide +kernel

theorem rowCheck12868 : row12868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12868 := by decide +kernel

theorem rowEval12868 (x : Key → ℝ) : Integer.Sparse.eval row12868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12868, Integer.Sparse.eval_collectBalanced, rawRowCheck12868]

theorem rawRowCheck12869 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form13 = rawRow12869 := by decide +kernel

theorem rowCheck12869 : row12869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12869 := by decide +kernel

theorem rowEval12869 (x : Key → ℝ) : Integer.Sparse.eval row12869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12869, Integer.Sparse.eval_collectBalanced, rawRowCheck12869]

theorem rawRowCheck12870 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form13 = rawRow12870 := by decide +kernel

theorem rowCheck12870 : row12870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12870 := by decide +kernel

theorem rowEval12870 (x : Key → ℝ) : Integer.Sparse.eval row12870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12870, Integer.Sparse.eval_collectBalanced, rawRowCheck12870]

theorem rawRowCheck12871 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form13 = rawRow12871 := by decide +kernel

theorem rowCheck12871 : row12871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12871 := by decide +kernel

theorem rowEval12871 (x : Key → ℝ) : Integer.Sparse.eval row12871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12871, Integer.Sparse.eval_collectBalanced, rawRowCheck12871]

theorem rawRowCheck12872 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form13 = rawRow12872 := by decide +kernel

theorem rowCheck12872 : row12872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12872 := by decide +kernel

theorem rowEval12872 (x : Key → ℝ) : Integer.Sparse.eval row12872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12872, Integer.Sparse.eval_collectBalanced, rawRowCheck12872]

theorem rawRowCheck12873 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form13 = rawRow12873 := by decide +kernel

theorem rowCheck12873 : row12873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12873 := by decide +kernel

theorem rowEval12873 (x : Key → ℝ) : Integer.Sparse.eval row12873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12873, Integer.Sparse.eval_collectBalanced, rawRowCheck12873]

theorem rawRowCheck12874 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form13 = rawRow12874 := by decide +kernel

theorem rowCheck12874 : row12874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12874 := by decide +kernel

theorem rowEval12874 (x : Key → ℝ) : Integer.Sparse.eval row12874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12874, Integer.Sparse.eval_collectBalanced, rawRowCheck12874]

theorem rawRowCheck12875 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12875 := by decide +kernel

theorem rowCheck12875 : row12875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12875 := by decide +kernel

theorem rowEval12875 (x : Key → ℝ) : Integer.Sparse.eval row12875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12875, Integer.Sparse.eval_collectBalanced, rawRowCheck12875]

theorem rawRowCheck12876 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12876 := by decide +kernel

theorem rowCheck12876 : row12876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12876 := by decide +kernel

theorem rowEval12876 (x : Key → ℝ) : Integer.Sparse.eval row12876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12876, Integer.Sparse.eval_collectBalanced, rawRowCheck12876]

theorem rawRowCheck12877 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12877 := by decide +kernel

theorem rowCheck12877 : row12877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12877 := by decide +kernel

theorem rowEval12877 (x : Key → ℝ) : Integer.Sparse.eval row12877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12877, Integer.Sparse.eval_collectBalanced, rawRowCheck12877]

theorem rawRowCheck12878 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form14 = rawRow12878 := by decide +kernel

theorem rowCheck12878 : row12878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12878 := by decide +kernel

theorem rowEval12878 (x : Key → ℝ) : Integer.Sparse.eval row12878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12878, Integer.Sparse.eval_collectBalanced, rawRowCheck12878]

theorem rawRowCheck12879 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form14 = rawRow12879 := by decide +kernel

theorem rowCheck12879 : row12879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12879 := by decide +kernel

theorem rowEval12879 (x : Key → ℝ) : Integer.Sparse.eval row12879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12879, Integer.Sparse.eval_collectBalanced, rawRowCheck12879]

theorem rawRowCheck12880 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form14 = rawRow12880 := by decide +kernel

theorem rowCheck12880 : row12880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12880 := by decide +kernel

theorem rowEval12880 (x : Key → ℝ) : Integer.Sparse.eval row12880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12880, Integer.Sparse.eval_collectBalanced, rawRowCheck12880]

theorem rawRowCheck12881 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow12881 := by decide +kernel

theorem rowCheck12881 : row12881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12881 := by decide +kernel

theorem rowEval12881 (x : Key → ℝ) : Integer.Sparse.eval row12881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12881, Integer.Sparse.eval_collectBalanced, rawRowCheck12881]

theorem rawRowCheck12882 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow12882 := by decide +kernel

theorem rowCheck12882 : row12882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12882 := by decide +kernel

theorem rowEval12882 (x : Key → ℝ) : Integer.Sparse.eval row12882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12882, Integer.Sparse.eval_collectBalanced, rawRowCheck12882]

theorem rawRowCheck12883 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow12883 := by decide +kernel

theorem rowCheck12883 : row12883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12883 := by decide +kernel

theorem rowEval12883 (x : Key → ℝ) : Integer.Sparse.eval row12883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12883, Integer.Sparse.eval_collectBalanced, rawRowCheck12883]

theorem rawRowCheck12884 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow12884 := by decide +kernel

theorem rowCheck12884 : row12884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12884 := by decide +kernel

theorem rowEval12884 (x : Key → ℝ) : Integer.Sparse.eval row12884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12884, Integer.Sparse.eval_collectBalanced, rawRowCheck12884]

theorem rawRowCheck12885 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow12885 := by decide +kernel

theorem rowCheck12885 : row12885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12885 := by decide +kernel

theorem rowEval12885 (x : Key → ℝ) : Integer.Sparse.eval row12885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12885, Integer.Sparse.eval_collectBalanced, rawRowCheck12885]

theorem rawRowCheck12886 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow12886 := by decide +kernel

theorem rowCheck12886 : row12886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12886 := by decide +kernel

theorem rowEval12886 (x : Key → ℝ) : Integer.Sparse.eval row12886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12886, Integer.Sparse.eval_collectBalanced, rawRowCheck12886]

theorem rawRowCheck12887 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form14 = rawRow12887 := by decide +kernel

theorem rowCheck12887 : row12887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12887 := by decide +kernel

theorem rowEval12887 (x : Key → ℝ) : Integer.Sparse.eval row12887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12887, Integer.Sparse.eval_collectBalanced, rawRowCheck12887]

theorem rawRowCheck12888 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form14 = rawRow12888 := by decide +kernel

theorem rowCheck12888 : row12888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12888 := by decide +kernel

theorem rowEval12888 (x : Key → ℝ) : Integer.Sparse.eval row12888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12888, Integer.Sparse.eval_collectBalanced, rawRowCheck12888]

theorem rawRowCheck12889 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form14 = rawRow12889 := by decide +kernel

theorem rowCheck12889 : row12889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12889 := by decide +kernel

theorem rowEval12889 (x : Key → ℝ) : Integer.Sparse.eval row12889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12889, Integer.Sparse.eval_collectBalanced, rawRowCheck12889]

theorem rawRowCheck12890 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form14 = rawRow12890 := by decide +kernel

theorem rowCheck12890 : row12890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12890 := by decide +kernel

theorem rowEval12890 (x : Key → ℝ) : Integer.Sparse.eval row12890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12890, Integer.Sparse.eval_collectBalanced, rawRowCheck12890]

theorem rawRowCheck12891 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form14 = rawRow12891 := by decide +kernel

theorem rowCheck12891 : row12891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12891 := by decide +kernel

theorem rowEval12891 (x : Key → ℝ) : Integer.Sparse.eval row12891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12891, Integer.Sparse.eval_collectBalanced, rawRowCheck12891]

theorem rawRowCheck12892 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form14 = rawRow12892 := by decide +kernel

theorem rowCheck12892 : row12892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12892 := by decide +kernel

theorem rowEval12892 (x : Key → ℝ) : Integer.Sparse.eval row12892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12892, Integer.Sparse.eval_collectBalanced, rawRowCheck12892]

theorem rawRowCheck12893 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form14 = rawRow12893 := by decide +kernel

theorem rowCheck12893 : row12893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12893 := by decide +kernel

theorem rowEval12893 (x : Key → ℝ) : Integer.Sparse.eval row12893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12893, Integer.Sparse.eval_collectBalanced, rawRowCheck12893]

theorem rawRowCheck12894 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form14 = rawRow12894 := by decide +kernel

theorem rowCheck12894 : row12894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12894 := by decide +kernel

theorem rowEval12894 (x : Key → ℝ) : Integer.Sparse.eval row12894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12894, Integer.Sparse.eval_collectBalanced, rawRowCheck12894]

theorem rawRowCheck12895 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form14 = rawRow12895 := by decide +kernel

theorem rowCheck12895 : row12895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12895 := by decide +kernel

theorem rowEval12895 (x : Key → ℝ) : Integer.Sparse.eval row12895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12895, Integer.Sparse.eval_collectBalanced, rawRowCheck12895]

theorem rawRowCheck12896 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow12896 := by decide +kernel

theorem rowCheck12896 : row12896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12896 := by decide +kernel

theorem rowEval12896 (x : Key → ℝ) : Integer.Sparse.eval row12896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12896, Integer.Sparse.eval_collectBalanced, rawRowCheck12896]

theorem rawRowCheck12897 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow12897 := by decide +kernel

theorem rowCheck12897 : row12897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12897 := by decide +kernel

theorem rowEval12897 (x : Key → ℝ) : Integer.Sparse.eval row12897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12897, Integer.Sparse.eval_collectBalanced, rawRowCheck12897]

theorem rawRowCheck12898 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow12898 := by decide +kernel

theorem rowCheck12898 : row12898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12898 := by decide +kernel

theorem rowEval12898 (x : Key → ℝ) : Integer.Sparse.eval row12898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12898, Integer.Sparse.eval_collectBalanced, rawRowCheck12898]

theorem rawRowCheck12899 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form15 = rawRow12899 := by decide +kernel

theorem rowCheck12899 : row12899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12899 := by decide +kernel

theorem rowEval12899 (x : Key → ℝ) : Integer.Sparse.eval row12899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12899, Integer.Sparse.eval_collectBalanced, rawRowCheck12899]

theorem rawRowCheck12900 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form15 = rawRow12900 := by decide +kernel

theorem rowCheck12900 : row12900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12900 := by decide +kernel

theorem rowEval12900 (x : Key → ℝ) : Integer.Sparse.eval row12900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12900, Integer.Sparse.eval_collectBalanced, rawRowCheck12900]

theorem rawRowCheck12901 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form15 = rawRow12901 := by decide +kernel

theorem rowCheck12901 : row12901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12901 := by decide +kernel

theorem rowEval12901 (x : Key → ℝ) : Integer.Sparse.eval row12901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12901, Integer.Sparse.eval_collectBalanced, rawRowCheck12901]

theorem rawRowCheck12902 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form15 = rawRow12902 := by decide +kernel

theorem rowCheck12902 : row12902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12902 := by decide +kernel

theorem rowEval12902 (x : Key → ℝ) : Integer.Sparse.eval row12902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12902, Integer.Sparse.eval_collectBalanced, rawRowCheck12902]

theorem rawRowCheck12903 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form15 = rawRow12903 := by decide +kernel

theorem rowCheck12903 : row12903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12903 := by decide +kernel

theorem rowEval12903 (x : Key → ℝ) : Integer.Sparse.eval row12903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12903, Integer.Sparse.eval_collectBalanced, rawRowCheck12903]

theorem rawRowCheck12904 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form15 = rawRow12904 := by decide +kernel

theorem rowCheck12904 : row12904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12904 := by decide +kernel

theorem rowEval12904 (x : Key → ℝ) : Integer.Sparse.eval row12904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12904, Integer.Sparse.eval_collectBalanced, rawRowCheck12904]

theorem rawRowCheck12905 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form15 = rawRow12905 := by decide +kernel

theorem rowCheck12905 : row12905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12905 := by decide +kernel

theorem rowEval12905 (x : Key → ℝ) : Integer.Sparse.eval row12905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12905, Integer.Sparse.eval_collectBalanced, rawRowCheck12905]

theorem rawRowCheck12906 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form15 = rawRow12906 := by decide +kernel

theorem rowCheck12906 : row12906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12906 := by decide +kernel

theorem rowEval12906 (x : Key → ℝ) : Integer.Sparse.eval row12906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12906, Integer.Sparse.eval_collectBalanced, rawRowCheck12906]

theorem rawRowCheck12907 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form15 = rawRow12907 := by decide +kernel

theorem rowCheck12907 : row12907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12907 := by decide +kernel

theorem rowEval12907 (x : Key → ℝ) : Integer.Sparse.eval row12907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12907, Integer.Sparse.eval_collectBalanced, rawRowCheck12907]

theorem rawRowCheck12908 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form15 = rawRow12908 := by decide +kernel

theorem rowCheck12908 : row12908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12908 := by decide +kernel

theorem rowEval12908 (x : Key → ℝ) : Integer.Sparse.eval row12908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12908, Integer.Sparse.eval_collectBalanced, rawRowCheck12908]

theorem rawRowCheck12909 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form15 = rawRow12909 := by decide +kernel

theorem rowCheck12909 : row12909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12909 := by decide +kernel

theorem rowEval12909 (x : Key → ℝ) : Integer.Sparse.eval row12909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12909, Integer.Sparse.eval_collectBalanced, rawRowCheck12909]

theorem rawRowCheck12910 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form15 = rawRow12910 := by decide +kernel

theorem rowCheck12910 : row12910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12910 := by decide +kernel

theorem rowEval12910 (x : Key → ℝ) : Integer.Sparse.eval row12910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12910, Integer.Sparse.eval_collectBalanced, rawRowCheck12910]

theorem rawRowCheck12911 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form15 = rawRow12911 := by decide +kernel

theorem rowCheck12911 : row12911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12911 := by decide +kernel

theorem rowEval12911 (x : Key → ℝ) : Integer.Sparse.eval row12911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12911, Integer.Sparse.eval_collectBalanced, rawRowCheck12911]

theorem rawRowCheck12912 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form15 = rawRow12912 := by decide +kernel

theorem rowCheck12912 : row12912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12912 := by decide +kernel

theorem rowEval12912 (x : Key → ℝ) : Integer.Sparse.eval row12912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12912, Integer.Sparse.eval_collectBalanced, rawRowCheck12912]

theorem rawRowCheck12913 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form15 = rawRow12913 := by decide +kernel

theorem rowCheck12913 : row12913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12913 := by decide +kernel

theorem rowEval12913 (x : Key → ℝ) : Integer.Sparse.eval row12913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12913, Integer.Sparse.eval_collectBalanced, rawRowCheck12913]

theorem rawRowCheck12914 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form15 = rawRow12914 := by decide +kernel

theorem rowCheck12914 : row12914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12914 := by decide +kernel

theorem rowEval12914 (x : Key → ℝ) : Integer.Sparse.eval row12914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12914, Integer.Sparse.eval_collectBalanced, rawRowCheck12914]

theorem rawRowCheck12915 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form15 = rawRow12915 := by decide +kernel

theorem rowCheck12915 : row12915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12915 := by decide +kernel

theorem rowEval12915 (x : Key → ℝ) : Integer.Sparse.eval row12915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12915, Integer.Sparse.eval_collectBalanced, rawRowCheck12915]

theorem rawRowCheck12916 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form15 = rawRow12916 := by decide +kernel

theorem rowCheck12916 : row12916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12916 := by decide +kernel

theorem rowEval12916 (x : Key → ℝ) : Integer.Sparse.eval row12916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12916, Integer.Sparse.eval_collectBalanced, rawRowCheck12916]

theorem rawRowCheck12917 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form15 = rawRow12917 := by decide +kernel

theorem rowCheck12917 : row12917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12917 := by decide +kernel

theorem rowEval12917 (x : Key → ℝ) : Integer.Sparse.eval row12917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12917, Integer.Sparse.eval_collectBalanced, rawRowCheck12917]

theorem rawRowCheck12918 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form15 = rawRow12918 := by decide +kernel

theorem rowCheck12918 : row12918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12918 := by decide +kernel

theorem rowEval12918 (x : Key → ℝ) : Integer.Sparse.eval row12918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12918, Integer.Sparse.eval_collectBalanced, rawRowCheck12918]

theorem rawRowCheck12919 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form15 = rawRow12919 := by decide +kernel

theorem rowCheck12919 : row12919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12919 := by decide +kernel

theorem rowEval12919 (x : Key → ℝ) : Integer.Sparse.eval row12919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12919, Integer.Sparse.eval_collectBalanced, rawRowCheck12919]

theorem rawRowCheck12920 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form15 = rawRow12920 := by decide +kernel

theorem rowCheck12920 : row12920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12920 := by decide +kernel

theorem rowEval12920 (x : Key → ℝ) : Integer.Sparse.eval row12920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12920, Integer.Sparse.eval_collectBalanced, rawRowCheck12920]

theorem rawRowCheck12921 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form15 = rawRow12921 := by decide +kernel

theorem rowCheck12921 : row12921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12921 := by decide +kernel

theorem rowEval12921 (x : Key → ℝ) : Integer.Sparse.eval row12921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12921, Integer.Sparse.eval_collectBalanced, rawRowCheck12921]

theorem rawRowCheck12922 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form15 = rawRow12922 := by decide +kernel

theorem rowCheck12922 : row12922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12922 := by decide +kernel

theorem rowEval12922 (x : Key → ℝ) : Integer.Sparse.eval row12922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12922, Integer.Sparse.eval_collectBalanced, rawRowCheck12922]

theorem rawRowCheck12923 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12923 := by decide +kernel

theorem rowCheck12923 : row12923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12923 := by decide +kernel

theorem rowEval12923 (x : Key → ℝ) : Integer.Sparse.eval row12923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12923, Integer.Sparse.eval_collectBalanced, rawRowCheck12923]

theorem rawRowCheck12924 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12924 := by decide +kernel

theorem rowCheck12924 : row12924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12924 := by decide +kernel

theorem rowEval12924 (x : Key → ℝ) : Integer.Sparse.eval row12924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12924, Integer.Sparse.eval_collectBalanced, rawRowCheck12924]

theorem rawRowCheck12925 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12925 := by decide +kernel

theorem rowCheck12925 : row12925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12925 := by decide +kernel

theorem rowEval12925 (x : Key → ℝ) : Integer.Sparse.eval row12925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12925, Integer.Sparse.eval_collectBalanced, rawRowCheck12925]

theorem rawRowCheck12926 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form16 = rawRow12926 := by decide +kernel

theorem rowCheck12926 : row12926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12926 := by decide +kernel

theorem rowEval12926 (x : Key → ℝ) : Integer.Sparse.eval row12926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12926, Integer.Sparse.eval_collectBalanced, rawRowCheck12926]

theorem rawRowCheck12927 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form16 = rawRow12927 := by decide +kernel

theorem rowCheck12927 : row12927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12927 := by decide +kernel

theorem rowEval12927 (x : Key → ℝ) : Integer.Sparse.eval row12927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12927, Integer.Sparse.eval_collectBalanced, rawRowCheck12927]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck12928 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form16 = rawRow12928 := by decide +kernel

theorem rowCheck12928 : row12928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12928 := by decide +kernel

theorem rowEval12928 (x : Key → ℝ) : Integer.Sparse.eval row12928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12928, Integer.Sparse.eval_collectBalanced, rawRowCheck12928]

theorem rawRowCheck12929 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form16 = rawRow12929 := by decide +kernel

theorem rowCheck12929 : row12929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12929 := by decide +kernel

theorem rowEval12929 (x : Key → ℝ) : Integer.Sparse.eval row12929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12929, Integer.Sparse.eval_collectBalanced, rawRowCheck12929]

theorem rawRowCheck12930 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form16 = rawRow12930 := by decide +kernel

theorem rowCheck12930 : row12930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12930 := by decide +kernel

theorem rowEval12930 (x : Key → ℝ) : Integer.Sparse.eval row12930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12930, Integer.Sparse.eval_collectBalanced, rawRowCheck12930]

theorem rawRowCheck12931 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form16 = rawRow12931 := by decide +kernel

theorem rowCheck12931 : row12931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12931 := by decide +kernel

theorem rowEval12931 (x : Key → ℝ) : Integer.Sparse.eval row12931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12931, Integer.Sparse.eval_collectBalanced, rawRowCheck12931]

theorem rawRowCheck12932 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form16 = rawRow12932 := by decide +kernel

theorem rowCheck12932 : row12932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12932 := by decide +kernel

theorem rowEval12932 (x : Key → ℝ) : Integer.Sparse.eval row12932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12932, Integer.Sparse.eval_collectBalanced, rawRowCheck12932]

theorem rawRowCheck12933 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form16 = rawRow12933 := by decide +kernel

theorem rowCheck12933 : row12933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12933 := by decide +kernel

theorem rowEval12933 (x : Key → ℝ) : Integer.Sparse.eval row12933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12933, Integer.Sparse.eval_collectBalanced, rawRowCheck12933]

theorem rawRowCheck12934 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form16 = rawRow12934 := by decide +kernel

theorem rowCheck12934 : row12934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12934 := by decide +kernel

theorem rowEval12934 (x : Key → ℝ) : Integer.Sparse.eval row12934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12934, Integer.Sparse.eval_collectBalanced, rawRowCheck12934]

theorem rawRowCheck12935 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form16 = rawRow12935 := by decide +kernel

theorem rowCheck12935 : row12935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12935 := by decide +kernel

theorem rowEval12935 (x : Key → ℝ) : Integer.Sparse.eval row12935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12935, Integer.Sparse.eval_collectBalanced, rawRowCheck12935]

theorem rawRowCheck12936 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form16 = rawRow12936 := by decide +kernel

theorem rowCheck12936 : row12936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12936 := by decide +kernel

theorem rowEval12936 (x : Key → ℝ) : Integer.Sparse.eval row12936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12936, Integer.Sparse.eval_collectBalanced, rawRowCheck12936]

theorem rawRowCheck12937 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form16 = rawRow12937 := by decide +kernel

theorem rowCheck12937 : row12937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12937 := by decide +kernel

theorem rowEval12937 (x : Key → ℝ) : Integer.Sparse.eval row12937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12937, Integer.Sparse.eval_collectBalanced, rawRowCheck12937]

theorem rawRowCheck12938 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form16 = rawRow12938 := by decide +kernel

theorem rowCheck12938 : row12938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12938 := by decide +kernel

theorem rowEval12938 (x : Key → ℝ) : Integer.Sparse.eval row12938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12938, Integer.Sparse.eval_collectBalanced, rawRowCheck12938]

theorem rawRowCheck12939 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form16 = rawRow12939 := by decide +kernel

theorem rowCheck12939 : row12939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12939 := by decide +kernel

theorem rowEval12939 (x : Key → ℝ) : Integer.Sparse.eval row12939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12939, Integer.Sparse.eval_collectBalanced, rawRowCheck12939]

theorem rawRowCheck12940 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form16 = rawRow12940 := by decide +kernel

theorem rowCheck12940 : row12940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12940 := by decide +kernel

theorem rowEval12940 (x : Key → ℝ) : Integer.Sparse.eval row12940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12940, Integer.Sparse.eval_collectBalanced, rawRowCheck12940]

theorem rawRowCheck12941 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form16 = rawRow12941 := by decide +kernel

theorem rowCheck12941 : row12941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12941 := by decide +kernel

theorem rowEval12941 (x : Key → ℝ) : Integer.Sparse.eval row12941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12941, Integer.Sparse.eval_collectBalanced, rawRowCheck12941]

theorem rawRowCheck12942 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form16 = rawRow12942 := by decide +kernel

theorem rowCheck12942 : row12942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12942 := by decide +kernel

theorem rowEval12942 (x : Key → ℝ) : Integer.Sparse.eval row12942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12942, Integer.Sparse.eval_collectBalanced, rawRowCheck12942]

theorem rawRowCheck12943 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form16 = rawRow12943 := by decide +kernel

theorem rowCheck12943 : row12943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12943 := by decide +kernel

theorem rowEval12943 (x : Key → ℝ) : Integer.Sparse.eval row12943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12943, Integer.Sparse.eval_collectBalanced, rawRowCheck12943]

theorem rawRowCheck12944 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow12944 := by decide +kernel

theorem rowCheck12944 : row12944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12944 := by decide +kernel

theorem rowEval12944 (x : Key → ℝ) : Integer.Sparse.eval row12944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12944, Integer.Sparse.eval_collectBalanced, rawRowCheck12944]

theorem rawRowCheck12945 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow12945 := by decide +kernel

theorem rowCheck12945 : row12945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12945 := by decide +kernel

theorem rowEval12945 (x : Key → ℝ) : Integer.Sparse.eval row12945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12945, Integer.Sparse.eval_collectBalanced, rawRowCheck12945]

theorem rawRowCheck12946 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow12946 := by decide +kernel

theorem rowCheck12946 : row12946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12946 := by decide +kernel

theorem rowEval12946 (x : Key → ℝ) : Integer.Sparse.eval row12946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12946, Integer.Sparse.eval_collectBalanced, rawRowCheck12946]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13115 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form24 = rawRow13115 := by decide +kernel

theorem rowCheck13115 : row13115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13115 := by decide +kernel

theorem rowEval13115 (x : Key → ℝ) : Integer.Sparse.eval row13115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13115, Integer.Sparse.eval_collectBalanced, rawRowCheck13115]

theorem rawRowCheck13116 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form24 = rawRow13116 := by decide +kernel

theorem rowCheck13116 : row13116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13116 := by decide +kernel

theorem rowEval13116 (x : Key → ℝ) : Integer.Sparse.eval row13116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13116, Integer.Sparse.eval_collectBalanced, rawRowCheck13116]

theorem rawRowCheck13117 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form24 = rawRow13117 := by decide +kernel

theorem rowCheck13117 : row13117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13117 := by decide +kernel

theorem rowEval13117 (x : Key → ℝ) : Integer.Sparse.eval row13117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13117, Integer.Sparse.eval_collectBalanced, rawRowCheck13117]

theorem rawRowCheck13118 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form24 = rawRow13118 := by decide +kernel

theorem rowCheck13118 : row13118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13118 := by decide +kernel

theorem rowEval13118 (x : Key → ℝ) : Integer.Sparse.eval row13118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13118, Integer.Sparse.eval_collectBalanced, rawRowCheck13118]

theorem rawRowCheck13119 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form24 = rawRow13119 := by decide +kernel

theorem rowCheck13119 : row13119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13119 := by decide +kernel

theorem rowEval13119 (x : Key → ℝ) : Integer.Sparse.eval row13119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13119, Integer.Sparse.eval_collectBalanced, rawRowCheck13119]

theorem rawRowCheck13120 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form24 = rawRow13120 := by decide +kernel

theorem rowCheck13120 : row13120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13120 := by decide +kernel

theorem rowEval13120 (x : Key → ℝ) : Integer.Sparse.eval row13120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13120, Integer.Sparse.eval_collectBalanced, rawRowCheck13120]

theorem rawRowCheck13121 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form24 = rawRow13121 := by decide +kernel

theorem rowCheck13121 : row13121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13121 := by decide +kernel

theorem rowEval13121 (x : Key → ℝ) : Integer.Sparse.eval row13121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13121, Integer.Sparse.eval_collectBalanced, rawRowCheck13121]

theorem rawRowCheck13122 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form24 = rawRow13122 := by decide +kernel

theorem rowCheck13122 : row13122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13122 := by decide +kernel

theorem rowEval13122 (x : Key → ℝ) : Integer.Sparse.eval row13122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13122, Integer.Sparse.eval_collectBalanced, rawRowCheck13122]

theorem rawRowCheck13123 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form24 = rawRow13123 := by decide +kernel

theorem rowCheck13123 : row13123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13123 := by decide +kernel

theorem rowEval13123 (x : Key → ℝ) : Integer.Sparse.eval row13123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13123, Integer.Sparse.eval_collectBalanced, rawRowCheck13123]

theorem rawRowCheck13124 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form24 = rawRow13124 := by decide +kernel

theorem rowCheck13124 : row13124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13124 := by decide +kernel

theorem rowEval13124 (x : Key → ℝ) : Integer.Sparse.eval row13124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13124, Integer.Sparse.eval_collectBalanced, rawRowCheck13124]

theorem rawRowCheck13125 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form24 = rawRow13125 := by decide +kernel

theorem rowCheck13125 : row13125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13125 := by decide +kernel

theorem rowEval13125 (x : Key → ℝ) : Integer.Sparse.eval row13125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13125, Integer.Sparse.eval_collectBalanced, rawRowCheck13125]

theorem rawRowCheck13126 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form24 = rawRow13126 := by decide +kernel

theorem rowCheck13126 : row13126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13126 := by decide +kernel

theorem rowEval13126 (x : Key → ℝ) : Integer.Sparse.eval row13126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13126, Integer.Sparse.eval_collectBalanced, rawRowCheck13126]

theorem rawRowCheck13127 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form24 = rawRow13127 := by decide +kernel

theorem rowCheck13127 : row13127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13127 := by decide +kernel

theorem rowEval13127 (x : Key → ℝ) : Integer.Sparse.eval row13127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13127, Integer.Sparse.eval_collectBalanced, rawRowCheck13127]

theorem rawRowCheck13128 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form24 = rawRow13128 := by decide +kernel

theorem rowCheck13128 : row13128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13128 := by decide +kernel

theorem rowEval13128 (x : Key → ℝ) : Integer.Sparse.eval row13128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13128, Integer.Sparse.eval_collectBalanced, rawRowCheck13128]

theorem rawRowCheck13129 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form24 = rawRow13129 := by decide +kernel

theorem rowCheck13129 : row13129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13129 := by decide +kernel

theorem rowEval13129 (x : Key → ℝ) : Integer.Sparse.eval row13129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13129, Integer.Sparse.eval_collectBalanced, rawRowCheck13129]

theorem rawRowCheck13130 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form24 = rawRow13130 := by decide +kernel

theorem rowCheck13130 : row13130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13130 := by decide +kernel

theorem rowEval13130 (x : Key → ℝ) : Integer.Sparse.eval row13130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13130, Integer.Sparse.eval_collectBalanced, rawRowCheck13130]

theorem rawRowCheck13131 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form24 = rawRow13131 := by decide +kernel

theorem rowCheck13131 : row13131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13131 := by decide +kernel

theorem rowEval13131 (x : Key → ℝ) : Integer.Sparse.eval row13131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13131, Integer.Sparse.eval_collectBalanced, rawRowCheck13131]

theorem rawRowCheck13132 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form24 = rawRow13132 := by decide +kernel

theorem rowCheck13132 : row13132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13132 := by decide +kernel

theorem rowEval13132 (x : Key → ℝ) : Integer.Sparse.eval row13132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13132, Integer.Sparse.eval_collectBalanced, rawRowCheck13132]

theorem rawRowCheck13133 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form24 = rawRow13133 := by decide +kernel

theorem rowCheck13133 : row13133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13133 := by decide +kernel

theorem rowEval13133 (x : Key → ℝ) : Integer.Sparse.eval row13133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13133, Integer.Sparse.eval_collectBalanced, rawRowCheck13133]

theorem rawRowCheck13134 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form24 = rawRow13134 := by decide +kernel

theorem rowCheck13134 : row13134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13134 := by decide +kernel

theorem rowEval13134 (x : Key → ℝ) : Integer.Sparse.eval row13134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13134, Integer.Sparse.eval_collectBalanced, rawRowCheck13134]

theorem rawRowCheck13135 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form24 = rawRow13135 := by decide +kernel

theorem rowCheck13135 : row13135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13135 := by decide +kernel

theorem rowEval13135 (x : Key → ℝ) : Integer.Sparse.eval row13135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13135, Integer.Sparse.eval_collectBalanced, rawRowCheck13135]

theorem rawRowCheck13136 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form24 = rawRow13136 := by decide +kernel

theorem rowCheck13136 : row13136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13136 := by decide +kernel

theorem rowEval13136 (x : Key → ℝ) : Integer.Sparse.eval row13136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13136, Integer.Sparse.eval_collectBalanced, rawRowCheck13136]

theorem rawRowCheck13137 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form24 = rawRow13137 := by decide +kernel

theorem rowCheck13137 : row13137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13137 := by decide +kernel

theorem rowEval13137 (x : Key → ℝ) : Integer.Sparse.eval row13137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13137, Integer.Sparse.eval_collectBalanced, rawRowCheck13137]

theorem rawRowCheck13138 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form24 = rawRow13138 := by decide +kernel

theorem rowCheck13138 : row13138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13138 := by decide +kernel

theorem rowEval13138 (x : Key → ℝ) : Integer.Sparse.eval row13138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13138, Integer.Sparse.eval_collectBalanced, rawRowCheck13138]

theorem rawRowCheck13139 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form25 = rawRow13139 := by decide +kernel

theorem rowCheck13139 : row13139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13139 := by decide +kernel

theorem rowEval13139 (x : Key → ℝ) : Integer.Sparse.eval row13139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13139, Integer.Sparse.eval_collectBalanced, rawRowCheck13139]

theorem rawRowCheck13140 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form25 = rawRow13140 := by decide +kernel

theorem rowCheck13140 : row13140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13140 := by decide +kernel

theorem rowEval13140 (x : Key → ℝ) : Integer.Sparse.eval row13140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13140, Integer.Sparse.eval_collectBalanced, rawRowCheck13140]

theorem rawRowCheck13141 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form25 = rawRow13141 := by decide +kernel

theorem rowCheck13141 : row13141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13141 := by decide +kernel

theorem rowEval13141 (x : Key → ℝ) : Integer.Sparse.eval row13141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13141, Integer.Sparse.eval_collectBalanced, rawRowCheck13141]

theorem rawRowCheck13142 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form25 = rawRow13142 := by decide +kernel

theorem rowCheck13142 : row13142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13142 := by decide +kernel

theorem rowEval13142 (x : Key → ℝ) : Integer.Sparse.eval row13142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13142, Integer.Sparse.eval_collectBalanced, rawRowCheck13142]

theorem rawRowCheck13143 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form25 = rawRow13143 := by decide +kernel

theorem rowCheck13143 : row13143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13143 := by decide +kernel

theorem rowEval13143 (x : Key → ℝ) : Integer.Sparse.eval row13143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13143, Integer.Sparse.eval_collectBalanced, rawRowCheck13143]

theorem rawRowCheck13144 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form25 = rawRow13144 := by decide +kernel

theorem rowCheck13144 : row13144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13144 := by decide +kernel

theorem rowEval13144 (x : Key → ℝ) : Integer.Sparse.eval row13144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13144, Integer.Sparse.eval_collectBalanced, rawRowCheck13144]

theorem rawRowCheck13145 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form25 = rawRow13145 := by decide +kernel

theorem rowCheck13145 : row13145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13145 := by decide +kernel

theorem rowEval13145 (x : Key → ℝ) : Integer.Sparse.eval row13145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13145, Integer.Sparse.eval_collectBalanced, rawRowCheck13145]

theorem rawRowCheck13146 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form25 = rawRow13146 := by decide +kernel

theorem rowCheck13146 : row13146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13146 := by decide +kernel

theorem rowEval13146 (x : Key → ℝ) : Integer.Sparse.eval row13146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13146, Integer.Sparse.eval_collectBalanced, rawRowCheck13146]

theorem rawRowCheck13147 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form25 = rawRow13147 := by decide +kernel

theorem rowCheck13147 : row13147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13147 := by decide +kernel

theorem rowEval13147 (x : Key → ℝ) : Integer.Sparse.eval row13147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13147, Integer.Sparse.eval_collectBalanced, rawRowCheck13147]

theorem rawRowCheck13148 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form25 = rawRow13148 := by decide +kernel

theorem rowCheck13148 : row13148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13148 := by decide +kernel

theorem rowEval13148 (x : Key → ℝ) : Integer.Sparse.eval row13148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13148, Integer.Sparse.eval_collectBalanced, rawRowCheck13148]

theorem rawRowCheck13149 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form25 = rawRow13149 := by decide +kernel

theorem rowCheck13149 : row13149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13149 := by decide +kernel

theorem rowEval13149 (x : Key → ℝ) : Integer.Sparse.eval row13149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13149, Integer.Sparse.eval_collectBalanced, rawRowCheck13149]

theorem rawRowCheck13150 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form25 = rawRow13150 := by decide +kernel

theorem rowCheck13150 : row13150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13150 := by decide +kernel

theorem rowEval13150 (x : Key → ℝ) : Integer.Sparse.eval row13150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13150, Integer.Sparse.eval_collectBalanced, rawRowCheck13150]

theorem rawRowCheck13151 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form25 = rawRow13151 := by decide +kernel

theorem rowCheck13151 : row13151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13151 := by decide +kernel

theorem rowEval13151 (x : Key → ℝ) : Integer.Sparse.eval row13151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13151, Integer.Sparse.eval_collectBalanced, rawRowCheck13151]

theorem rawRowCheck13152 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form25 = rawRow13152 := by decide +kernel

theorem rowCheck13152 : row13152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13152 := by decide +kernel

theorem rowEval13152 (x : Key → ℝ) : Integer.Sparse.eval row13152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13152, Integer.Sparse.eval_collectBalanced, rawRowCheck13152]

theorem rawRowCheck13153 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form25 = rawRow13153 := by decide +kernel

theorem rowCheck13153 : row13153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13153 := by decide +kernel

theorem rowEval13153 (x : Key → ℝ) : Integer.Sparse.eval row13153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13153, Integer.Sparse.eval_collectBalanced, rawRowCheck13153]

theorem rawRowCheck13154 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form25 = rawRow13154 := by decide +kernel

theorem rowCheck13154 : row13154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13154 := by decide +kernel

theorem rowEval13154 (x : Key → ℝ) : Integer.Sparse.eval row13154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13154, Integer.Sparse.eval_collectBalanced, rawRowCheck13154]

theorem rawRowCheck13155 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form25 = rawRow13155 := by decide +kernel

theorem rowCheck13155 : row13155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13155 := by decide +kernel

theorem rowEval13155 (x : Key → ℝ) : Integer.Sparse.eval row13155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13155, Integer.Sparse.eval_collectBalanced, rawRowCheck13155]

theorem rawRowCheck13156 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form25 = rawRow13156 := by decide +kernel

theorem rowCheck13156 : row13156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13156 := by decide +kernel

theorem rowEval13156 (x : Key → ℝ) : Integer.Sparse.eval row13156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13156, Integer.Sparse.eval_collectBalanced, rawRowCheck13156]

theorem rawRowCheck13157 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form25 = rawRow13157 := by decide +kernel

theorem rowCheck13157 : row13157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13157 := by decide +kernel

theorem rowEval13157 (x : Key → ℝ) : Integer.Sparse.eval row13157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13157, Integer.Sparse.eval_collectBalanced, rawRowCheck13157]

theorem rawRowCheck13158 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form25 = rawRow13158 := by decide +kernel

theorem rowCheck13158 : row13158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13158 := by decide +kernel

theorem rowEval13158 (x : Key → ℝ) : Integer.Sparse.eval row13158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13158, Integer.Sparse.eval_collectBalanced, rawRowCheck13158]

theorem rawRowCheck13159 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form25 = rawRow13159 := by decide +kernel

theorem rowCheck13159 : row13159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13159 := by decide +kernel

theorem rowEval13159 (x : Key → ℝ) : Integer.Sparse.eval row13159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13159, Integer.Sparse.eval_collectBalanced, rawRowCheck13159]

theorem rawRowCheck13160 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form25 = rawRow13160 := by decide +kernel

theorem rowCheck13160 : row13160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13160 := by decide +kernel

theorem rowEval13160 (x : Key → ℝ) : Integer.Sparse.eval row13160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13160, Integer.Sparse.eval_collectBalanced, rawRowCheck13160]

theorem rawRowCheck13161 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form25 = rawRow13161 := by decide +kernel

theorem rowCheck13161 : row13161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13161 := by decide +kernel

theorem rowEval13161 (x : Key → ℝ) : Integer.Sparse.eval row13161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13161, Integer.Sparse.eval_collectBalanced, rawRowCheck13161]

theorem rawRowCheck13162 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form25 = rawRow13162 := by decide +kernel

theorem rowCheck13162 : row13162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13162 := by decide +kernel

theorem rowEval13162 (x : Key → ℝ) : Integer.Sparse.eval row13162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13162, Integer.Sparse.eval_collectBalanced, rawRowCheck13162]

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

theorem entryCheck26_1 : entry26_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_1 k)) := by decide +kernel

theorem rowsSound26_1 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12563 x
  · exact rowEval12564 x
  · exact rowEval12565 x
  · exact rowEval12566 x
  · exact rowEval12567 x
  · exact rowEval12568 x
  · exact rowEval12569 x
  · exact rowEval12570 x
  · exact rowEval12571 x
  · exact rowEval12572 x
  · exact rowEval12573 x
  · exact rowEval12574 x
  · exact rowEval12575 x
  · exact rowEval12576 x
  · exact rowEval12577 x
  · exact rowEval12578 x
  · exact rowEval12579 x
  · exact rowEval12580 x
  · exact rowEval12581 x
  · exact rowEval12582 x
  · exact rowEval12583 x
  · exact rowEval12584 x
  · exact rowEval12585 x
  · exact rowEval12586 x

theorem entryEval26_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_1 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck26_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_1]

theorem entryCheck26_2 : entry26_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_2 k)) := by decide +kernel

theorem rowsSound26_2 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12587 x
  · exact rowEval12588 x
  · exact rowEval12589 x
  · exact rowEval12590 x
  · exact rowEval12591 x
  · exact rowEval12592 x
  · exact rowEval12593 x
  · exact rowEval12594 x
  · exact rowEval12595 x
  · exact rowEval12596 x
  · exact rowEval12597 x
  · exact rowEval12598 x
  · exact rowEval12599 x
  · exact rowEval12600 x
  · exact rowEval12601 x
  · exact rowEval12602 x
  · exact rowEval12603 x
  · exact rowEval12604 x
  · exact rowEval12605 x
  · exact rowEval12606 x
  · exact rowEval12607 x
  · exact rowEval12608 x
  · exact rowEval12609 x
  · exact rowEval12610 x

theorem entryEval26_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_2 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck26_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_2]

theorem entryCheck26_3 : entry26_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_3 k)) := by decide +kernel

theorem rowsSound26_3 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12611 x
  · exact rowEval12612 x
  · exact rowEval12613 x
  · exact rowEval12614 x
  · exact rowEval12615 x
  · exact rowEval12616 x
  · exact rowEval12617 x
  · exact rowEval12618 x
  · exact rowEval12619 x
  · exact rowEval12620 x
  · exact rowEval12621 x
  · exact rowEval12622 x
  · exact rowEval12623 x
  · exact rowEval12624 x
  · exact rowEval12625 x
  · exact rowEval12626 x
  · exact rowEval12627 x
  · exact rowEval12628 x
  · exact rowEval12629 x
  · exact rowEval12630 x
  · exact rowEval12631 x
  · exact rowEval12632 x
  · exact rowEval12633 x
  · exact rowEval12634 x

theorem entryEval26_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_3 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck26_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_3]

theorem entryCheck26_4 : entry26_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_4 k)) := by decide +kernel

theorem rowsSound26_4 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval12635 x
  · exact rowEval12636 x
  · exact rowEval12637 x
  · exact rowEval12638 x
  · exact rowEval12639 x
  · exact rowEval12640 x
  · exact rowEval12641 x
  · exact rowEval12642 x
  · exact rowEval12643 x
  · exact rowEval12644 x
  · exact rowEval12645 x
  · exact rowEval12646 x
  · exact rowEval12647 x
  · exact rowEval12648 x
  · exact rowEval12649 x
  · exact rowEval12650 x
  · exact rowEval12651 x
  · exact rowEval12652 x
  · exact rowEval12653 x
  · exact rowEval12654 x
  · exact rowEval12655 x
  · exact rowEval12656 x
  · exact rowEval12657 x
  · exact rowEval12658 x

theorem entryEval26_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_4 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck26_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_4]

theorem entryCheck26_6 : entry26_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_6 k)) := by decide +kernel

theorem rowsSound26_6 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval12683 x
  · exact rowEval12684 x
  · exact rowEval12685 x
  · exact rowEval12686 x
  · exact rowEval12687 x
  · exact rowEval12688 x
  · exact rowEval12689 x
  · exact rowEval12690 x
  · exact rowEval12691 x
  · exact rowEval12692 x
  · exact rowEval12693 x
  · exact rowEval12694 x
  · exact rowEval12695 x
  · exact rowEval12696 x
  · exact rowEval12697 x
  · exact rowEval12698 x
  · exact rowEval12699 x
  · exact rowEval12700 x
  · exact rowEval12701 x
  · exact rowEval12702 x
  · exact rowEval12703 x
  · exact rowEval12704 x
  · exact rowEval12705 x
  · exact rowEval12706 x

theorem entryEval26_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_6 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck26_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_6]

theorem entryCheck26_11 : entry26_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_11 k)) := by decide +kernel

theorem rowsSound26_11 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval12803 x
  · exact rowEval12804 x
  · exact rowEval12805 x
  · exact rowEval12806 x
  · exact rowEval12807 x
  · exact rowEval12808 x
  · exact rowEval12809 x
  · exact rowEval12810 x
  · exact rowEval12811 x
  · exact rowEval12812 x
  · exact rowEval12813 x
  · exact rowEval12814 x
  · exact rowEval12815 x
  · exact rowEval12816 x
  · exact rowEval12817 x
  · exact rowEval12818 x
  · exact rowEval12819 x
  · exact rowEval12820 x
  · exact rowEval12821 x
  · exact rowEval12822 x
  · exact rowEval12823 x
  · exact rowEval12824 x
  · exact rowEval12825 x
  · exact rowEval12826 x

theorem entryEval26_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_11 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck26_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_11]

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

theorem entryCheck26_13 : entry26_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_13 k)) := by decide +kernel

theorem rowsSound26_13 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12851 x
  · exact rowEval12852 x
  · exact rowEval12853 x
  · exact rowEval12854 x
  · exact rowEval12855 x
  · exact rowEval12856 x
  · exact rowEval12857 x
  · exact rowEval12858 x
  · exact rowEval12859 x
  · exact rowEval12860 x
  · exact rowEval12861 x
  · exact rowEval12862 x
  · exact rowEval12863 x
  · exact rowEval12864 x
  · exact rowEval12865 x
  · exact rowEval12866 x
  · exact rowEval12867 x
  · exact rowEval12868 x
  · exact rowEval12869 x
  · exact rowEval12870 x
  · exact rowEval12871 x
  · exact rowEval12872 x
  · exact rowEval12873 x
  · exact rowEval12874 x

theorem entryEval26_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_13 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck26_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_13]

theorem entryCheck26_14 : entry26_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_14 k)) := by decide +kernel

theorem rowsSound26_14 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12875 x
  · exact rowEval12876 x
  · exact rowEval12877 x
  · exact rowEval12878 x
  · exact rowEval12879 x
  · exact rowEval12880 x
  · exact rowEval12881 x
  · exact rowEval12882 x
  · exact rowEval12883 x
  · exact rowEval12884 x
  · exact rowEval12885 x
  · exact rowEval12886 x
  · exact rowEval12887 x
  · exact rowEval12888 x
  · exact rowEval12889 x
  · exact rowEval12890 x
  · exact rowEval12891 x
  · exact rowEval12892 x
  · exact rowEval12893 x
  · exact rowEval12894 x
  · exact rowEval12895 x
  · exact rowEval12896 x
  · exact rowEval12897 x
  · exact rowEval12898 x

theorem entryEval26_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_14 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck26_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_14]

theorem entryCheck26_15 : entry26_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_15 k)) := by decide +kernel

theorem rowsSound26_15 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12899 x
  · exact rowEval12900 x
  · exact rowEval12901 x
  · exact rowEval12902 x
  · exact rowEval12903 x
  · exact rowEval12904 x
  · exact rowEval12905 x
  · exact rowEval12906 x
  · exact rowEval12907 x
  · exact rowEval12908 x
  · exact rowEval12909 x
  · exact rowEval12910 x
  · exact rowEval12911 x
  · exact rowEval12912 x
  · exact rowEval12913 x
  · exact rowEval12914 x
  · exact rowEval12915 x
  · exact rowEval12916 x
  · exact rowEval12917 x
  · exact rowEval12918 x
  · exact rowEval12919 x
  · exact rowEval12920 x
  · exact rowEval12921 x
  · exact rowEval12922 x

theorem entryEval26_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_15 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck26_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_15]

theorem entryCheck26_16 : entry26_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_16 k)) := by decide +kernel

theorem rowsSound26_16 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12923 x
  · exact rowEval12924 x
  · exact rowEval12925 x
  · exact rowEval12926 x
  · exact rowEval12927 x
  · exact rowEval12928 x
  · exact rowEval12929 x
  · exact rowEval12930 x
  · exact rowEval12931 x
  · exact rowEval12932 x
  · exact rowEval12933 x
  · exact rowEval12934 x
  · exact rowEval12935 x
  · exact rowEval12936 x
  · exact rowEval12937 x
  · exact rowEval12938 x
  · exact rowEval12939 x
  · exact rowEval12940 x
  · exact rowEval12941 x
  · exact rowEval12942 x
  · exact rowEval12943 x
  · exact rowEval12944 x
  · exact rowEval12945 x
  · exact rowEval12946 x

theorem entryEval26_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_16 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck26_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_16]

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

theorem entryCheck26_24 : entry26_24 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_24 k)) := by decide +kernel

theorem rowsSound26_24 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_24 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form24) x := by
  fin_cases k
  · exact rowEval13115 x
  · exact rowEval13116 x
  · exact rowEval13117 x
  · exact rowEval13118 x
  · exact rowEval13119 x
  · exact rowEval13120 x
  · exact rowEval13121 x
  · exact rowEval13122 x
  · exact rowEval13123 x
  · exact rowEval13124 x
  · exact rowEval13125 x
  · exact rowEval13126 x
  · exact rowEval13127 x
  · exact rowEval13128 x
  · exact rowEval13129 x
  · exact rowEval13130 x
  · exact rowEval13131 x
  · exact rowEval13132 x
  · exact rowEval13133 x
  · exact rowEval13134 x
  · exact rowEval13135 x
  · exact rowEval13136 x
  · exact rowEval13137 x
  · exact rowEval13138 x

theorem entryEval26_24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_24 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form24 B := by
  rw [entryCheck26_24, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form24 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_24]

theorem entryCheck26_25 : entry26_25 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_25 k)) := by decide +kernel

theorem rowsSound26_25 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_25 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form25) x := by
  fin_cases k
  · exact rowEval13139 x
  · exact rowEval13140 x
  · exact rowEval13141 x
  · exact rowEval13142 x
  · exact rowEval13143 x
  · exact rowEval13144 x
  · exact rowEval13145 x
  · exact rowEval13146 x
  · exact rowEval13147 x
  · exact rowEval13148 x
  · exact rowEval13149 x
  · exact rowEval13150 x
  · exact rowEval13151 x
  · exact rowEval13152 x
  · exact rowEval13153 x
  · exact rowEval13154 x
  · exact rowEval13155 x
  · exact rowEval13156 x
  · exact rowEval13157 x
  · exact rowEval13158 x
  · exact rowEval13159 x
  · exact rowEval13160 x
  · exact rowEval13161 x
  · exact rowEval13162 x

theorem entryEval26_25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_25 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form25 B := by
  rw [entryCheck26_25, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form25 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_25]

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

theorem entryEvalRow26_e_oai (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 26 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 26).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval26_0_e B hB
  · exact entryEval26_1 B hB
  · exact entryEval26_2 B hB
  · exact entryEval26_3 B hB
  · exact entryEval26_4 B hB
  · exact entryEval26_5_e B hB
  · exact entryEval26_6 B hB
  · exact entryEval26_7_e B hB
  · exact entryEval26_8_e B hB
  · exact entryEval26_9_e B hB
  · exact entryEval26_10_e B hB
  · exact entryEval26_11 B hB
  · exact entryEval26_12 B hB
  · exact entryEval26_13 B hB
  · exact entryEval26_14 B hB
  · exact entryEval26_15 B hB
  · exact entryEval26_16 B hB
  · exact entryEval26_17_e B hB
  · exact entryEval26_18_e B hB
  · exact entryEval26_19 B hB
  · exact entryEval26_20 B hB
  · exact entryEval26_21_e B hB
  · exact entryEval26_22_e B hB
  · exact entryEval26_23_e B hB
  · exact entryEval26_24 B hB
  · exact entryEval26_25 B hB
  · exact entryEval26_26_e B hB

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e_oai
