-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:44:18.314713+00:00
-- url     : https://prove2.me/submissions/d0cce92d-6685-47a7-8d7f-68c318520619

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E026
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E053
import Definitions.Def_OAIQ106E054
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck5160 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form0 = rawRow5160 := by decide +kernel

theorem rowCheck5160 : row5160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5160 := by decide +kernel

theorem rowEval5160 (x : Key → ℝ) : Integer.Sparse.eval row5160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5160, Integer.Sparse.eval_collectBalanced, rawRowCheck5160]

theorem rawRowCheck5161 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form0 = rawRow5161 := by decide +kernel

theorem rowCheck5161 : row5161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5161 := by decide +kernel

theorem rowEval5161 (x : Key → ℝ) : Integer.Sparse.eval row5161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5161, Integer.Sparse.eval_collectBalanced, rawRowCheck5161]

theorem rawRowCheck5162 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form0 = rawRow5162 := by decide +kernel

theorem rowCheck5162 : row5162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5162 := by decide +kernel

theorem rowEval5162 (x : Key → ℝ) : Integer.Sparse.eval row5162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5162, Integer.Sparse.eval_collectBalanced, rawRowCheck5162]

theorem rawRowCheck5163 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form0 = rawRow5163 := by decide +kernel

theorem rowCheck5163 : row5163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5163 := by decide +kernel

theorem rowEval5163 (x : Key → ℝ) : Integer.Sparse.eval row5163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5163, Integer.Sparse.eval_collectBalanced, rawRowCheck5163]

theorem rawRowCheck5164 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form0 = rawRow5164 := by decide +kernel

theorem rowCheck5164 : row5164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5164 := by decide +kernel

theorem rowEval5164 (x : Key → ℝ) : Integer.Sparse.eval row5164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5164, Integer.Sparse.eval_collectBalanced, rawRowCheck5164]

theorem rawRowCheck5165 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form0 = rawRow5165 := by decide +kernel

theorem rowCheck5165 : row5165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5165 := by decide +kernel

theorem rowEval5165 (x : Key → ℝ) : Integer.Sparse.eval row5165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5165, Integer.Sparse.eval_collectBalanced, rawRowCheck5165]

theorem rawRowCheck5166 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form0 = rawRow5166 := by decide +kernel

theorem rowCheck5166 : row5166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5166 := by decide +kernel

theorem rowEval5166 (x : Key → ℝ) : Integer.Sparse.eval row5166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5166, Integer.Sparse.eval_collectBalanced, rawRowCheck5166]

theorem rawRowCheck5167 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form0 = rawRow5167 := by decide +kernel

theorem rowCheck5167 : row5167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5167 := by decide +kernel

theorem rowEval5167 (x : Key → ℝ) : Integer.Sparse.eval row5167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5167, Integer.Sparse.eval_collectBalanced, rawRowCheck5167]

theorem rawRowCheck5168 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form0 = rawRow5168 := by decide +kernel

theorem rowCheck5168 : row5168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5168 := by decide +kernel

theorem rowEval5168 (x : Key → ℝ) : Integer.Sparse.eval row5168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5168, Integer.Sparse.eval_collectBalanced, rawRowCheck5168]

theorem rawRowCheck5169 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form0 = rawRow5169 := by decide +kernel

theorem rowCheck5169 : row5169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5169 := by decide +kernel

theorem rowEval5169 (x : Key → ℝ) : Integer.Sparse.eval row5169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5169, Integer.Sparse.eval_collectBalanced, rawRowCheck5169]

theorem rawRowCheck5170 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form0 = rawRow5170 := by decide +kernel

theorem rowCheck5170 : row5170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5170 := by decide +kernel

theorem rowEval5170 (x : Key → ℝ) : Integer.Sparse.eval row5170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5170, Integer.Sparse.eval_collectBalanced, rawRowCheck5170]

theorem rawRowCheck5171 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form0 = rawRow5171 := by decide +kernel

theorem rowCheck5171 : row5171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5171 := by decide +kernel

theorem rowEval5171 (x : Key → ℝ) : Integer.Sparse.eval row5171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5171, Integer.Sparse.eval_collectBalanced, rawRowCheck5171]

theorem rawRowCheck5174 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form0 = rawRow5174 := by decide +kernel

theorem rowCheck5174 : row5174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5174 := by decide +kernel

theorem rowEval5174 (x : Key → ℝ) : Integer.Sparse.eval row5174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5174, Integer.Sparse.eval_collectBalanced, rawRowCheck5174]

theorem rawRowCheck5175 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form0 = rawRow5175 := by decide +kernel

theorem rowCheck5175 : row5175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5175 := by decide +kernel

theorem rowEval5175 (x : Key → ℝ) : Integer.Sparse.eval row5175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5175, Integer.Sparse.eval_collectBalanced, rawRowCheck5175]

theorem rawRowCheck5176 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form0 = rawRow5176 := by decide +kernel

theorem rowCheck5176 : row5176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5176 := by decide +kernel

theorem rowEval5176 (x : Key → ℝ) : Integer.Sparse.eval row5176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5176, Integer.Sparse.eval_collectBalanced, rawRowCheck5176]

theorem rawRowCheck5177 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form0 = rawRow5177 := by decide +kernel

theorem rowCheck5177 : row5177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5177 := by decide +kernel

theorem rowEval5177 (x : Key → ℝ) : Integer.Sparse.eval row5177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5177, Integer.Sparse.eval_collectBalanced, rawRowCheck5177]

theorem rawRowCheck5182 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form0 = rawRow5182 := by decide +kernel

theorem rowCheck5182 : row5182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5182 := by decide +kernel

theorem rowEval5182 (x : Key → ℝ) : Integer.Sparse.eval row5182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5182, Integer.Sparse.eval_collectBalanced, rawRowCheck5182]

theorem rawRowCheck5183 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form0 = rawRow5183 := by decide +kernel

theorem rowCheck5183 : row5183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5183 := by decide +kernel

theorem rowEval5183 (x : Key → ℝ) : Integer.Sparse.eval row5183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5183, Integer.Sparse.eval_collectBalanced, rawRowCheck5183]

theorem rawRowCheck5184 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form0 = rawRow5184 := by decide +kernel

theorem rowCheck5184 : row5184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5184 := by decide +kernel

theorem rowEval5184 (x : Key → ℝ) : Integer.Sparse.eval row5184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5184, Integer.Sparse.eval_collectBalanced, rawRowCheck5184]

theorem rawRowCheck5185 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form0 = rawRow5185 := by decide +kernel

theorem rowCheck5185 : row5185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5185 := by decide +kernel

theorem rowEval5185 (x : Key → ℝ) : Integer.Sparse.eval row5185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5185, Integer.Sparse.eval_collectBalanced, rawRowCheck5185]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck6178 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form0 = rawRow6178 := by decide +kernel

theorem rowCheck6178 : row6178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6178 := by decide +kernel

theorem rowEval6178 (x : Key → ℝ) : Integer.Sparse.eval row6178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6178, Integer.Sparse.eval_collectBalanced, rawRowCheck6178]

theorem rawRowCheck6179 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form0 = rawRow6179 := by decide +kernel

theorem rowCheck6179 : row6179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6179 := by decide +kernel

theorem rowEval6179 (x : Key → ℝ) : Integer.Sparse.eval row6179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6179, Integer.Sparse.eval_collectBalanced, rawRowCheck6179]

theorem rawRowCheck6180 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form0 = rawRow6180 := by decide +kernel

theorem rowCheck6180 : row6180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6180 := by decide +kernel

theorem rowEval6180 (x : Key → ℝ) : Integer.Sparse.eval row6180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6180, Integer.Sparse.eval_collectBalanced, rawRowCheck6180]

theorem rawRowCheck6181 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form0 = rawRow6181 := by decide +kernel

theorem rowCheck6181 : row6181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6181 := by decide +kernel

theorem rowEval6181 (x : Key → ℝ) : Integer.Sparse.eval row6181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6181, Integer.Sparse.eval_collectBalanced, rawRowCheck6181]

theorem rawRowCheck6182 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form0 = rawRow6182 := by decide +kernel

theorem rowCheck6182 : row6182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6182 := by decide +kernel

theorem rowEval6182 (x : Key → ℝ) : Integer.Sparse.eval row6182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6182, Integer.Sparse.eval_collectBalanced, rawRowCheck6182]

theorem rawRowCheck6183 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form0 = rawRow6183 := by decide +kernel

theorem rowCheck6183 : row6183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6183 := by decide +kernel

theorem rowEval6183 (x : Key → ℝ) : Integer.Sparse.eval row6183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6183, Integer.Sparse.eval_collectBalanced, rawRowCheck6183]

theorem rawRowCheck6184 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form0 = rawRow6184 := by decide +kernel

theorem rowCheck6184 : row6184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6184 := by decide +kernel

theorem rowEval6184 (x : Key → ℝ) : Integer.Sparse.eval row6184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6184, Integer.Sparse.eval_collectBalanced, rawRowCheck6184]

theorem rawRowCheck6185 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form0 = rawRow6185 := by decide +kernel

theorem rowCheck6185 : row6185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6185 := by decide +kernel

theorem rowEval6185 (x : Key → ℝ) : Integer.Sparse.eval row6185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6185, Integer.Sparse.eval_collectBalanced, rawRowCheck6185]

theorem rawRowCheck6186 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form0 = rawRow6186 := by decide +kernel

theorem rowCheck6186 : row6186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6186 := by decide +kernel

theorem rowEval6186 (x : Key → ℝ) : Integer.Sparse.eval row6186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6186, Integer.Sparse.eval_collectBalanced, rawRowCheck6186]

theorem rawRowCheck6187 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form0 = rawRow6187 := by decide +kernel

theorem rowCheck6187 : row6187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6187 := by decide +kernel

theorem rowEval6187 (x : Key → ℝ) : Integer.Sparse.eval row6187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6187, Integer.Sparse.eval_collectBalanced, rawRowCheck6187]

theorem rawRowCheck6188 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form0 = rawRow6188 := by decide +kernel

theorem rowCheck6188 : row6188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6188 := by decide +kernel

theorem rowEval6188 (x : Key → ℝ) : Integer.Sparse.eval row6188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6188, Integer.Sparse.eval_collectBalanced, rawRowCheck6188]

theorem rawRowCheck6189 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form0 = rawRow6189 := by decide +kernel

theorem rowCheck6189 : row6189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6189 := by decide +kernel

theorem rowEval6189 (x : Key → ℝ) : Integer.Sparse.eval row6189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6189, Integer.Sparse.eval_collectBalanced, rawRowCheck6189]

theorem rawRowCheck6190 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form0 = rawRow6190 := by decide +kernel

theorem rowCheck6190 : row6190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6190 := by decide +kernel

theorem rowEval6190 (x : Key → ℝ) : Integer.Sparse.eval row6190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6190, Integer.Sparse.eval_collectBalanced, rawRowCheck6190]

theorem rawRowCheck6191 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form0 = rawRow6191 := by decide +kernel

theorem rowCheck6191 : row6191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6191 := by decide +kernel

theorem rowEval6191 (x : Key → ℝ) : Integer.Sparse.eval row6191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6191, Integer.Sparse.eval_collectBalanced, rawRowCheck6191]

theorem rawRowCheck6192 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form0 = rawRow6192 := by decide +kernel

theorem rowCheck6192 : row6192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6192 := by decide +kernel

theorem rowEval6192 (x : Key → ℝ) : Integer.Sparse.eval row6192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6192, Integer.Sparse.eval_collectBalanced, rawRowCheck6192]

theorem rawRowCheck6193 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form0 = rawRow6193 := by decide +kernel

theorem rowCheck6193 : row6193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6193 := by decide +kernel

theorem rowEval6193 (x : Key → ℝ) : Integer.Sparse.eval row6193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6193, Integer.Sparse.eval_collectBalanced, rawRowCheck6193]

theorem rawRowCheck6194 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form0 = rawRow6194 := by decide +kernel

theorem rowCheck6194 : row6194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6194 := by decide +kernel

theorem rowEval6194 (x : Key → ℝ) : Integer.Sparse.eval row6194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6194, Integer.Sparse.eval_collectBalanced, rawRowCheck6194]

theorem rawRowCheck6195 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form0 = rawRow6195 := by decide +kernel

theorem rowCheck6195 : row6195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6195 := by decide +kernel

theorem rowEval6195 (x : Key → ℝ) : Integer.Sparse.eval row6195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6195, Integer.Sparse.eval_collectBalanced, rawRowCheck6195]

theorem rawRowCheck6196 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form0 = rawRow6196 := by decide +kernel

theorem rowCheck6196 : row6196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6196 := by decide +kernel

theorem rowEval6196 (x : Key → ℝ) : Integer.Sparse.eval row6196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6196, Integer.Sparse.eval_collectBalanced, rawRowCheck6196]

theorem rawRowCheck6197 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form0 = rawRow6197 := by decide +kernel

theorem rowCheck6197 : row6197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6197 := by decide +kernel

theorem rowEval6197 (x : Key → ℝ) : Integer.Sparse.eval row6197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6197, Integer.Sparse.eval_collectBalanced, rawRowCheck6197]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5160 x
  · exact rowEval5161 x
  · exact rowEval5162 x
  · exact rowEval5163 x
  · exact rowEval5164 x
  · exact rowEval5165 x
  · exact rowEval5166 x
  · exact rowEval5167 x
  · exact rowEval5168 x
  · exact rowEval5169 x
  · exact rowEval5170 x
  · exact rowEval5171 x
  · exact rowEval6178 x
  · exact rowEval6179 x
  · exact rowEval5174 x
  · exact rowEval5175 x
  · exact rowEval6180 x
  · exact rowEval6181 x
  · exact rowEval5176 x
  · exact rowEval5177 x
  · exact rowEval5182 x
  · exact rowEval5183 x
  · exact rowEval6182 x
  · exact rowEval6183 x
  · exact rowEval5184 x
  · exact rowEval5185 x
  · exact rowEval6184 x
  · exact rowEval6185 x
  · exact rowEval6186 x
  · exact rowEval6187 x
  · exact rowEval6188 x
  · exact rowEval6189 x
  · exact rowEval6190 x
  · exact rowEval6191 x
  · exact rowEval6192 x
  · exact rowEval6193 x
  · exact rowEval6194 x
  · exact rowEval6195 x
  · exact rowEval6196 x
  · exact rowEval6197 x

theorem entryEval7_0_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_0_e_oai
