-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:31:29.225768+00:00
-- url     : https://prove2.me/submissions/18a82e43-9ac2-4275-bee6-f070ffe939bc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E055
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7018 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form0 = rawRow7018 := by decide +kernel

theorem rowCheck7018 : row7018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7018 := by decide +kernel

theorem rowEval7018 (x : Key → ℝ) : Integer.Sparse.eval row7018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7018, Integer.Sparse.eval_collectBalanced, rawRowCheck7018]

theorem rawRowCheck7019 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form0 = rawRow7019 := by decide +kernel

theorem rowCheck7019 : row7019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7019 := by decide +kernel

theorem rowEval7019 (x : Key → ℝ) : Integer.Sparse.eval row7019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7019, Integer.Sparse.eval_collectBalanced, rawRowCheck7019]

theorem rawRowCheck7020 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form0 = rawRow7020 := by decide +kernel

theorem rowCheck7020 : row7020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7020 := by decide +kernel

theorem rowEval7020 (x : Key → ℝ) : Integer.Sparse.eval row7020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7020, Integer.Sparse.eval_collectBalanced, rawRowCheck7020]

theorem rawRowCheck7021 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow7021 := by decide +kernel

theorem rowCheck7021 : row7021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7021 := by decide +kernel

theorem rowEval7021 (x : Key → ℝ) : Integer.Sparse.eval row7021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7021, Integer.Sparse.eval_collectBalanced, rawRowCheck7021]

theorem rawRowCheck7022 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow7022 := by decide +kernel

theorem rowCheck7022 : row7022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7022 := by decide +kernel

theorem rowEval7022 (x : Key → ℝ) : Integer.Sparse.eval row7022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7022, Integer.Sparse.eval_collectBalanced, rawRowCheck7022]

theorem rawRowCheck7023 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow7023 := by decide +kernel

theorem rowCheck7023 : row7023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7023 := by decide +kernel

theorem rowEval7023 (x : Key → ℝ) : Integer.Sparse.eval row7023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7023, Integer.Sparse.eval_collectBalanced, rawRowCheck7023]

theorem rawRowCheck7024 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form0 = rawRow7024 := by decide +kernel

theorem rowCheck7024 : row7024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7024 := by decide +kernel

theorem rowEval7024 (x : Key → ℝ) : Integer.Sparse.eval row7024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7024, Integer.Sparse.eval_collectBalanced, rawRowCheck7024]

theorem rawRowCheck7025 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form0 = rawRow7025 := by decide +kernel

theorem rowCheck7025 : row7025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7025 := by decide +kernel

theorem rowEval7025 (x : Key → ℝ) : Integer.Sparse.eval row7025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7025, Integer.Sparse.eval_collectBalanced, rawRowCheck7025]

theorem rawRowCheck7026 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form0 = rawRow7026 := by decide +kernel

theorem rowCheck7026 : row7026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7026 := by decide +kernel

theorem rowEval7026 (x : Key → ℝ) : Integer.Sparse.eval row7026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7026, Integer.Sparse.eval_collectBalanced, rawRowCheck7026]

theorem rawRowCheck7027 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form0 = rawRow7027 := by decide +kernel

theorem rowCheck7027 : row7027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7027 := by decide +kernel

theorem rowEval7027 (x : Key → ℝ) : Integer.Sparse.eval row7027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7027, Integer.Sparse.eval_collectBalanced, rawRowCheck7027]

theorem rawRowCheck7028 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form0 = rawRow7028 := by decide +kernel

theorem rowCheck7028 : row7028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7028 := by decide +kernel

theorem rowEval7028 (x : Key → ℝ) : Integer.Sparse.eval row7028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7028, Integer.Sparse.eval_collectBalanced, rawRowCheck7028]

theorem rawRowCheck7029 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form0 = rawRow7029 := by decide +kernel

theorem rowCheck7029 : row7029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7029 := by decide +kernel

theorem rowEval7029 (x : Key → ℝ) : Integer.Sparse.eval row7029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7029, Integer.Sparse.eval_collectBalanced, rawRowCheck7029]

theorem rawRowCheck7030 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form0 = rawRow7030 := by decide +kernel

theorem rowCheck7030 : row7030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7030 := by decide +kernel

theorem rowEval7030 (x : Key → ℝ) : Integer.Sparse.eval row7030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7030, Integer.Sparse.eval_collectBalanced, rawRowCheck7030]

theorem rawRowCheck7031 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form0 = rawRow7031 := by decide +kernel

theorem rowCheck7031 : row7031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7031 := by decide +kernel

theorem rowEval7031 (x : Key → ℝ) : Integer.Sparse.eval row7031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7031, Integer.Sparse.eval_collectBalanced, rawRowCheck7031]

theorem rawRowCheck7032 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form0 = rawRow7032 := by decide +kernel

theorem rowCheck7032 : row7032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7032 := by decide +kernel

theorem rowEval7032 (x : Key → ℝ) : Integer.Sparse.eval row7032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7032, Integer.Sparse.eval_collectBalanced, rawRowCheck7032]

theorem rawRowCheck7033 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form0 = rawRow7033 := by decide +kernel

theorem rowCheck7033 : row7033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7033 := by decide +kernel

theorem rowEval7033 (x : Key → ℝ) : Integer.Sparse.eval row7033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7033, Integer.Sparse.eval_collectBalanced, rawRowCheck7033]

theorem rawRowCheck7034 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form0 = rawRow7034 := by decide +kernel

theorem rowCheck7034 : row7034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7034 := by decide +kernel

theorem rowEval7034 (x : Key → ℝ) : Integer.Sparse.eval row7034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7034, Integer.Sparse.eval_collectBalanced, rawRowCheck7034]

theorem rawRowCheck7035 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form0 = rawRow7035 := by decide +kernel

theorem rowCheck7035 : row7035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7035 := by decide +kernel

theorem rowEval7035 (x : Key → ℝ) : Integer.Sparse.eval row7035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7035, Integer.Sparse.eval_collectBalanced, rawRowCheck7035]

theorem rawRowCheck7036 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow7036 := by decide +kernel

theorem rowCheck7036 : row7036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7036 := by decide +kernel

theorem rowEval7036 (x : Key → ℝ) : Integer.Sparse.eval row7036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7036, Integer.Sparse.eval_collectBalanced, rawRowCheck7036]

theorem rawRowCheck7037 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow7037 := by decide +kernel

theorem rowCheck7037 : row7037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7037 := by decide +kernel

theorem rowEval7037 (x : Key → ℝ) : Integer.Sparse.eval row7037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7037, Integer.Sparse.eval_collectBalanced, rawRowCheck7037]

theorem rawRowCheck7038 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow7038 := by decide +kernel

theorem rowCheck7038 : row7038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7038 := by decide +kernel

theorem rowEval7038 (x : Key → ℝ) : Integer.Sparse.eval row7038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7038, Integer.Sparse.eval_collectBalanced, rawRowCheck7038]

theorem rawRowCheck7039 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form0 = rawRow7039 := by decide +kernel

theorem rowCheck7039 : row7039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7039 := by decide +kernel

theorem rowEval7039 (x : Key → ℝ) : Integer.Sparse.eval row7039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7039, Integer.Sparse.eval_collectBalanced, rawRowCheck7039]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7040 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form0 = rawRow7040 := by decide +kernel

theorem rowCheck7040 : row7040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7040 := by decide +kernel

theorem rowEval7040 (x : Key → ℝ) : Integer.Sparse.eval row7040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7040, Integer.Sparse.eval_collectBalanced, rawRowCheck7040]

theorem rawRowCheck7041 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form0 = rawRow7041 := by decide +kernel

theorem rowCheck7041 : row7041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7041 := by decide +kernel

theorem rowEval7041 (x : Key → ℝ) : Integer.Sparse.eval row7041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7041, Integer.Sparse.eval_collectBalanced, rawRowCheck7041]

theorem rawRowCheck7042 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form0 = rawRow7042 := by decide +kernel

theorem rowCheck7042 : row7042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7042 := by decide +kernel

theorem rowEval7042 (x : Key → ℝ) : Integer.Sparse.eval row7042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7042, Integer.Sparse.eval_collectBalanced, rawRowCheck7042]

theorem rawRowCheck7043 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form0 = rawRow7043 := by decide +kernel

theorem rowCheck7043 : row7043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7043 := by decide +kernel

theorem rowEval7043 (x : Key → ℝ) : Integer.Sparse.eval row7043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7043, Integer.Sparse.eval_collectBalanced, rawRowCheck7043]

theorem rawRowCheck7044 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form0 = rawRow7044 := by decide +kernel

theorem rowCheck7044 : row7044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7044 := by decide +kernel

theorem rowEval7044 (x : Key → ℝ) : Integer.Sparse.eval row7044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7044, Integer.Sparse.eval_collectBalanced, rawRowCheck7044]

theorem rawRowCheck7045 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form0 = rawRow7045 := by decide +kernel

theorem rowCheck7045 : row7045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7045 := by decide +kernel

theorem rowEval7045 (x : Key → ℝ) : Integer.Sparse.eval row7045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7045, Integer.Sparse.eval_collectBalanced, rawRowCheck7045]

theorem rawRowCheck7046 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form0 = rawRow7046 := by decide +kernel

theorem rowCheck7046 : row7046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7046 := by decide +kernel

theorem rowEval7046 (x : Key → ℝ) : Integer.Sparse.eval row7046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7046, Integer.Sparse.eval_collectBalanced, rawRowCheck7046]

theorem rawRowCheck7047 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form0 = rawRow7047 := by decide +kernel

theorem rowCheck7047 : row7047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7047 := by decide +kernel

theorem rowEval7047 (x : Key → ℝ) : Integer.Sparse.eval row7047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7047, Integer.Sparse.eval_collectBalanced, rawRowCheck7047]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval7018 x
  · exact rowEval7019 x
  · exact rowEval7020 x
  · exact rowEval7021 x
  · exact rowEval7022 x
  · exact rowEval7023 x
  · exact rowEval7024 x
  · exact rowEval7025 x
  · exact rowEval7026 x
  · exact rowEval7027 x
  · exact rowEval7028 x
  · exact rowEval7029 x
  · exact rowEval7030 x
  · exact rowEval7031 x
  · exact rowEval7032 x
  · exact rowEval7033 x
  · exact rowEval7034 x
  · exact rowEval7035 x
  · exact rowEval7036 x
  · exact rowEval7037 x
  · exact rowEval7038 x
  · exact rowEval7039 x
  · exact rowEval7040 x
  · exact rowEval7041 x
  · exact rowEval7042 x
  · exact rowEval7043 x
  · exact rowEval7044 x
  · exact rowEval7045 x
  · exact rowEval7046 x
  · exact rowEval7047 x

theorem entryEval10_0_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_0_e_oai
