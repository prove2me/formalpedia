-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:46:42.593889+00:00
-- url     : https://prove2.me/submissions/35130a48-8020-4999-98b7-dcaf85ed7720

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E037
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck20204 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form10 = rawRow20204 := by decide +kernel

theorem rowCheck20204 : row20204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20204 := by decide +kernel

theorem rowEval20204 (x : Key → ℝ) : Integer.Sparse.eval row20204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20204, Integer.Sparse.eval_collectBalanced, rawRowCheck20204]

theorem rawRowCheck20205 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form10 = rawRow20205 := by decide +kernel

theorem rowCheck20205 : row20205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20205 := by decide +kernel

theorem rowEval20205 (x : Key → ℝ) : Integer.Sparse.eval row20205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20205, Integer.Sparse.eval_collectBalanced, rawRowCheck20205]

theorem rawRowCheck20206 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form10 = rawRow20206 := by decide +kernel

theorem rowCheck20206 : row20206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20206 := by decide +kernel

theorem rowEval20206 (x : Key → ℝ) : Integer.Sparse.eval row20206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20206, Integer.Sparse.eval_collectBalanced, rawRowCheck20206]

theorem rawRowCheck20207 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form10 = rawRow20207 := by decide +kernel

theorem rowCheck20207 : row20207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20207 := by decide +kernel

theorem rowEval20207 (x : Key → ℝ) : Integer.Sparse.eval row20207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20207, Integer.Sparse.eval_collectBalanced, rawRowCheck20207]

theorem rawRowCheck20208 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form10 = rawRow20208 := by decide +kernel

theorem rowCheck20208 : row20208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20208 := by decide +kernel

theorem rowEval20208 (x : Key → ℝ) : Integer.Sparse.eval row20208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20208, Integer.Sparse.eval_collectBalanced, rawRowCheck20208]

theorem rawRowCheck20209 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form10 = rawRow20209 := by decide +kernel

theorem rowCheck20209 : row20209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20209 := by decide +kernel

theorem rowEval20209 (x : Key → ℝ) : Integer.Sparse.eval row20209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20209, Integer.Sparse.eval_collectBalanced, rawRowCheck20209]

theorem rawRowCheck20210 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form10 = rawRow20210 := by decide +kernel

theorem rowCheck20210 : row20210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20210 := by decide +kernel

theorem rowEval20210 (x : Key → ℝ) : Integer.Sparse.eval row20210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20210, Integer.Sparse.eval_collectBalanced, rawRowCheck20210]

theorem rawRowCheck20211 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form10 = rawRow20211 := by decide +kernel

theorem rowCheck20211 : row20211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20211 := by decide +kernel

theorem rowEval20211 (x : Key → ℝ) : Integer.Sparse.eval row20211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20211, Integer.Sparse.eval_collectBalanced, rawRowCheck20211]

theorem rawRowCheck20212 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form10 = rawRow20212 := by decide +kernel

theorem rowCheck20212 : row20212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20212 := by decide +kernel

theorem rowEval20212 (x : Key → ℝ) : Integer.Sparse.eval row20212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20212, Integer.Sparse.eval_collectBalanced, rawRowCheck20212]

theorem rawRowCheck20213 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form10 = rawRow20213 := by decide +kernel

theorem rowCheck20213 : row20213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20213 := by decide +kernel

theorem rowEval20213 (x : Key → ℝ) : Integer.Sparse.eval row20213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20213, Integer.Sparse.eval_collectBalanced, rawRowCheck20213]

theorem rawRowCheck20214 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form10 = rawRow20214 := by decide +kernel

theorem rowCheck20214 : row20214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20214 := by decide +kernel

theorem rowEval20214 (x : Key → ℝ) : Integer.Sparse.eval row20214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20214, Integer.Sparse.eval_collectBalanced, rawRowCheck20214]

theorem rawRowCheck20215 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form10 = rawRow20215 := by decide +kernel

theorem rowCheck20215 : row20215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20215 := by decide +kernel

theorem rowEval20215 (x : Key → ℝ) : Integer.Sparse.eval row20215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20215, Integer.Sparse.eval_collectBalanced, rawRowCheck20215]

theorem rawRowCheck20216 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form10 = rawRow20216 := by decide +kernel

theorem rowCheck20216 : row20216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20216 := by decide +kernel

theorem rowEval20216 (x : Key → ℝ) : Integer.Sparse.eval row20216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20216, Integer.Sparse.eval_collectBalanced, rawRowCheck20216]

theorem rawRowCheck20217 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form10 = rawRow20217 := by decide +kernel

theorem rowCheck20217 : row20217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20217 := by decide +kernel

theorem rowEval20217 (x : Key → ℝ) : Integer.Sparse.eval row20217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20217, Integer.Sparse.eval_collectBalanced, rawRowCheck20217]

theorem rawRowCheck20218 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form10 = rawRow20218 := by decide +kernel

theorem rowCheck20218 : row20218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20218 := by decide +kernel

theorem rowEval20218 (x : Key → ℝ) : Integer.Sparse.eval row20218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20218, Integer.Sparse.eval_collectBalanced, rawRowCheck20218]

theorem rawRowCheck20219 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form10 = rawRow20219 := by decide +kernel

theorem rowCheck20219 : row20219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20219 := by decide +kernel

theorem rowEval20219 (x : Key → ℝ) : Integer.Sparse.eval row20219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20219, Integer.Sparse.eval_collectBalanced, rawRowCheck20219]

theorem rawRowCheck20220 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form10 = rawRow20220 := by decide +kernel

theorem rowCheck20220 : row20220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20220 := by decide +kernel

theorem rowEval20220 (x : Key → ℝ) : Integer.Sparse.eval row20220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20220, Integer.Sparse.eval_collectBalanced, rawRowCheck20220]

theorem rawRowCheck20221 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form10 = rawRow20221 := by decide +kernel

theorem rowCheck20221 : row20221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20221 := by decide +kernel

theorem rowEval20221 (x : Key → ℝ) : Integer.Sparse.eval row20221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20221, Integer.Sparse.eval_collectBalanced, rawRowCheck20221]

theorem rawRowCheck20222 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form10 = rawRow20222 := by decide +kernel

theorem rowCheck20222 : row20222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20222 := by decide +kernel

theorem rowEval20222 (x : Key → ℝ) : Integer.Sparse.eval row20222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20222, Integer.Sparse.eval_collectBalanced, rawRowCheck20222]

theorem rawRowCheck20223 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form10 = rawRow20223 := by decide +kernel

theorem rowCheck20223 : row20223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20223 := by decide +kernel

theorem rowEval20223 (x : Key → ℝ) : Integer.Sparse.eval row20223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20223, Integer.Sparse.eval_collectBalanced, rawRowCheck20223]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck20224 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form10 = rawRow20224 := by decide +kernel

theorem rowCheck20224 : row20224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20224 := by decide +kernel

theorem rowEval20224 (x : Key → ℝ) : Integer.Sparse.eval row20224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20224, Integer.Sparse.eval_collectBalanced, rawRowCheck20224]

theorem rawRowCheck20225 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form10 = rawRow20225 := by decide +kernel

theorem rowCheck20225 : row20225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20225 := by decide +kernel

theorem rowEval20225 (x : Key → ℝ) : Integer.Sparse.eval row20225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20225, Integer.Sparse.eval_collectBalanced, rawRowCheck20225]

theorem rawRowCheck20226 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form10 = rawRow20226 := by decide +kernel

theorem rowCheck20226 : row20226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20226 := by decide +kernel

theorem rowEval20226 (x : Key → ℝ) : Integer.Sparse.eval row20226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20226, Integer.Sparse.eval_collectBalanced, rawRowCheck20226]

theorem rawRowCheck20227 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form10 = rawRow20227 := by decide +kernel

theorem rowCheck20227 : row20227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20227 := by decide +kernel

theorem rowEval20227 (x : Key → ℝ) : Integer.Sparse.eval row20227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20227, Integer.Sparse.eval_collectBalanced, rawRowCheck20227]

theorem rawRowCheck20228 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form10 = rawRow20228 := by decide +kernel

theorem rowCheck20228 : row20228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20228 := by decide +kernel

theorem rowEval20228 (x : Key → ℝ) : Integer.Sparse.eval row20228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20228, Integer.Sparse.eval_collectBalanced, rawRowCheck20228]

theorem rawRowCheck20229 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form10 = rawRow20229 := by decide +kernel

theorem rowCheck20229 : row20229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20229 := by decide +kernel

theorem rowEval20229 (x : Key → ℝ) : Integer.Sparse.eval row20229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20229, Integer.Sparse.eval_collectBalanced, rawRowCheck20229]

theorem rawRowCheck20230 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form10 = rawRow20230 := by decide +kernel

theorem rowCheck20230 : row20230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20230 := by decide +kernel

theorem rowEval20230 (x : Key → ℝ) : Integer.Sparse.eval row20230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20230, Integer.Sparse.eval_collectBalanced, rawRowCheck20230]

theorem rawRowCheck20231 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form10 = rawRow20231 := by decide +kernel

theorem rowCheck20231 : row20231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20231 := by decide +kernel

theorem rowEval20231 (x : Key → ℝ) : Integer.Sparse.eval row20231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20231, Integer.Sparse.eval_collectBalanced, rawRowCheck20231]

theorem rawRowCheck20232 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form10 = rawRow20232 := by decide +kernel

theorem rowCheck20232 : row20232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20232 := by decide +kernel

theorem rowEval20232 (x : Key → ℝ) : Integer.Sparse.eval row20232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20232, Integer.Sparse.eval_collectBalanced, rawRowCheck20232]

theorem rawRowCheck20233 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form10 = rawRow20233 := by decide +kernel

theorem rowCheck20233 : row20233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20233 := by decide +kernel

theorem rowEval20233 (x : Key → ℝ) : Integer.Sparse.eval row20233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20233, Integer.Sparse.eval_collectBalanced, rawRowCheck20233]

theorem rawRowCheck20234 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form10 = rawRow20234 := by decide +kernel

theorem rowCheck20234 : row20234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20234 := by decide +kernel

theorem rowEval20234 (x : Key → ℝ) : Integer.Sparse.eval row20234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20234, Integer.Sparse.eval_collectBalanced, rawRowCheck20234]

theorem rawRowCheck20235 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form10 = rawRow20235 := by decide +kernel

theorem rowCheck20235 : row20235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20235 := by decide +kernel

theorem rowEval20235 (x : Key → ℝ) : Integer.Sparse.eval row20235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20235, Integer.Sparse.eval_collectBalanced, rawRowCheck20235]

theorem rawRowCheck20236 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form10 = rawRow20236 := by decide +kernel

theorem rowCheck20236 : row20236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20236 := by decide +kernel

theorem rowEval20236 (x : Key → ℝ) : Integer.Sparse.eval row20236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20236, Integer.Sparse.eval_collectBalanced, rawRowCheck20236]

theorem rawRowCheck20237 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form10 = rawRow20237 := by decide +kernel

theorem rowCheck20237 : row20237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20237 := by decide +kernel

theorem rowEval20237 (x : Key → ℝ) : Integer.Sparse.eval row20237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20237, Integer.Sparse.eval_collectBalanced, rawRowCheck20237]

theorem rawRowCheck20238 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form10 = rawRow20238 := by decide +kernel

theorem rowCheck20238 : row20238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20238 := by decide +kernel

theorem rowEval20238 (x : Key → ℝ) : Integer.Sparse.eval row20238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20238, Integer.Sparse.eval_collectBalanced, rawRowCheck20238]

theorem rawRowCheck20239 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form10 = rawRow20239 := by decide +kernel

theorem rowCheck20239 : row20239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20239 := by decide +kernel

theorem rowEval20239 (x : Key → ℝ) : Integer.Sparse.eval row20239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20239, Integer.Sparse.eval_collectBalanced, rawRowCheck20239]

theorem rawRowCheck20240 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form10 = rawRow20240 := by decide +kernel

theorem rowCheck20240 : row20240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20240 := by decide +kernel

theorem rowEval20240 (x : Key → ℝ) : Integer.Sparse.eval row20240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20240, Integer.Sparse.eval_collectBalanced, rawRowCheck20240]

theorem rawRowCheck20241 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form10 = rawRow20241 := by decide +kernel

theorem rowCheck20241 : row20241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20241 := by decide +kernel

theorem rowEval20241 (x : Key → ℝ) : Integer.Sparse.eval row20241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20241, Integer.Sparse.eval_collectBalanced, rawRowCheck20241]

theorem rawRowCheck20242 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form10 = rawRow20242 := by decide +kernel

theorem rowCheck20242 : row20242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20242 := by decide +kernel

theorem rowEval20242 (x : Key → ℝ) : Integer.Sparse.eval row20242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20242, Integer.Sparse.eval_collectBalanced, rawRowCheck20242]

theorem rawRowCheck20243 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form10 = rawRow20243 := by decide +kernel

theorem rowCheck20243 : row20243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20243 := by decide +kernel

theorem rowEval20243 (x : Key → ℝ) : Integer.Sparse.eval row20243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20243, Integer.Sparse.eval_collectBalanced, rawRowCheck20243]

theorem rawRowCheck20244 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form10 = rawRow20244 := by decide +kernel

theorem rowCheck20244 : row20244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20244 := by decide +kernel

theorem rowEval20244 (x : Key → ℝ) : Integer.Sparse.eval row20244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20244, Integer.Sparse.eval_collectBalanced, rawRowCheck20244]

theorem rawRowCheck20245 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form10 = rawRow20245 := by decide +kernel

theorem rowCheck20245 : row20245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20245 := by decide +kernel

theorem rowEval20245 (x : Key → ℝ) : Integer.Sparse.eval row20245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20245, Integer.Sparse.eval_collectBalanced, rawRowCheck20245]

theorem rawRowCheck20246 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form10 = rawRow20246 := by decide +kernel

theorem rowCheck20246 : row20246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20246 := by decide +kernel

theorem rowEval20246 (x : Key → ℝ) : Integer.Sparse.eval row20246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20246, Integer.Sparse.eval_collectBalanced, rawRowCheck20246]

theorem rawRowCheck20247 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form10 = rawRow20247 := by decide +kernel

theorem rowCheck20247 : row20247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20247 := by decide +kernel

theorem rowEval20247 (x : Key → ℝ) : Integer.Sparse.eval row20247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20247, Integer.Sparse.eval_collectBalanced, rawRowCheck20247]

theorem rawRowCheck20248 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form10 = rawRow20248 := by decide +kernel

theorem rowCheck20248 : row20248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20248 := by decide +kernel

theorem rowEval20248 (x : Key → ℝ) : Integer.Sparse.eval row20248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20248, Integer.Sparse.eval_collectBalanced, rawRowCheck20248]

theorem rawRowCheck20249 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form10 = rawRow20249 := by decide +kernel

theorem rowCheck20249 : row20249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20249 := by decide +kernel

theorem rowEval20249 (x : Key → ℝ) : Integer.Sparse.eval row20249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20249, Integer.Sparse.eval_collectBalanced, rawRowCheck20249]

theorem rawRowCheck20250 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form10 = rawRow20250 := by decide +kernel

theorem rowCheck20250 : row20250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20250 := by decide +kernel

theorem rowEval20250 (x : Key → ℝ) : Integer.Sparse.eval row20250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20250, Integer.Sparse.eval_collectBalanced, rawRowCheck20250]

theorem rawRowCheck20251 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form10 = rawRow20251 := by decide +kernel

theorem rowCheck20251 : row20251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20251 := by decide +kernel

theorem rowEval20251 (x : Key → ℝ) : Integer.Sparse.eval row20251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20251, Integer.Sparse.eval_collectBalanced, rawRowCheck20251]

theorem rawRowCheck20252 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form10 = rawRow20252 := by decide +kernel

theorem rowCheck20252 : row20252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20252 := by decide +kernel

theorem rowEval20252 (x : Key → ℝ) : Integer.Sparse.eval row20252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20252, Integer.Sparse.eval_collectBalanced, rawRowCheck20252]

theorem rawRowCheck20253 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form10 = rawRow20253 := by decide +kernel

theorem rowCheck20253 : row20253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20253 := by decide +kernel

theorem rowEval20253 (x : Key → ℝ) : Integer.Sparse.eval row20253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20253, Integer.Sparse.eval_collectBalanced, rawRowCheck20253]

theorem rawRowCheck20254 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form10 = rawRow20254 := by decide +kernel

theorem rowCheck20254 : row20254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20254 := by decide +kernel

theorem rowEval20254 (x : Key → ℝ) : Integer.Sparse.eval row20254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20254, Integer.Sparse.eval_collectBalanced, rawRowCheck20254]

theorem rawRowCheck20255 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form10 = rawRow20255 := by decide +kernel

theorem rowCheck20255 : row20255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20255 := by decide +kernel

theorem rowEval20255 (x : Key → ℝ) : Integer.Sparse.eval row20255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20255, Integer.Sparse.eval_collectBalanced, rawRowCheck20255]

theorem rawRowCheck20256 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form10 = rawRow20256 := by decide +kernel

theorem rowCheck20256 : row20256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20256 := by decide +kernel

theorem rowEval20256 (x : Key → ℝ) : Integer.Sparse.eval row20256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20256, Integer.Sparse.eval_collectBalanced, rawRowCheck20256]

theorem rawRowCheck20257 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form10 = rawRow20257 := by decide +kernel

theorem rowCheck20257 : row20257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20257 := by decide +kernel

theorem rowEval20257 (x : Key → ℝ) : Integer.Sparse.eval row20257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20257, Integer.Sparse.eval_collectBalanced, rawRowCheck20257]

theorem rawRowCheck20258 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form10 = rawRow20258 := by decide +kernel

theorem rowCheck20258 : row20258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20258 := by decide +kernel

theorem rowEval20258 (x : Key → ℝ) : Integer.Sparse.eval row20258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20258, Integer.Sparse.eval_collectBalanced, rawRowCheck20258]

theorem rawRowCheck20259 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form10 = rawRow20259 := by decide +kernel

theorem rowCheck20259 : row20259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20259 := by decide +kernel

theorem rowEval20259 (x : Key → ℝ) : Integer.Sparse.eval row20259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20259, Integer.Sparse.eval_collectBalanced, rawRowCheck20259]

theorem rawRowCheck20260 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form10 = rawRow20260 := by decide +kernel

theorem rowCheck20260 : row20260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20260 := by decide +kernel

theorem rowEval20260 (x : Key → ℝ) : Integer.Sparse.eval row20260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20260, Integer.Sparse.eval_collectBalanced, rawRowCheck20260]

theorem rawRowCheck20261 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form10 = rawRow20261 := by decide +kernel

theorem rowCheck20261 : row20261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20261 := by decide +kernel

theorem rowEval20261 (x : Key → ℝ) : Integer.Sparse.eval row20261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20261, Integer.Sparse.eval_collectBalanced, rawRowCheck20261]

theorem rawRowCheck20262 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form10 = rawRow20262 := by decide +kernel

theorem rowCheck20262 : row20262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20262 := by decide +kernel

theorem rowEval20262 (x : Key → ℝ) : Integer.Sparse.eval row20262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20262, Integer.Sparse.eval_collectBalanced, rawRowCheck20262]

theorem rawRowCheck20263 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form10 = rawRow20263 := by decide +kernel

theorem rowCheck20263 : row20263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20263 := by decide +kernel

theorem rowEval20263 (x : Key → ℝ) : Integer.Sparse.eval row20263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20263, Integer.Sparse.eval_collectBalanced, rawRowCheck20263]

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

theorem entryCheck11_10 : entry11_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_10 k)) := by decide +kernel

theorem rowsSound11_10 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form10) x := by
  fin_cases k
  · exact rowEval20204 x
  · exact rowEval20205 x
  · exact rowEval20206 x
  · exact rowEval20207 x
  · exact rowEval20208 x
  · exact rowEval20209 x
  · exact rowEval20210 x
  · exact rowEval20211 x
  · exact rowEval20212 x
  · exact rowEval20213 x
  · exact rowEval20214 x
  · exact rowEval20215 x
  · exact rowEval20216 x
  · exact rowEval20217 x
  · exact rowEval20218 x
  · exact rowEval20219 x
  · exact rowEval20220 x
  · exact rowEval20221 x
  · exact rowEval20222 x
  · exact rowEval20223 x
  · exact rowEval20224 x
  · exact rowEval20225 x
  · exact rowEval20226 x
  · exact rowEval20227 x
  · exact rowEval20228 x
  · exact rowEval20229 x
  · exact rowEval20230 x
  · exact rowEval20231 x
  · exact rowEval20232 x
  · exact rowEval20233 x
  · exact rowEval20234 x
  · exact rowEval20235 x
  · exact rowEval20236 x
  · exact rowEval20237 x
  · exact rowEval20238 x
  · exact rowEval20239 x
  · exact rowEval20240 x
  · exact rowEval20241 x
  · exact rowEval20242 x
  · exact rowEval20243 x
  · exact rowEval20244 x
  · exact rowEval20245 x
  · exact rowEval20246 x
  · exact rowEval20247 x
  · exact rowEval20248 x
  · exact rowEval20249 x
  · exact rowEval20250 x
  · exact rowEval20251 x
  · exact rowEval20252 x
  · exact rowEval20253 x
  · exact rowEval20254 x
  · exact rowEval20255 x
  · exact rowEval20256 x
  · exact rowEval20257 x
  · exact rowEval20258 x
  · exact rowEval20259 x
  · exact rowEval20260 x
  · exact rowEval20261 x
  · exact rowEval20262 x
  · exact rowEval20263 x

theorem entryEval11_10_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_10 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form10 B := by
  rw [entryCheck11_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_10]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_10_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_10_e_oai
