-- Prove2me | solution 1 for OAI.Problem346.SecondTransfer.polynomial_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:15:15.500956+00:00
-- url     : https://prove2.me/submissions/37f74f40-ee84-4bda-93fb-7a51f2660264

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SecondTransfer.lean:L31-L54
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.SecondTransfer.polynomial_step. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondSwap
import Theorems.Thm_OAI_Problem346_SecondTransfer_source_occurrences
import Theorems.Thm_OAI_Problem346_SecondTransfer_update_label_eq_progress_rowSwap
import Theorems.Thm_OAI_Problem346_multilinearPolynomial_eq_zero_of_replacements

-- ---- from OAI.RepresentationTheory.FoulkesHowe.MonomialMultilinear ----
namespace OAI

noncomputable section

open scoped BigOperators

universe u v

namespace Problem346

theorem symMonomial_permute (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (σ : Equiv.Perm (Fin n)) (x : Fin n → V) :
    symMonomial n V (fun i => x (σ i)) = symMonomial n V x := by
  apply Subtype.ext
  exact Equiv.prod_comp σ (fun i => SymmetricAlgebra.ι ℂ V (x i))

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FlattenedForm ----
namespace OAI

noncomputable section

namespace Problem346

universe u

variable {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Independent permutations within the rows preserve the flattened form. -/
theorem flattenedSymmetricForm_inner_permute
    (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T (fun p => v (p.1, σ p.1 p.2)) =
      flattenedSymmetricForm T v := by
  apply congrArg T
  funext i
  exact symMonomial_permute b V (σ i) (fun j => v (i, j))

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.MultilinearPolynomial ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

universe uι uκ uβ uV
variable {ι : Type uι} {κ : Type uκ} {β : Type uβ} {V : Type uV}
variable [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℂ V]

/-- Evaluation of the multilinear polynomial on arbitrary coordinate assignments. -/
theorem eval_multilinearPolynomial
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β) (z : β × κ → ℂ) :
    MvPolynomial.eval z (multilinearPolynomial L e block) =
      L (fun i => ∑ k, z (block i, k) • e k) := by
  classical
  simp only [multilinearPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    map_prod, MvPolynomial.eval_X]
  rw [L.map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [L.map_smul_univ]
  simp only [smul_eq_mul]
  exact mul_comm _ _

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SecondCounts ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SecondTransfer

/-- A source occurrence lies in exactly one nonzero row and beyond its
already-transferred prefix. -/
theorem label_eq_source_iff {r b : ℕ} (k : Fin r → ℕ)
    (i : Fin r) (p : Fin (r+1) × Fin b) :
    label k p = some i.succ ↔ p.1 = i.succ ∧ k i ≤ p.2.val := by
  rcases p with ⟨l,j⟩
  refine Fin.cases ?_ (fun l => ?_) l
  · simp [Ne.symm (Fin.succ_ne_zero i)]
  · by_cases h : l = i
    · subst l
      simp [not_lt]
    · simp [label_succ_row, Fin.succ_inj, h]

private theorem sum_fin_ite_lt (b k : ℕ) (hk : k ≤ b) :
    (∑ j : Fin b, if j.val < k then 1 else 0) = k := by
  classical
  by_cases h : k < b
  · let c : Fin b := ⟨k,h⟩
    have hs : Finset.univ.filter (fun j : Fin b => j.val < k) = Finset.Iio c := by
      ext j
      simp [c, Fin.lt_def]
    rw [← Finset.card_filter, hs, Fin.card_Iio]
  · have hkb : k = b := by omega
    subst k
    simp

/-- Number of occurrences of the shared destination vector. -/
theorem destination_occurrences {r b : ℕ} (k : Fin r → ℕ)
    (hk : ∀ i, k i ≤ b) :
    (∑ p : Fin (r+1) × Fin b, if label k p = none then 1 else 0) = ∑ i, k i := by
  classical
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [label_zero_row, reduceCtorEq, ite_false, Finset.sum_const_zero, zero_add,
    label_succ_row]
  apply Finset.sum_congr rfl
  intro i hi
  convert sum_fin_ite_lt b (k i) (hk i) using 1
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp_all

/-- At every unfinished row, the quadratic threshold makes the source degree
strictly larger than the accumulated shared-destination degree. -/
theorem source_degree_gt_destination {r b : ℕ} (k : Fin r → ℕ)
    (hb : r * (r+1) ≤ b) (hk : ∀ j, k j ≤ r)
    (i : Fin r) (hi : k i < r) :
    (∑ j, k j) < b - k i := by
  have hsum : (∑ j, k j) ≤ r*r := by
    calc
      _ ≤ ∑ _ : Fin r, r := Finset.sum_le_sum (fun j _ => hk j)
      _ = r*r := by simp
  have hquad : r*r+r ≤ b := by nlinarith
  omega

/-- The actual occurrence counts satisfy the positive-weight hypothesis
used to cancel a shift at any unfinished row. -/
theorem destination_occurrences_lt_source {r b : ℕ} (k : Fin r → ℕ)
    (hb : r * (r+1) ≤ b) (hk : ∀ j, k j ≤ r)
    (i : Fin r) (hi : k i < r) :
    (∑ p : Fin (r+1) × Fin b, if label k p = none then 1 else 0) <
      ∑ p : Fin (r+1) × Fin b, if label k p = some i.succ then 1 else 0 := by
  have hrb : r ≤ b := by nlinarith
  have hkb : ∀ j, k j ≤ b := fun j => (hk j).trans hrb
  rw [destination_occurrences k hkb, source_occurrences k hkb]
  exact source_degree_gt_destination k hb hk i hi

end Problem346.SecondTransfer

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SecondSwap ----
namespace OAI

noncomputable section
namespace Problem346.SecondTransfer

/-- Any expression invariant under permutations of factors within each row takes the
same value on a derivative label update and the progressed prefix labels. -/
theorem invariant_update_label_eq_progress
    {r b : ℕ} {A : Type*}
    (F : ((Fin (r+1) × Fin b) → Block r) → A)
    (hF : ∀ (l : (Fin (r+1) × Fin b) → Block r)
      (σ : Fin (r+1) → Equiv.Perm (Fin b)),
      F (fun p => l (p.1, σ p.1 p.2)) = F l)
    (k : Fin r → ℕ) (i : Fin r) (hi : k i < b)
    (j : Fin b) (hj : k i ≤ j.val) :
    F (Function.update (label k) (i.succ,j) none) =
      F (label (Function.update k i (k i+1))) := by
  have heq : Function.update (label k) (i.succ,j) none =
      fun p => label (Function.update k i (k i+1))
        (p.1, rowFactorSwap i j ⟨k i, hi⟩ p.1 p.2) := by
    funext p
    exact update_label_eq_progress_rowSwap k i hi j hj p
  rw [heq]
  exact hF _ _

end Problem346.SecondTransfer

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SecondTransfer ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SecondTransfer

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Polynomial encoding preserves the independent factor permutations of each row. -/
theorem polynomial_row_permute {κ : Type*} [Fintype κ] {r b : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V) (e : κ → V)
    (l : Fin (r+1) × Fin b → Block r)
    (σ : Fin (r+1) → Equiv.Perm (Fin b)) :
    multilinearPolynomial (flattenedSymmetricForm T) e
        (fun p => l (p.1, σ p.1 p.2)) =
      multilinearPolynomial (flattenedSymmetricForm T) e l := by
  apply MvPolynomial.funext
  intro z
  simp only [eval_multilinearPolynomial]
  exact flattenedSymmetricForm_inner_permute T σ
    (fun p => ∑ j : κ, z (l p,j) • e j)

/-- A single unfinished row can be recovered from its one-step progressed state. -/
theorem polynomial_step {κ : Type*} [Fintype κ] {r b : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V) (e : κ → V)
    (hb : r * (r+1) ≤ b) (k : Fin r → ℕ) (hk : ∀ j, k j ≤ r)
    (i : Fin r) (hi : k i < r)
    (hnext : multilinearPolynomial (flattenedSymmetricForm T) e
      (label (Function.update k i (k i+1))) = 0) :
    multilinearPolynomial (flattenedSymmetricForm T) e (label k) = 0 := by
  classical
  apply multilinearPolynomial_eq_zero_of_replacements
    (flattenedSymmetricForm T) e (label k) (some i.succ) none (by simp)
  · have hd := destination_occurrences_lt_source (b := b) k hb hk i hi
    simpa only [Finset.card_filter] using hd
  · rintro ⟨row,j⟩ hp
    obtain ⟨hrow,hj⟩ := (label_eq_source_iff k i (row,j)).mp hp
    change row = i.succ at hrow
    change k i ≤ j.val at hj
    subst row
    have hrb : r ≤ b := by nlinarith
    have hki : k i < b := lt_of_lt_of_le hi hrb
    have heq := invariant_update_label_eq_progress
      (fun l => multilinearPolynomial (flattenedSymmetricForm T) e l)
      (polynomial_row_permute T e) k i hki j hj
    exact heq.trans hnext

end Problem346.SecondTransfer

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346 OAI.Problem346.SecondTransfer
open scoped BigOperators


theorem solution.{u,u_1} : type_of% @_root_.OAI.Problem346.SecondTransfer.polynomial_step.{u,u_1} := @_root_.OAI.Problem346.SecondTransfer.polynomial_step.{u,u_1}
