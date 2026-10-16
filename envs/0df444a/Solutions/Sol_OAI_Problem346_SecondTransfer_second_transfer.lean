-- Prove2me | solution 1 for OAI.Problem346.SecondTransfer.second_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:17:03.766528+00:00
-- url     : https://prove2.me/submissions/239fff61-aa8f-4c4a-8d82-ea974ef6331f

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SecondTransfer.lean:L56-L77
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.SecondTransfer.second_transfer. The node keeps its source
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
import Theorems.Thm_OAI_Problem346_SecondTransfer_polynomial_step
import Theorems.Thm_OAI_Problem346_zero_of_upward_grid

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

/-- With basis coordinates, evaluation is literal evaluation on the chosen vector blocks. -/
theorem eval_multilinearPolynomial_basis
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : Module.Basis κ ℂ V) (block : ι → β) (v : β → V) :
    MvPolynomial.eval (fun z : β × κ => e.repr (v z.1) z.2)
      (multilinearPolynomial L e block) = L (fun i => v (block i)) := by
  rw [eval_multilinearPolynomial]
  simp only [e.sum_repr]

/-- Pointwise vanishing on vector blocks implies the corresponding polynomial identity. -/
theorem multilinearPolynomial_eq_zero
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β)
    (h : ∀ v : β → V, L (fun i => v (block i)) = 0) :
    multilinearPolynomial L e block = 0 := by
  apply MvPolynomial.funext
  intro z
  rw [eval_multilinearPolynomial, map_zero]
  exact h (fun j => ∑ k, z (j, k) • e k)

/-- Conversely, a polynomial identity gives the vector-valued identity by basis evaluation. -/
theorem multilinearPolynomial_eq_zero_iff
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : Module.Basis κ ℂ V) (block : ι → β) :
    multilinearPolynomial L e block = 0 ↔
      ∀ v : β → V, L (fun i => v (block i)) = 0 := by
  constructor
  · intro h v
    rw [← eval_multilinearPolynomial_basis L e block v, h, map_zero]
  · exact multilinearPolynomial_eq_zero L e block

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.MonomialCut ----
namespace OAI

noncomputable section

namespace Problem346

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Splitting a list of equal factors at a cutoff is graded multiplication of two pure powers. -/
theorem symMonomial_cut (r m : ℕ) (x y : V) :
    symMonomial (r+m) V (fun j => if j.val < r then x else y) =
      symPowMul r m (symMonomial r V (fun _ => x))
        (symMonomial m V (fun _ => y)) := by
  rw [symPowMul_symMonomial]
  congr 1
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp
  · simp

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SecondEndpoints ----
namespace OAI

noncomputable section

namespace Problem346.SecondTransfer

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- At the terminal count vector, the first `r` factors in every moving row
are the common vector. This is precisely the product form in the induction hypothesis. -/
theorem terminal_eval (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (v : Block r → V) :
    flattenedSymmetricForm T (fun p => v (label (fun _ : Fin r => r) p)) =
      T (Fin.cons (symMonomial (r+m) V (fun _ => v (some 0)))
        (fun i => symPowMul r m (symMonomial r V (fun _ => v none))
          (symMonomial m V (fun _ => v (some i.succ))))) := by
  rw [flattenedSymmetricForm_apply]
  apply congrArg T
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [label_zero_row, Fin.cons_zero]
  · simp only [label_succ_row, Fin.cons_succ, apply_ite]
    exact symMonomial_cut r m (v none) (v (some i.succ))

/-- The known common-power vanishing implies the terminal labelled expression vanishes. -/
theorem terminal_eval_zero (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0)
    (v : Block r → V) :
    flattenedSymmetricForm T (fun p => v (label (fun _ : Fin r => r) p)) = 0 := by
  rw [terminal_eval]
  exact h (v none) (v (some 0)) (fun i => symMonomial m V (fun _ => v (some i.succ)))

/-- The terminal labelled polynomial is zero, before any degree-shift cancellation. -/
theorem terminal_polynomial_zero {κ : Type*} [Fintype κ] (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0) :
    multilinearPolynomial (flattenedSymmetricForm T) e (label (fun _ : Fin r => r)) = 0 := by
  apply multilinearPolynomial_eq_zero
  exact terminal_eval_zero r m T h

/-- After cancelling all shifts, the initial polynomial identity evaluates to
vanishing on independent pure powers in every slot. -/
theorem independent_powers_zero_of_initial_polynomial_zero
    {κ : Type*} [Fintype κ] {r b : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V) (e : Module.Basis κ ℂ V)
    (h : multilinearPolynomial (flattenedSymmetricForm T) e
      (label (fun _ : Fin r => 0)) = 0) (v : Fin (r+1) → V) :
    T (fun i => symMonomial b V (fun _ => v i)) = 0 := by
  have hv := (multilinearPolynomial_eq_zero_iff (flattenedSymmetricForm T) e
    (label (fun _ : Fin r => 0))).mp h (fun o => o.elim 0 v)
  simpa only [flattenedSymmetricForm_apply, label_zero, Option.elim_some] using hv

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

/-- The second differential transfer: remove the common degree-`r` power from
all `r` moving arguments. Count-vector induction allows the shifts in any order. -/
theorem second_transfer [FiniteDimensional ℂ V] (r m : ℕ)
    (hb : r * (r+1) ≤ r+m)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0) :
    ∀ v : Fin (r+1) → V,
      T (fun i => symMonomial (r+m) V (fun _ => v i)) = 0 := by
  classical
  let e := Module.finBasis ℂ V
  let P (k : Fin r → ℕ) :=
    multilinearPolynomial (flattenedSymmetricForm T) e (label k)
  have hend : P (fun _ => r) = 0 := terminal_polynomial_zero r m T e h
  have hzero : P (fun _ => 0) = 0 := by
    apply zero_of_upward_grid r P hend
    · intro k hk i hi hnext
      exact polynomial_step T e hb k hk i hi hnext
    · intro i
      exact Nat.zero_le r
  exact independent_powers_zero_of_initial_polynomial_zero T e hzero

end Problem346.SecondTransfer

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346 OAI.Problem346.SecondTransfer
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem346.SecondTransfer.second_transfer.{u} := @_root_.OAI.Problem346.SecondTransfer.second_transfer.{u}
