-- Prove2me | solution 1 for MIPRE.LIDT.CL.accepts_honest
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:04.937025+00:00
-- url     : https://prove2.me/submissions/7f514c5f-00ec-4d4a-a929-7f5c6a9d266c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/CLHonest.lean (solution of MIPRE.LIDT.CL.accepts_honest);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest
import Theorems.Thm_MIPRE_LowDegree_natDegree_lineRestrict_le
import Theorems.Thm_MIPRE_LowDegree_natDegree_lineRestrict_single_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **A point differs from its canonical representative by an element of `S`.** For a line ---
`S = span {w}` --- this is the statement that the base point the seeded test reports lies on the
line through the sampled point, which is what lets a line answer be evaluated at the point. -/
theorem sub_canonLin_mem (S : Submodule F (Fin n → F)) (x : Fin n → F) :
    x - canonLin S x ∈ S :=
  Submodule.sub_projection_mem _ x
end
end MIPRE.CL

namespace MIPRE.LowDegree
noncomputable section
open Finset
variable {F : Type*} [Field F] {m : ℕ}
/-- **Evaluating the restriction is evaluating along the line.** -/
theorem eval_lineRestrict (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) (t : F) :
    (lineRestrict u₀ w p).eval t = MvPolynomial.eval (u₀ + t • w) p := by
  have key : ((Polynomial.aeval t).comp (MvPolynomial.aeval
      (fun i => Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i))) :
        MvPolynomial (Fin m) F →ₐ[F] F) = MvPolynomial.aeval (u₀ + t • w) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp
    ring
  simpa [lineRestrict] using congrArg (fun φ => φ p) key
end
end MIPRE.LowDegree

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
/-- A point lies on the line through its canonical base point. -/
theorem exists_eq_rep_add (w u : Point F m) : ∃ t : F, u = rep w u + t • w := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_canonLin_mem (Submodule.span F {w}) u)
  exact ⟨t, by rw [rep, ht]; abel⟩
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
/-- The parameter of a point of a line is its parameter, when the line is not a point. -/
theorem add_lineParam_smul [DecidableEq F] (u₀ w : Point F m) (t : F) :
    u₀ + lineParam u₀ w (u₀ + t • w) • w = u₀ + t • w := by
  unfold lineParam
  split_ifs with h
  · have hw := Fin.find_spec h
    congr 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    field_simp
  · simp only [not_exists, not_not] at h
    have : w = 0 := funext h
    simp [this]
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
theorem eval_lineCo {n : ℕ} {u₀ w : Point F m} {p : MvPolynomial (Fin m) F}
    (h : (lineRestrict u₀ w p).natDegree ≤ n) (t : F) :
    (lineCo n u₀ w p).eval t = MvPolynomial.eval (u₀ + t • w) p := by
  rw [LinePoly.eval, ← eval_lineRestrict u₀ w p t]
  change ∑ i : Fin (n + 1), (lineRestrict u₀ w p).coeff i * t ^ (i : ℕ) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (lineRestrict u₀ w p).coeff i * t ^ i) (n + 1)]
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h) t).symm
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
/-- Individual degree at most `d` in each of `m` variables is total degree at most `m d`. -/
theorem totalDegree_le_of_degreeOf_le {d : ℕ} {p : MvPolynomial (Fin m) F}
    (h : ∀ i, p.degreeOf i ≤ d) : p.totalDegree ≤ m * d := by
  classical
  refine Finset.sup_le fun s hs => ?_
  calc (s.sum fun _ e => e) = ∑ i ∈ s.support, s i := rfl
    _ ≤ ∑ i : Fin m, s i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ _i : Fin m, d :=
        Finset.sum_le_sum fun i _ => (MvPolynomial.monomial_le_degreeOf i hs).trans (h i)
    _ = m * d := by simp
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
omit [DecidableEq F] in
theorem fmtOk_honest (G : Fin ldc → MvPolynomial (Fin m) F) (q : Question F m) :
    q.fmtOk (honest hm (d := d) G q) = true := by
  cases q <;> rfl
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}
omit [NeZero m] in
/-- A line answer against a point on the line: the honest answers agree. -/
theorem lineVsPoint_honest {n : ℕ} {G : Fin ldc → MvPolynomial (Fin m) F} {u₀ w x : Point F m}
    (hx : ∃ t : F, x = u₀ + t • w) (hG : ∀ j, (lineRestrict u₀ w (G j)).natDegree ≤ n) :
    lineVsPoint u₀ w x (fun j => lineCo n u₀ w (G j)) (fun j => MvPolynomial.eval x (G j))
      = true := by
  obtain ⟨t, rfl⟩ := hx
  simp only [lineVsPoint, decide_eq_true_eq]
  refine ⟨⟨t, rfl⟩, fun j => ?_⟩
  rw [eval_lineCo (hG j), add_lineParam_smul]
end
end MIPRE.LIDT.CL

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.CL
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}
theorem _root_.solution {G : Fin ldc → MvPolynomial (Fin m) F}
    (hG : ∀ j i, (G j).degreeOf i ≤ d) (sm : Sample F m) (τ τ' : Ty) :
    accepts hm (sm.question hm τ) (sm.question hm τ')
      (honest hm (d := d) G (sm.question hm τ)) (honest hm (d := d) G (sm.question hm τ'))
      = true := by
  have hA : ∀ j, (lineRestrict (rep (Pi.single (chi hm sm.s) 1) sm.u)
      (Pi.single (chi hm sm.s) 1) (G j)).natDegree ≤ d := fun j =>
    (natDegree_lineRestrict_single_le _ _ _).trans (hG j _)
  have hD : ∀ (u₀ v : Point F m) j, (lineRestrict u₀ v (G j)).natDegree ≤ m * d := fun u₀ v j =>
    (natDegree_lineRestrict_le _ _ _).trans (totalDegree_le_of_degreeOf_le (hG j))
  have hlA := exists_eq_rep_add (Pi.single (chi hm sm.s) 1) sm.u
  have hlD := exists_eq_rep_add (zeroBelow (chi hm sm.s) sm.v) sm.u
  simp only [accepts, fmtOk_honest, Bool.true_and]
  cases τ <;> cases τ' <;>
    simp only [Sample.question, honest, subtests, decide_true]
  · exact lineVsPoint_honest hlA hA
  · exact lineVsPoint_honest hlD (hD _ _)
  · exact lineVsPoint_honest hlA hA
  · exact lineVsPoint_honest hlD (hD _ _)
end MIPRE.LIDT.CL
