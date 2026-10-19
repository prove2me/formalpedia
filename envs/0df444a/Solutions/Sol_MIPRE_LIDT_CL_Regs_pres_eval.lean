-- Prove2me | solution 1 for MIPRE.LIDT.CL.Regs.pres_eval
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:15.684434+00:00
-- url     : https://prove2.me/submissions/0075bd5e-e701-4849-b5fe-45e48e2b6d58

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/PresentationEmbed.lean (solution of MIPRE.LIDT.CL.Regs.pres_eval);
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
import Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_apply_of_mem {S : Finset ι} {i : ι} (h : i ∈ S) (x : ι → F) :
    proj S x i = x i := by simp [h]
end
end MIPRE.CL

namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_apply_of_not_mem {S : Finset ι} {i : ι} (h : i ∉ S) (x : ι → F) :
    proj S x i = 0 := by simp [h]
end
end MIPRE.CL

namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_eq_self_iff {S : Finset ι} {x : ι → F} : proj S x = x ↔ ∀ i, i ∉ S → x i = 0 := by
  constructor
  · intro h i hi
    rw [← congrFun h i, proj_apply_of_not_mem hi]
  · intro h
    ext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, h i hi]
end
end MIPRE.CL

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
theorem pt_mem_finalSet (i : Fin n) : R.pt i ∈ R.finalSet := by
  simp only [finalSet, coordSet, dirSet, mem_sdiff, mem_univ, mem_singleton, mem_image,
    true_and, not_exists]
  exact ⟨R.pt_ne_coord i, fun j h => R.pt_ne_dir i j h.symm⟩
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
omit [Fintype ι] in
theorem dir_mem_dirSet (j : Fin n) : R.dir j ∈ R.dirSet := mem_image_of_mem _ (mem_univ j)
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
theorem proj_finalSet_putPt (w : Point F n) : proj R.finalSet (R.putPt w) = R.putPt w := by
  refine proj_eq_self_iff.mpr fun c hc =>
    R.putPt_of_not (fun i h => hc (by subst h; exact R.pt_mem_finalSet i)) w
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
omit [Fintype ι] in
theorem proj_dirSet_putDir (w : Point F n) : proj R.dirSet (R.putDir w) = R.putDir w := by
  refine proj_eq_self_iff.mpr fun c hc =>
    R.putDir_of_not (fun j h => hc (by subst h; exact R.dir_mem_dirSet j)) w
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
theorem ptOf_proj_finalSet (x : ι → F) : R.ptOf (proj R.finalSet x) = R.ptOf x := by
  funext i; simp [ptOf, proj_apply_of_mem (R.pt_mem_finalSet i)]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
omit [Fintype ι] in
theorem dirOf_proj_dirSet (x : ι → F) : R.dirOf (proj R.dirSet x) = R.dirOf x := by
  funext j; simp [dirOf, proj_apply_of_mem (R.dir_mem_dirSet j)]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
theorem ptLin_apply (A : Point F n →ₗ[F] Point F n) (x : ι → F) :
    R.ptLin A x = R.putPt (A (R.ptOf x)) := by
  simp only [ptLin, RegLinear.ofLinearMap_apply, LinearMap.comp_apply]
  rw [show (LinearMap.funLeft F F R.pt) (proj R.finalSet x) = R.ptOf (proj R.finalSet x) from rfl,
    R.ptOf_proj_finalSet, R.proj_finalSet_putPt]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
omit [Fintype ι] in
theorem dirLin_apply (i : Fin n) (x : ι → F) :
    R.dirLin i x = R.putDir (zeroBelow i (R.dirOf x)) := by
  simp only [dirLin, RegLinear.ofLinearMap_apply, LinearMap.comp_apply]
  rw [show (LinearMap.funLeft F F R.dir) (proj R.dirSet x) = R.dirOf (proj R.dirSet x) from rfl,
    R.dirOf_proj_dirSet]
  exact R.proj_dirSet_putDir _
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
omit [DecidableEq ι] [Fintype ι] [NeZero n] in
theorem not_mem_coordSet_pt (i : Fin n) : R.pt i ∉ R.coordSet := by
  simp [coordSet, R.pt_ne_coord i]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
omit [Fintype ι] [NeZero n] in
theorem not_mem_dirSet_pt (i : Fin n) : R.pt i ∉ R.dirSet := by
  simp only [dirSet, mem_image, mem_univ, true_and, not_exists]
  exact fun j h => R.pt_ne_dir i j h.symm
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
omit [DecidableEq ι] [Fintype ι] [NeZero n] in
theorem not_mem_coordSet_dir (j : Fin n) : R.dir j ∉ R.coordSet := by
  simp [coordSet, R.dir_ne_coord j]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
omit [DecidableEq ι] [Fintype ι] [NeZero n] in
theorem coord_mem_coordSet : R.coord ∈ R.coordSet := mem_singleton_self _
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem proj_coordSet (x : ι → F) : proj R.coordSet x = Pi.single R.coord (x R.coord) := by
  funext i
  by_cases h : i = R.coord
  · subst h
    simp [proj_apply_of_mem R.coord_mem_coordSet]
  · rw [proj_apply_of_not_mem (by simpa [coordSet] using h), Pi.single_eq_of_ne h]
end
end MIPRE.LIDT.CL.Regs

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.CL.Regs
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem _root_.solution (t : Ty) (x : ι → F) :
    (R.pres S t).eval x = R.embedQ S ((R.sampleOf S t x).question hn t) := by
  have hpt : ∀ i, (proj R.dirSetᶜ (proj R.coordSetᶜ x)) (R.pt i) = x (R.pt i) := fun i => by
    rw [proj_apply_of_mem (by simpa using R.not_mem_dirSet_pt i),
      proj_apply_of_mem (by simpa using R.not_mem_coordSet_pt i)]
  have hptOf : R.ptOf (proj R.dirSetᶜ (proj R.coordSetᶜ x)) = R.ptOf x := funext hpt
  have hdirOf : R.dirOf (proj R.coordSetᶜ x) = R.dirOf x := by
    funext j
    simp only [dirOf]
    rw [proj_apply_of_mem (by simpa using R.not_mem_coordSet_dir j)]
  have hcoord : (proj R.coordSet x) R.coord = x R.coord := proj_apply_of_mem R.coord_mem_coordSet x
  cases t with
  | point =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.zero_apply, zero_add, add_zero, ptLin_apply, LinearMap.id_apply, hptOf]
    rfl
  | aline =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.zero_apply, RegLinear.id_apply, zero_add, add_zero, ptLin_apply, hptOf, hcoord]
    simp only [sampleOf, Sample.question, embedQ, rep, S.chi_π, Equiv.symm_apply_apply,
      proj_coordSet]
  | dline =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.id_apply, add_zero, ptLin_apply, dirLin_apply, hptOf, hcoord, hdirOf]
    simp only [dirOf_putDir, sampleOf, Sample.question, embedQ, rep, S.chi_π,
      Equiv.symm_apply_apply, proj_coordSet]
    abel
end MIPRE.LIDT.CL.Regs
