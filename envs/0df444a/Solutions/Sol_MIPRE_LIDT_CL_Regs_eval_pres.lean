-- Prove2me | solution 1 for MIPRE.LIDT.CL.Regs.eval_pres
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:16.299988+00:00
-- url     : https://prove2.me/submissions/e3dbaa3c-a4c6-4b8c-8221-4472f114a856

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/PresentationQueries.lean (solution of MIPRE.LIDT.CL.Regs.eval_pres);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries

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
theorem dirSet_subset : R.dirSet ⊆ univ \ R.coordSet := by
  intro c hc
  obtain ⟨j, -, rfl⟩ := mem_image.mp hc
  simp [coordSet, R.dir_ne_coord j]
end
end MIPRE.LIDT.CL.Regs

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
theorem coord_mem_coordSet : R.coord ∈ R.coordSet := mem_singleton_self _
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] in
theorem secondLin_apply (t : Ty) (s : F) (x : ι → F) :
    R.secondLin S t s x = if t = .dline then R.putDir (zeroBelow (S.χ s) (R.dirOf x)) else 0 := by
  cases t
  · rfl
  · rfl
  · exact R.dirLin_apply _ x
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem finalLin_apply (t : Ty) (s : F) (v : Point F n) (x : ι → F) :
    R.finalLin S t s v x = R.putPt (ptMap S t s v (R.ptOf x)) := by
  cases t <;> exact R.ptLin_apply _ x
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] in
theorem coord_seedLin (t : Ty) (x : ι → F) (s : F) (h : t ≠ .point → x R.coord = s) :
    R.secondLin S t ((R.seedLin t x) R.coord) = R.secondLin S t s := by
  cases t with
  | point => rfl
  | aline => rfl
  | dline =>
    change R.secondLin S _ ((proj R.coordSet x) R.coord) = _
    rw [proj_apply_of_mem R.coord_mem_coordSet, h (by simp)]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [NeZero n] in
theorem dirSet_subset_compl : R.dirSet ⊆ R.coordSetᶜ := fun c hc => by
  have := R.dirSet_subset hc
  simp only [mem_sdiff, mem_univ, true_and] at this
  exact mem_compl.mpr this
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [NeZero n] in
theorem finalSet_subset_compl : R.finalSet ⊆ R.dirSetᶜ ∩ R.coordSetᶜ := fun c hc => by
  simp only [finalSet, mem_sdiff, mem_univ, true_and] at hc
  exact mem_inter.mpr ⟨mem_compl.mpr hc.2, mem_compl.mpr hc.1⟩
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] in
theorem dirOf_secondLin (t : Ty) (s : F) (x : ι → F) :
    R.dirOf (R.secondLin S t s x) = if t = .dline then zeroBelow (S.χ s) (R.dirOf x) else 0 := by
  rw [secondLin_apply]
  split_ifs
  · exact R.dirOf_putDir _
  · rfl
end
end MIPRE.LIDT.CL.Regs

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.CL.Regs
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem _root_.solution (t : Ty) (x : ι → F) :
    (R.pres S t).eval x = R.seedLin t x + R.secondLin S t (x R.coord) x +
      R.putPt (ptMap S t (x R.coord)
        (if t = .dline then zeroBelow (S.χ (x R.coord)) (R.dirOf x) else 0) (R.ptOf x)) := by
  simp only [pres, eval_cons, eval_zero, add_zero]
  rw [R.coord_seedLin S t x (x R.coord) (fun _ => rfl),
    (R.secondLin S t (x R.coord)).apply_proj_of_subset R.dirSet_subset_compl, add_assoc]
  congr 2
  have hsd : proj R.dirSetᶜ (proj R.coordSetᶜ x) = proj (R.dirSetᶜ ∩ R.coordSetᶜ) x := by
    rw [proj_proj]
  rw [hsd, (R.finalLin S t _ _).apply_proj_of_subset R.finalSet_subset_compl, finalLin_apply]
  have h1 : (proj R.coordSet x) R.coord = x R.coord := proj_apply_of_mem R.coord_mem_coordSet x
  cases t with
  | point => rfl
  | aline =>
    change R.putPt (ptMap S .aline ((proj R.coordSet x) R.coord) _ _) = _
    rw [h1]
    rfl
  | dline =>
    change R.putPt (ptMap S .dline ((proj R.coordSet x) R.coord) _ _) = _
    rw [h1, dirOf_secondLin]
end MIPRE.LIDT.CL.Regs
