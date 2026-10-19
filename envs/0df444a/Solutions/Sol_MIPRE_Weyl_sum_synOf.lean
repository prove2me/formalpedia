-- Prove2me | solution 1 for MIPRE.Weyl.sum_synOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:42:16.96043+00:00
-- url     : https://prove2.me/submissions/c5422ddf-9267-44da-94d9-df92ab0f96b8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Weyl.lean (solution of MIPRE.Weyl.sum_synOf);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem _root_.solution {C D : Type*} [Fintype C] [DecidableEq C] [DecidableEq D]
    (w : (n → F) → Matrix (n → F) (n → F) ℂ) (φ : (n → F) → C) (g : C → D) (c : D) :
    ∑ o ∈ univ.filter fun o => g o = c, synOf w φ o = synOf w (fun e => g (φ e)) c := by
  classical
  have hmaps : ∀ e ∈ univ.filter fun e => g (φ e) = c, φ e ∈ univ.filter fun o => g o = c :=
    fun e he => Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp he).2⟩
  have hfil : ∀ o ∈ univ.filter fun o => g o = c,
      (univ.filter fun e => g (φ e) = c).filter (fun e => φ e = o)
        = univ.filter fun e => φ e = o := by
    intro o ho
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun e _ => ?_
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [h]
    exact (Finset.mem_filter.mp ho).2
  rw [show synOf w (fun e => g (φ e)) c
      = ∑ e ∈ univ.filter fun e => g (φ e) = c, proj w e from rfl,
    ← Finset.sum_fiberwise_of_maps_to hmaps (proj w)]
  exact Finset.sum_congr rfl fun o ho => by rw [synOf, ← hfil o ho]
end MIPRE.Weyl
