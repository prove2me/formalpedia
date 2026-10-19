-- Prove2me | solution 1 for MIPRE.obs2_commutator_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:22:25.020683+00:00
-- url     : https://prove2.me/submissions/3fb0aed4-5f8b-4c4d-9bb9-d13dbe3038a3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (solution of MIPRE.obs2_commutator_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Theorems.Thm_MIPRE_POVM_sum_val

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
theorem _root_.solution {d : Type*} [Fintype d] [DecidableEq d]
    (A : POVM (ZMod 2) d) (Cm : POVM (ZMod 2) d) :
    obs2 A * obs2 Cm - obs2 Cm * obs2 A
      = (4 : ℂ) • (((A.mats 1).val) * ((Cm.mats 1).val)
        - ((Cm.mats 1).val) * ((A.mats 1).val)) := by
  have hA : ((A.mats 0).val) = 1 - ((A.mats 1).val) := by
    have h := POVM.sum_val A
    rw [show (univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
    linear_combination (norm := module) h
  have hC : ((Cm.mats 0).val) = 1 - ((Cm.mats 1).val) := by
    have h := POVM.sum_val Cm
    rw [show (univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
    linear_combination (norm := module) h
  rw [obs2, obs2, hA, hC]
  noncomm_ring
  module
end MIPRE
