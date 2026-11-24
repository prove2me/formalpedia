-- Prove2me | solution 1 for GlobalTheory.UnitLemma.InertUnit.charpoly_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:59:10.505043+00:00
-- url     : https://prove2.me/submissions/84d09e99-bb2d-4bb5-8789-2d63c11968a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfReciprocalInvAlgWithPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma
noncomputable section
open GlobalTheory.UnitLemma.InertUnit
variable {K : UQ} {P : K.E[X]}
namespace GlobalTheory.UnitLemma.InertUnit
theorem _root_.solution (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (invAlg hP hr).P = P := by
  haveI : Module.Finite K.E (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis hP.ne_zero)
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen,
    AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one] at h
  exact h
end GlobalTheory.UnitLemma.InertUnit
