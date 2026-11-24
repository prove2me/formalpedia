-- Prove2me | solution 1 for GlobalTheory.HullClasses.sigma_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:37:16.854612+00:00
-- url     : https://prove2.me/submissions/4b285761-7198-409b-8e85-95db89a3aa42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.HullClasses
theorem _root_.solution (c cb : K.O) (h : K.c (algebraMap K.O K.E c) = algebraMap K.O K.E cb) :
    B.σ (algebraMap K.O B.A c) = algebraMap K.O B.A cb := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, h, ← IsScalarTower.algebraMap_apply]
end GlobalTheory.HullClasses
