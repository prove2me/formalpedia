-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnitBase.algebraMap_cO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:00.485661+00:00
-- url     : https://prove2.me/submissions/327178f6-8c5e-40a1-a139-be22c5bf0f94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.UnitBase
theorem _root_.solution (K : UQ) (x : K.O) : algebraMap K.O K.E (cO K x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm
end GlobalTheory.UnitLemma.UnitBase
