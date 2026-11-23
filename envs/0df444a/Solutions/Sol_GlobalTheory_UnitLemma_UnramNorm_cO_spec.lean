-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnramNorm.cO_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:39.947812+00:00
-- url     : https://prove2.me/submissions/5be4704c-2d13-473e-a679-a5e7539d2f88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnramNorm
open IsLocalRing Polynomial
variable (K : UQ)
open IsLocalRing Polynomial
variable (K : _root_.GlobalTheory.UnitLemma.UQ)
namespace GlobalTheory.UnitLemma.UnramNorm
namespace _root_.GlobalTheory.UnitLemma.UnramNorm
theorem _root_.solution (x : K.O) :
    algebraMap K.O K.E (_root_.GlobalTheory.UnitLemma.UnramNorm.cO K x) = K.c (algebraMap K.O K.E x) :=
  _root_.GlobalTheory.UnitLemma.UnramNorm.cOf_spec K x
end _root_.GlobalTheory.UnitLemma.UnramNorm
end GlobalTheory.UnitLemma.UnramNorm
