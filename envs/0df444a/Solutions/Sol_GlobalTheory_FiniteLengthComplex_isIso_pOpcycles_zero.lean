-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.isIso_pOpcycles_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:14.856118+00:00
-- url     : https://prove2.me/submissions/ffcde508-4a69-41dd-bb68-f0bf853e2ae9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution : IsIso (C.pOpcycles 0) :=
  C.isIso_pOpcycles 0 0 (by simp) (by simp)
end GlobalTheory.FiniteLengthComplex
