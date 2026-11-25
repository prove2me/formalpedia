-- Prove2me | solution 1 for GlobalTheory.GaussPoint.valV_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:19.160795+00:00
-- url     : https://prove2.me/submissions/94d38e00-e3b9-4217-94a8-7c59f5bceeed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing
open GlobalTheory GlobalTheory.GaussPoint
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]
namespace GlobalTheory.GaussPoint
theorem _root_.solution {u : V} (hu : IsUnit u) : valV V (algebraMap V K u) = 1 := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => h hu
end GlobalTheory.GaussPoint
