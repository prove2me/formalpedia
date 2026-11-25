-- Prove2me | solution 1 for GlobalTheory.GaussPoint.valV_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:17.383966+00:00
-- url     : https://prove2.me/submissions/1e7628bb-826b-4538-a576-71acf1451bb1

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
theorem _root_.solution {π : V} (hπ : Irreducible π) :
    valV V (algebraMap V K π) = WithZero.exp (-1 : ℤ) := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq
end GlobalTheory.GaussPoint
