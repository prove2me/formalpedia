-- Prove2me | solution 1 for GlobalTheory.NormValuation.log_valuation_of_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:09.281843+00:00
-- url     : https://prove2.me/submissions/dd85ed04-521c-4027-b7fb-249af9086421

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
noncomputable section
open GlobalTheory GlobalTheory.NormValuation
variable {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R)
namespace GlobalTheory.NormValuation
theorem _root_.solution (F : Type) [Field F] [Algebra R F] [IsFractionRing R F] (x : R) (hx : x ≠ 0) :
    WithZero.log (w.valuation F (algebraMap R F x)) = -(exponent w (Ideal.span {x}) : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_if_neg hx, WithZero.log_exp, exponent]
end GlobalTheory.NormValuation
