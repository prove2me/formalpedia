-- Prove2me | solution 1 for GlobalTheory.NormValuation.exponent_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:43.790856+00:00
-- url     : https://prove2.me/submissions/7d32d088-97ed-4aa0-a52e-764fec1eaf42

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
theorem _root_.solution {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    exponent w (I * J) = exponent w I + exponent w J := by
  unfold exponent
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI)
    (Associates.mk_ne_zero.2 hJ) w.associates_irreducible]
end GlobalTheory.NormValuation
