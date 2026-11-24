-- Prove2me | solution 1 for GlobalTheory.NormValuation.exponent_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:44.599893+00:00
-- url     : https://prove2.me/submissions/eaf9410c-e133-4615-bb52-e90cd9c05c8e

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
theorem _root_.solution {I : Ideal R} (hI : I ≠ ⊥) (n : ℕ) :
    exponent w (I ^ n) = n * exponent w I := by
  unfold exponent
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 hI) w.associates_irreducible]
end GlobalTheory.NormValuation
