-- Prove2me | solution 1 for GlobalTheory.NormValuation.exponent_prime_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:45.421812+00:00
-- url     : https://prove2.me/submissions/bdb3bea0-e376-4f1b-bafe-46ef6a4d4830

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
theorem _root_.solution (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) (h : p ≠ w.asIdeal) :
    exponent w p = 0 := by
  unfold exponent
  refine Associates.count_eq_zero_of_ne w.associates_irreducible
    (HeightOneSpectrum.associates_irreducible ⟨p, inferInstance, hp⟩) ?_
  intro h1
  exact h (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 h1)).symm
end GlobalTheory.NormValuation
