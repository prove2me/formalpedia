-- Prove2me | solution 1 for GlobalTheory.VerticalGauss.mem_extPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:22.472075+00:00
-- url     : https://prove2.me/submissions/d512bbde-35a8-4b2e-89a7-4b724eaa3d46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteVerticalGaussValuations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.VerticalGauss
open IsLocalRing IsDedekindDomain
namespace GlobalTheory.VerticalGauss
theorem _root_.solution {K : Type} [Field K] [NumberField K] {σ : Type}
    (la : HeightOneSpectrum (𝓞 K)) (p : MvPolynomial σ (𝓞 K)) :
    p ∈ extPrime σ la ↔ ∀ m, p.coeff m ∈ la.asIdeal :=
  MvPolynomial.mem_map_C_iff
end GlobalTheory.VerticalGauss
