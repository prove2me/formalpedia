-- Prove2me | solution 1 for GlobalTheory.VerticalGauss.nonneg_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:23.932826+00:00
-- url     : https://prove2.me/submissions/698274a5-9270-432a-acd7-dff8119955d1

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
theorem _root_.solution {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (w : AddValuation Ω (WithTop ℤ)) (h : ∀ r, 0 ≤ w (algebraMap R Ω r)) {b : Ω}
    (hb : IsIntegral R b) : 0 ≤ w b := by
  letI : Algebra R (vRing w) := ((algebraMap R Ω).codRestrict (vRing w) h).toAlgebra
  haveI : IsScalarTower R (vRing w) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb' : IsIntegral (vRing w) b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  rw [← hy]
  exact y.2
end GlobalTheory.VerticalGauss
