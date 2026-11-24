-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.component_aeval_cx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:20:23.890538+00:00
-- url     : https://prove2.me/submissions/3bf38d26-24a6-4731-a77e-3da127c4cf20

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxPosDens
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxSimple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MemChartComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsGoodProjFirstCoordinate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
theorem _root_.solution {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MRingOver ℂ ι)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (H : MvPolynomial E ℂ)
    (δ : K →₀ ℕ) :
    weightedHomogeneousComponent (blkWt (ι := ι)) δ (aeval yt H) =
      aeval yt (weightedHomogeneousComponent w' δ H) := by
  classical
  rw [H.as_sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hmon : IsWeightedHomogeneous (blkWt (ι := ι)) (aeval yt (monomial m (coeff m H)))
      (Finsupp.weight w' m) := by
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    refine IsWeightedHomogeneous.C_mul ?_ _
    have := IsWeightedHomogeneous.prod m.support (fun e => yt e ^ m e) (fun e => m e • w' e)
      (fun e _ => (hy e).pow (m e))
    rwa [Finsupp.weight_apply]
  by_cases h : Finsupp.weight w' m = δ
  · subst h
    rw [hmon.weightedHomogeneousComponent_same,
      (isWeightedHomogeneous_monomial w' m (coeff m H) rfl).weightedHomogeneousComponent_same]
  · rw [hmon.weightedHomogeneousComponent_ne δ (Ne.symm h),
      (isWeightedHomogeneous_monomial w' m (coeff m H) rfl).weightedHomogeneousComponent_ne δ
        (Ne.symm h), map_zero]
end GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
