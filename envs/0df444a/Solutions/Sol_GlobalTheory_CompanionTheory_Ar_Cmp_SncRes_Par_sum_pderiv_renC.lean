-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.sum_pderiv_renC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:15:04.441211+00:00
-- url     : https://prove2.me/submissions/65a0d0ff-a729-4255-83d8-f721fa20dd87

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MapMemChartIdealOfAevalEqZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SpanEqTopOfForallDotEqZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_BoundaryOnPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_IsRegularLocalRingLocRingOfSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsMulPowEqAevalOfMemAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsBasicOpenOfIsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartParametersAtConePoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution {σ : Type} [Fintype σ] (t₀ : σ → ℂ) (v : Fin (Fintype.card σ) → ℂ)
    (h : MvPolynomial σ ℂ) :
    ∑ j, v j * eval (renPt t₀) (pderiv j (renC σ h)) =
      ∑ q, v (Fintype.equivFin σ q) * eval t₀ (pderiv q h) := by
  rw [← Equiv.sum_comp (Fintype.equivFin σ)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have ht : (renPt t₀ ∘ ⇑(Fintype.equivFin σ)) = t₀ := by
    funext x
    simp [renPt]
  rw [renC, MvPolynomial.renameEquiv_apply, MvPolynomial.pderiv_rename (Fintype.equivFin σ).injective,
    MvPolynomial.eval_rename, ht]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
