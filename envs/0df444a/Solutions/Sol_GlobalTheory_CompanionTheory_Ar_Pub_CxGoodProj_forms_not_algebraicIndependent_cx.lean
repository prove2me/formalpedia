-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.forms_not_algebraicIndependent_cx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:06:07.297074+00:00
-- url     : https://prove2.me/submissions/bb9c1eab-ec8d-41d5-a5d1-5972597c8448

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_card_le_ringKrullDim
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxGoodProj_algebraicIndependent_sumElim_cx

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
theorem _root_.solution (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (hQ : IsCxVar Q e)
    {r : ℕ} (hr : e + 1 < r) (L : Fin r → ((k : K) → ι k) → ℂ) :
    ¬ AlgebraicIndependent ℂ (forms (segC Q) L) := by
  intro hind
  obtain ⟨⟨k0⟩, ⟨hprime, hhom, hrel⟩, hdim⟩ := hQ
  haveI := hprime
  choose i0 hi0 using hrel
  have hs := algebraicIndependent_sumElim_cx Q hhom k0 i0 hi0 L hind
  let eqv : Fin (r + Fintype.card {k // k ≠ k0}) ≃ Fin r ⊕ {k // k ≠ k0} :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _).symm)
  have h := card_le_ringKrullDim Q _ (hs.comp eqv eqv.injective)
  rw [hdim] at h
  have hc : Fintype.card {k // k ≠ k0} + 1 = Fintype.card K := by
    have h1 := Fintype.card_subtype_compl (fun k => k = k0)
    rw [Fintype.card_subtype_eq] at h1
    have := Fintype.card_pos_iff.mpr ⟨k0⟩
    simp only [ne_eq]
    omega
  have h' : r + Fintype.card {k // k ≠ k0} ≤ e + Fintype.card K := by exact_mod_cast h
  omega
end GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
