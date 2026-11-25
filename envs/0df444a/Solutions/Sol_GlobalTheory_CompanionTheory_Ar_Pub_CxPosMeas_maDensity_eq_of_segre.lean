-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.maDensity_eq_of_segre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:54:24.989091+00:00
-- url     : https://prove2.me/submissions/b8096876-2284-474a-9f0a-9d91ac2a92c1

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
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SetFibreFiniteOfGoodProj
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AemeasurableCxPosDensity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_density_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
open MvPolynomial MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
  GlobalTheory.CompanionTheory.Ar.Pub.CxComp
open ReciprocityTheory.AnForm.R (conePts)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
theorem _root_.solution {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    maDensity (fun j y' => pot L j (γ y')) y = maDensity (fun j y' => pot L j (γ' y')) y := by
  have hs : IsSectionOn (⊥ : Ideal (MRing ι))
      (HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)) 1 := by
    refine ⟨0, fun k => by simp [HermLine.ofWeight], fun m hm k => ?_, ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp
    · simp
  have h := density_eq hL hs hγ hγ' hy hseg
  have h1 : ∀ z, logNorm (HermLine.ofWeight (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) (fun _ _ _ => rfl)) 1 z = 1 := by
    intro z
    simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]
  simpa only [h1, one_mul] using h
end GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
