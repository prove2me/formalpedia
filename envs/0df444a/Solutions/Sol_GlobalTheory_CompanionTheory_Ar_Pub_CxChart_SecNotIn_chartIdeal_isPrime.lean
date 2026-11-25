-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn.chartIdeal_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:52.353596+00:00
-- url     : https://prove2.me/submissions/ffb13ab2-5679-42b9-914e-f7e9ba0f0caf

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
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChartSectionNotMemComponents
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_SecNotIn_mem_of_eval_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_SecNotIn_normAt_mem_chartSet
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_SecNotIn_exists_homogenise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxChart
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights (chartLift chartLift_segre_apply)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn
theorem _root_.solution {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime)
    (hQh : IsMultiHomogIdeal Q) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    {i : (k : K) → ι k} (hw : chartMono i ∉ Q) (hne : chartIdeal (conePts Q) σ i ≠ ⊤) :
    (chartIdeal (conePts Q) σ i).IsPrime := by
  have back : ∀ (f : MvPolynomial (Fin m) ℂ) (F : MRingOver ℂ ι) (D : ℕ),
      (∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
        eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f) →
      F ∈ Q → f ∈ chartIdeal (conePts Q) σ i := by
    intro f F D hF hFQ
    rw [chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 : segre z i ≠ 0 := by rw [hz1]; exact one_ne_zero
    have h := hF z h0
    rw [hz.2 F hFQ, hz1] at h
    simpa using h.symm
  refine ⟨hne, fun {f g} hfg => ?_⟩
  obtain ⟨F, D, hF⟩ := exists_homogenise σ i f
  obtain ⟨G, E, hG⟩ := exists_homogenise σ i g
  have hFG : F * G ∈ Q := mem_of_eval_eq_zero hQp hw fun x hx h0 => by
    have h1 : eval (fun a => segre x (σ a) / segre x i) (f * g) = 0 :=
      (mem_vanishingIdeal_iff.1 hfg) _ (normAt_mem_chartSet hQh σ hx h0)
    rw [map_mul] at h1
    rw [map_mul, hF x h0, hG x h0]
    linear_combination (segre x i ^ D * segre x i ^ E) * h1
  rcases hQp.mem_or_mem hFG with h | h
  · exact Or.inl (back f F D hF h)
  · exact Or.inr (back g G E hG h)
end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn
