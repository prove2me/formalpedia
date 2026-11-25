-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.setBadSet_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:05.068184+00:00
-- url     : https://prove2.me/submissions/2c575e57-3ee7-4ece-a32b-cfcadaa3effd

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxPosMeas_setCoincide_null
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxPosMeas_setSecSet_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxPosMeas_mem_setSecSet_of_sheet

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
theorem _root_.solution {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (setFibre S Ψ y).Finite) :
    volume (setBadSet S Ψ) = 0 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  have hρ : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  refine measure_mono_null (t := ⋃ d ∈ D, ⋃ n : ℕ,
      ⋃ G ∈ setSecSet S Ψ (ball d (1 / (n + 1))), ⋃ G' ∈ setSecSet S Ψ (ball d (1 / (n + 1))),
        ⋃ (_ : G ≠ G'), {y | y ∈ ball d (1 / (n + 1)) ∧ G y = G' y}) ?_ ?_
  · rintro y ⟨w, γ, γ', h1, h2, hne⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.2.and h2.2)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨d, hdy, hdD⟩ := Metric.dense_iff.mp hDd y _ (hρ n)
    set B := ball d (1 / ((n : ℝ) + 1))
    have hyB : y ∈ B := by
      rw [mem_ball, dist_comm]
      exact hdy
    have hBsub : B ⊆ ball y ε := by
      intro y' hy'
      rw [mem_ball] at hy' hdy ⊢
      calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hy' hdy
        _ < ε := by linarith
    have hG := mem_setSecSet_of_sheet (S := S) (Ψ := Ψ) (B := B) (γ := γ) fun y' hy' =>
      (hball y' (hBsub hy')).1
    have hG' := mem_setSecSet_of_sheet (S := S) (Ψ := Ψ) (B := B) (γ := γ') fun y' hy' =>
      (hball y' (hBsub hy')).2
    refine Set.mem_iUnion₂.mpr ⟨d, hdD, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion₂.mpr ⟨_, hG,
      Set.mem_iUnion₂.mpr ⟨_, hG', Set.mem_iUnion.mpr ⟨fun heq => hne ?_, hyB, ?_⟩⟩⟩⟩⟩
    · filter_upwards [isOpen_ball.mem_nhds hyB] with y' hy'
      have := congrFun heq y'
      rwa [Set.indicator_of_mem hy', Set.indicator_of_mem hy'] at this
    · simp only [Set.indicator_of_mem hyB]
      rw [h1.1, h2.1]
  · refine (measure_biUnion_null_iff hDc).mpr fun d _ => measure_iUnion_null fun n => ?_
    have hfinS := setSecSet_finite hfin d (hρ n) (S := S) (Ψ := Ψ)
    refine (measure_biUnion_null_iff hfinS.countable).mpr fun G hG => ?_
    refine (measure_biUnion_null_iff hfinS.countable).mpr fun G' hG' => ?_
    exact measure_iUnion_null fun hne => setCoincide_null hG hG' hne
end GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
