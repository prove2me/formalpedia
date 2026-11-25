-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:13.435848+00:00
-- url     : https://prove2.me/submissions/2d2ca18a-0576-4430-8f80-e7f9d6dc1b4d

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
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MeasurableDomCellLogNormChart
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_eval_chartSection
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_mem_closedBall_of_lift_mem_domCell
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_abs_log_div_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_mem_chartComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_sheetSum_0ce06e8414ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartAbsDens_nonneg_5c6d71b76cc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartWeight_of_coord_6d29224d3334
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_chartLift_8692f480c9b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isOpen_chartLiftDom_f424c0a84590
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetSum_le_mul_0df1d0f6a4b5


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxChart
open GroundTheory.Heights₂.Heights (chartLift chartLiftDom contDiff_chartLift chartLift_blockNonzero segre_chartLift
  chartWeight_of_coord)
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart
theorem _root_.solution : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by
  intro K _ _ ι _ Q e m σ i Ψ N A s a J hA _ _ hmeas hzero hJ hproj hint
  classical
  set T : Set (Fin m → ℂ) := Metric.closedBall 0 1 ∩ {x | x (σ.symm i) = 1} with hT
  have hTc : IsCompact T :=
    (isCompact_closedBall (0 : Fin m → ℂ) 1).inter_right
      (isClosed_eq (continuous_apply _) continuous_const)
  have hcont : ContinuousOn (fun x => Real.log (A.h (chartLift σ i x))) T := by
    have h1 : ContinuousOn (fun x => A.h (chartLift σ i x)) T :=
      hA.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn
        fun x hx => chartLift_blockNonzero σ i hx.2
    exact h1.log fun x hx => (A.pos _ (chartLift_blockNonzero σ i hx.2)).ne'
  obtain ⟨C, hC⟩ := hTc.exists_bound_of_continuousOn hcont
  have hchart : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J, x ∈ chartSet (conePts Q) σ i := by
    intro x hx
    rw [← hzero]
    intro q hq
    exact hx q ((mem_chartComponents.1 hJ).1.2 hq)
  have hcoord : ∀ x ∈ chartSet (conePts Q) σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hmeasW : Measurable (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) := by
    unfold chartWeight
    exact (hmeas.comp (contDiff_chartLift σ i (n := 0)).continuous.measurable).piecewise
      (GroundTheory.Heights₂.Heights.isOpen_chartLiftDom σ i).measurableSet measurable_const
  have hmeasD : Measurable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) :=
    GroundTheory.Heights₂.Heights.SheetSumMeasurable.measurable_sheetSum hproj (fun a b => |a * b|)
      ((continuous_mul.comp continuous_id).abs.measurable) hmeasW _
  refine (hint 1 (max C 0)).mono' hmeasD.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (GroundTheory.Heights₂.Heights.chartAbsDens_nonneg _ _ _ _ _)]
  have key : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J,
      |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x| ≤
        |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
          (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x| := by
    intro x hx
    have hxc := hchart x hx
    have h1 := hcoord x hxc
    rw [chartWeight_of_coord _ h1]
    by_cases hd : chartLift σ i x ∈ domCell i
    · have hb := mem_closedBall_of_lift_mem_domCell hxc hd
      have hC' : |Real.log (A.h (chartLift σ i x))| ≤ max C 0 :=
        (hC x ⟨hb, h1⟩).trans (le_max_left _ _)
      have hnz := chartLift_blockNonzero σ i h1
      have habs : absLogNorm A s (chartLift σ i x) = |logNormC A s (chartLift σ i x)| := by
        simp only [absLogNorm]
        rw [if_pos hnz]
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem hb, habs, abs_abs, logNormC,
        ← eval_chartSection]
      exact (abs_log_div_le (norm_nonneg _) (A.pos _ hnz) hC' (le_max_right _ _)).trans
        (le_abs_self _)
    · rw [Set.indicator_of_notMem hd, abs_zero]
      exact abs_nonneg _
  have h := GroundTheory.Heights₂.Heights.sheetSum_le_mul (J := J) (A := chartProjMatrix σ Ψ) (y := y)
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hproj y) 1
    (fun x t => |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x t => |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
      (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x hx t _ => by
      rw [one_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (key x hx.1) (abs_nonneg _))
  exact h.trans_eq (one_mul _)
end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
