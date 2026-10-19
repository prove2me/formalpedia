-- Prove2me | solution 1 for OAI.Problem356.SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:51:54.06778+00:00
-- url     : https://prove2.me/submissions/696944bb-a5fe-4120-9366-262466916fb6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SmoothBranchMarginal.lean:L272-L319
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Theorems.Thm_OAI_Problem356_JacobianSquareRoot_det_fderiv_ne_zero_of_eventual_leftInverse
import Theorems.Thm_OAI_Problem356_SmoothBranchMarginal_exists_smooth_branch_marginal

-- ---- from OAI.Analysis.CoulombTransport.LocalBranchMeasure ----
namespace OAI

universe uAlpha uBeta

noncomputable section

open MeasureTheory Set

namespace Problem356
namespace LocalBranchMeasure

variable {α : Type uAlpha} {β : Type uBeta} [TopologicalSpace α] [TopologicalSpace β]
  [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β]

/-- The extension is Borel measurable even if the local map is arbitrary outside its source. -/
theorem measurable_extendedBranch (e : OpenPartialHomeomorph α β) (z : β) :
    Measurable (extendedBranch e z) := by
  classical
  exact e.continuousOn.measurable_piecewise continuous_const.continuousOn
    e.open_source.measurableSet

/-- Restricting the domain of a local branch to a measurable set gives a measurable image. -/
theorem measurableSet_image (e : OpenPartialHomeomorph α β)
    {S : Set α} (hS : MeasurableSet S) (hSub : S ⊆ e.source) :
    MeasurableSet (e '' S) := by
  have h := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (hS.preimage measurable_subtype_coe)
  simpa only [Set.image_domRestrict, Set.inter_eq_left.mpr hSub] using h

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
/-- Extension preserves every image of a subset of the local source. -/
theorem extendedBranch_image (e : OpenPartialHomeomorph α β) (z : β)
    {S : Set α} (hSub : S ⊆ e.source) :
    extendedBranch e z '' S = e '' S := by
  apply Set.image_congr
  intro x hx
  exact extendedBranch_apply_of_mem e z (hSub hx)

/-- Measurability of selected branch images required by deterministic-selection obstructions. -/
theorem measurableSet_extendedBranch_image (e : OpenPartialHomeomorph α β) (z : β)
    {S : Set α} (hS : MeasurableSet S) (hSub : S ⊆ e.source) :
    MeasurableSet (extendedBranch e z '' S) := by
  rw [extendedBranch_image e z hSub]
  exact measurableSet_image e hS hSub

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
/-- Injectivity of the extension on any subset of the source. -/
theorem injOn_extendedBranch (e : OpenPartialHomeomorph α β) (z : β)
    {B : Set α} (hB : B ⊆ e.source) : InjOn (extendedBranch e z) B := by
  intro x hx y hy hxy
  apply e.injOn (hB hx) (hB hy)
  simpa only [extendedBranch_apply_of_mem e z (hB hx),
    extendedBranch_apply_of_mem e z (hB hy)] using hxy

end LocalBranchMeasure
end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.JacobianSquareRoot ----
namespace OAI

universe uIndex uE uD

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

namespace Problem356.JacobianSquareRoot

/-- The determinant is a smooth polynomial in the matrix entries. -/
theorem contDiff_matrix_det {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (n : WithTop ENat) : ContDiff ℝ n (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  classical
  change ContDiff ℝ n (fun M : Matrix ι ι ℝ => M.det)
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact contDiff_apply_apply ℝ ℝ (σ i) i

/-- The determinant is smooth on continuous linear endomorphisms in finite dimension. -/
theorem contDiff_clm_det {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : WithTop ENat) :
    ContDiff ℝ n (fun A : E →L[ℝ] E => A.det) := by
  let b := Module.finBasis ℝ E
  have hM : ContDiff ℝ n (fun A : E →L[ℝ] E =>
      LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)) :=
    (((LinearMap.toMatrix b b).toLinearMap.comp
      (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap).contDiff
  simpa only [Function.comp_def, LinearMap.det_toMatrix] using
    (contDiff_matrix_det n).comp hM

/-- Nonzero determinants yield smooth absolute-Jacobian square roots. -/
theorem contDiffOn_sqrt_abs_det
    {D : Type uD} {E : Type uE} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : WithTop ENat} {U : Set D} {A : D → E →L[ℝ] E}
    (hA : ContDiffOn ℝ n A U) (hdet : ∀ x ∈ U, (A x).det ≠ 0) :
    ContDiffOn ℝ n (fun x => Real.sqrt |(A x).det|) U := by
  have hd : ContDiffOn ℝ n (fun x => (A x).det) U :=
    (contDiff_clm_det n).fun_comp_contDiffOn hA
  have ha : ContDiffOn ℝ n (fun x => |(A x).det|) U := by
    simpa only [Real.norm_eq_abs] using hd.norm ℝ hdet
  exact ha.sqrt (fun x hx => abs_ne_zero.mpr (hdet x hx))

/-- Smoothness of the square root of the absolute derivative determinant on an open set. -/
theorem contDiffOn_sqrt_abs_det_fderiv
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} {F : E → E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) F U)
    (hdet : ∀ x ∈ U, (fderiv ℝ F x).det ≠ 0) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun x => Real.sqrt |(fderiv ℝ F x).det|) U := by
  apply contDiffOn_sqrt_abs_det
  · exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hF).2
  · exact hdet

/-- Both smooth directions of an open partial homeomorphism have nonvanishing inverse Jacobian. -/
theorem det_fderiv_symm_ne_zero
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e e.source)
    (he' : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    {y : E} (hy : y ∈ e.target) : (fderiv ℝ e.symm y).det ≠ 0 := by
  apply det_fderiv_ne_zero_of_eventual_leftInverse
    ((he'.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp))
    ((he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp))
  exact e.eventually_right_inverse hy

/-- Smooth inverse-Jacobian factor for a smooth open partial diffeomorphism. -/
theorem contDiffOn_sqrt_abs_det_fderiv_symm
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e e.source)
    (he' : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(fderiv ℝ e.symm y).det|) e.target :=
  contDiffOn_sqrt_abs_det_fderiv e.open_target he'
    (fun _ hy => det_fderiv_symm_ne_zero e he he' hy)

end Problem356.JacobianSquareRoot

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.SmoothBranchMarginal ----
namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.SmoothBranchMarginal

theorem squareDensity_ae_tsupport {g : E3 → ℝ} (hg : Measurable g) :
    ∀ᵐ x ∂densityMeasure (fun x => g x ^ 2), x ∈ tsupport g := by
  rw [densityMeasure, ae_withDensity_iff ((hg.pow_const 2).ennreal_ofReal)]
  apply ae_of_all
  intro x hx
  apply subset_tsupport g
  intro hgx
  exact hx (by simp [hgx])

/-- The preceding construction only needs smoothness in both directions of
the local charts; no determinant or change-of-variables premise remains. -/
theorem exists_smooth_branch_marginal_of_smooth_charts
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target) :
    ∃ (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ),
      NormalizedAmplitude g ∧ tsupport g ⊆ Metric.ball c r ∧
      (∀ i, NormalizedAmplitude (q i) ∧ tsupport (q i) ⊆ e i '' Metric.ball c r) ∧
      IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) ∧
      IsSmoothCompactProbabilityDensity (marginalDensity g q) ∧
      densityMeasure (marginalDensity g q) =
        (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
        ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) •
          Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
            (densityMeasure (fun x => g x ^ 2)) := by
  apply exists_smooth_branch_marginal c hr e hsource hdisj he'
    (fun i y => fderiv ℝ (e i).symm y)
  · intro i y hy
    exact (((he' i).contDiffAt ((e i).open_target.mem_nhds hy)).differentiableAt
      (by simp)).hasFDerivAt
  · intro i
    exact JacobianSquareRoot.contDiffOn_sqrt_abs_det_fderiv_symm (e i) (he i) (he' i)

/-- A measure-level packaging of the actual smooth marginal construction.
All branch extensions are globally measurable, while continuity is retained
on the compact support where it is needed. -/
theorem exists_smoothBranchData_of_smooth_charts
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target) :
    ∃ d : SmoothBranchData (Metric.ball c r),
      ∀ i x, x ∈ Metric.ball c r → d.branch i x = e i x := by
  obtain ⟨g, q, hg, hgs, _, hprob, hrho, hmeasure⟩ :=
    exists_smooth_branch_marginal_of_smooth_charts c hr e hsource hdisj he he'
  let H : Fin 4 → E3 → E3 := fun i => LocalBranchMeasure.extendedBranch (e i) 0
  have himage : ∀ i, H i '' Metric.ball c r = e i '' Metric.ball c r :=
    fun i => LocalBranchMeasure.extendedBranch_image (e i) 0 (hsource i)
  refine ⟨{
    rho := marginalDensity g q
    nu := densityMeasure (fun x => g x ^ 2)
    branch := H
    compactCore := tsupport g
    density_smooth := hrho
    probability := hprob
    measurable_central := Metric.isOpen_ball.measurableSet
    core_compact := hg.2.2.1
    core_subset := hgs
    core_full := squareDensity_ae_tsupport hg.2.1.continuous.measurable
    branch_measurable := fun i => LocalBranchMeasure.measurable_extendedBranch (e i) 0
    branch_injective := fun i => LocalBranchMeasure.injOn_extendedBranch (e i) 0 (hsource i)
    branch_image_measurable := ?_
    branch_continuous := ?_
    component_disjoint := ?_
    density_eq := hmeasure
  }, ?_⟩
  · intro i S hS hSB
    exact LocalBranchMeasure.measurableSet_extendedBranch_image (e i) 0 hS
      (hSB.trans (hsource i))
  · intro i
    apply ((e i).continuousOn.mono (hgs.trans (hsource i))).congr
    intro x hx
    exact LocalBranchMeasure.extendedBranch_apply_of_mem (e i) 0 (hsource i (hgs hx))
  · intro i j hij
    have h := hdisj hij
    cases i <;> cases j <;> simpa only [Option.elim, componentRegion, himage] using h
  · intro i x hx
    exact LocalBranchMeasure.extendedBranch_apply_of_mem (e i) 0 (hsource i hx)

end Problem356.SmoothBranchMarginal

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal
open MeasureTheory Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts := @_root_.OAI.Problem356.SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts
