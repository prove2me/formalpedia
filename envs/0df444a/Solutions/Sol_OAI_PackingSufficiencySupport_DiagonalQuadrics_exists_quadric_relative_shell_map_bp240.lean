-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:50:53.774244+00:00
-- url     : https://prove2.me/submissions/5e38abf9-b1b0-4b20-b929-2e6c4bfb3b17

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_radial_exact_moser_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem staticPullbackOneForm_fderiv {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) (u v : F) :
    fderiv ℝ (staticPullbackOneForm α g) x u v =
      fderiv ℝ α (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) +
        α (g x) (fderiv ℝ (fderiv ℝ g) x u v) := by
  have hd := ((ha.differentiableAt (by simp)).hasFDerivAt.comp x
    (hg.differentiableAt (by simp)).hasFDerivAt).clm_comp
      ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  rw [show fderiv ℝ (staticPullbackOneForm α g) x = _ from hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem staticPullbackOneForm_exterior {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (staticPullbackOneForm α g) x =
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.bilinearComp_apply,staticPullbackOneForm_fderiv ha hg]
  have hs := hg.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq u v]
  ring


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]



theorem timeChartField_contDiffOn
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) (c : M) :
    ContDiffOn ℝ ∞ (timeChartField V c) (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  have h := (contMDiff_iff.mp hV).2 (0,c) (⟨c,V (0,c)⟩ : TangentBundle 𝓘(ℝ,E) M)
  have hh := h.snd
  have hs : ContDiffOn ℝ ∞
      (fun p : ℝ × E => let z := (extChartAt 𝓘(ℝ,E) c).symm p.2
        tangentCoordChange 𝓘(ℝ,E) z c z (V (p.1,z)))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
    apply hh.mono
    intro p hp
    refine ⟨?_,?_⟩
    · simp only [mfld_simps]
      change p ∈ univ ×ˢ (chartAt E c).target
      simpa only [mfld_simps] using hp
    · simp only [Set.mem_preimage,mfld_simps,TangentBundle.mem_chart_source_iff]
      change (chartAt E c).symm p.2 ∈ (chartAt E c).source
      simpa only [mfld_simps] using (extChartAt 𝓘(ℝ,E) c).map_target hp.2

  apply hs.congr
  intro p hp
  dsimp only [timeChartField,chartDifferential]
  have hz := (extChartAt 𝓘(ℝ,E) c).map_target hp.2
  have hz' : (extChartAt 𝓘(ℝ,E) c).symm p.2 ∈ (chartAt E c).source := by
    simpa only [extChartAt_source] using hz
  rw [show (extChartAt 𝓘(ℝ,E) c : M → E) = chartAt E c from rfl,
    mfderiv_chartAt_eq_tangentCoordChange hz']



theorem timeField_smooth_of_coordinates
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ∀ p : ℝ × M, ContDiffAt ℝ ∞ (timeChartField V p.2)
      (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  intro p
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd,?_⟩
  have hc : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ × E) ∞
      (fun q : ℝ × M => (q.1,extChartAt 𝓘(ℝ,E) p.2 q.2)) p :=
    contMDiffAt_fst.prodMk_space (contMDiffAt_extChartAt.comp p contMDiffAt_snd)
  have hh := (hV p).contMDiffAt.comp p hc
  apply hh.congr_of_eventuallyEq
  have hn : ∀ᶠ q : ℝ × M in 𝓝 p, q.2 ∈ (extChartAt 𝓘(ℝ,E) p.2).source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds p.2)
  filter_upwards [hn] with q hq
  dsimp only [Function.comp_apply,timeChartField]
  rw [(extChartAt 𝓘(ℝ,E) p.2).left_inv hq]
  have hq' : q.2 ∈ (chartAt E p.2).source := by simpa only [extChartAt_source] using hq
  have he := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p.2).continuousLinearMapAt_apply_of_mem
    (R := ℝ) (show q.2 ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p.2).baseSet by
      simpa only [TangentBundle.trivializationAt_baseSet] using hq') (V q)
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hq'] at he
  exact he.symm



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartDifferential_inverse {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).inverse =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm y := by
  apply ContinuousLinearMap.inverse_eq
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,E)) hy)
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hy)


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclideanPullbackOneForm_chart {α : ℝ → ManifoldOneForm E M} {g : F → M}
    {p : ℝ × F} {c : M} (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanPullbackOneForm α g p =
      (chartOneForm (α p.1) c (extChartAt 𝓘(ℝ,E) c (g p.2))).comp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2) := by
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp p.2 hg.hasMFDerivAt)
  let A : F →L[ℝ] E :=
    (chartDifferential c (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A p.2 :=
    hasMFDerivAt_iff_hasFDerivAt.mp hd
  have hdf := hf.fderiv
  dsimp only [A,chartDifferential] at hdf
  rw [hdf]
  have hC : (chartDifferential (E := E) c (g p.2)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hc using 1
    all_goals try with_reducible_and_instances rfl
  ext v
  change α p.1 (g p.2) _ = α p.1 ((extChartAt 𝓘(ℝ,E) c).symm
    (extChartAt 𝓘(ℝ,E) c (g p.2))) _
  rw [(extChartAt 𝓘(ℝ,E) c).left_inv hc]
  change _ = α p.1 (g p.2) ((chartDifferential c (g p.2)).inverse
    (chartDifferential c (g p.2) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2 v)))
  erw [hC.inverse_apply_self]
  rfl


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_FixedSpatialIntegral
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem euclideanExteriorOneForm_add {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    euclideanExteriorOneForm (α+β) x =
      euclideanExteriorOneForm α x + euclideanExteriorOneForm β x := by
  rw [euclideanExteriorOneForm,fderiv_add hα hβ]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,add_apply]
  ring

theorem euclideanExteriorOneForm_smul (a : ℝ) {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) :
    euclideanExteriorOneForm (a • α) x = a • euclideanExteriorOneForm α x := by
  rw [euclideanExteriorOneForm,fderiv_const_smul hα]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,smul_apply,
    smul_eq_mul]
  ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology ENNReal
open Set Function MeasureTheory
open Filter
open scoped Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

theorem exists_smooth_compact_extension {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧
      ContDiff ℝ ∞ (fun x => χ x • f x) ∧
      HasCompactSupport (fun x => χ x • f x) ∧
      (∀ᶠ x in 𝓝ˢ K, χ x • f x = f x) := by
  obtain ⟨χ,hχ,hχc,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hK hU hKU
  have hg : ContDiff ℝ ∞ (fun x => χ x • f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun h => hx (hχU h)
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn)
      apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [hy,zero_smul,Pi.zero_apply]
  have hs : tsupport (fun x => χ x • f x) ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    apply hx
    change χ x • f x = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  refine ⟨χ,hχ,hχc,hχU,hχrange,hχ1,hg,
    hχc.of_isClosed_subset (isClosed_tsupport _) hs,?_⟩
  filter_upwards [hχ1] with x hx
  rw [hx,one_smul]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Kahler_PhaseArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Topology
section
variable {ι : Type*} [Fintype ι]

theorem phaseArea_apply (v w : PlanePhase ι) :
    phaseArea v w = ∑ i, ((v i).1*(w i).2-(v i).2*(w i).1) := by
  simp [phaseArea]

theorem phaseArea_skew (v w : PlanePhase ι) : phaseArea v w = -phaseArea w v := by
  simp only [phaseArea_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [DecidableEq ι]

@[simp] theorem phaseArea_single_right (v : PlanePhase ι) (i : ι) (w : Plane) :
    phaseArea v (Pi.single i w) = planarArea (v i) w := by
  classical
  rw [phaseArea_apply,Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hbi]
  · simp

@[simp] theorem phaseArea_single_left (i : ι) (v : Plane) (w : PlanePhase ι) :
    phaseArea (Pi.single i v) w = planarArea v (w i) := by
  classical
  rw [phaseArea_apply,Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hbi]
  · simp

end
section

variable {ι : Type*} [Fintype ι]

theorem phaseDot_symm (z v : PlanePhase ι) : phaseDot z v = phaseDot v z := by
  simp only [phaseDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem phaseSq_hasFDerivAt (z : PlanePhase ι) :
    HasFDerivAt phaseSq ((2:ℝ) • phaseDot z) z := by
  have h := phaseDot.hasFDerivAt.clm_apply (hasFDerivAt_id z)
  apply h.congr_fderiv
  ext v
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.flip_apply,id_eq,
    smul_apply,smul_eq_mul]
  rw [phaseDot_symm v z]
  ring

@[simp] theorem phaseSq_fderiv (z v : PlanePhase ι) :
    fderiv ℝ phaseSq z v = 2 * phaseDot z v := by
  rw [(phaseSq_hasFDerivAt z).fderiv]
  rfl

theorem phaseArea_self (z : PlanePhase ι) : phaseArea z z = 0 := by
  have h := phaseArea_skew z z
  linarith

end
section

variable {ι : Type*} [Fintype ι]

@[simp] theorem phaseDot_J_right (z v : PlanePhase ι) :
    phaseDot z (phaseJ v) = -phaseArea z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem phaseDot_J_left (z v : PlanePhase ι) :
    phaseDot (phaseJ z) v = phaseArea z v := by
  rw [phaseDot_symm,phaseDot_J_right,phaseArea_skew v z,neg_neg]

@[simp] theorem phaseArea_J_right (z v : PlanePhase ι) :
    phaseArea z (phaseJ v) = phaseDot z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem phaseArea_J_left (z v : PlanePhase ι) :
    phaseArea (phaseJ z) v = -phaseDot z v := by
  rw [phaseArea_skew,phaseArea_J_right,phaseDot_symm]

@[simp] theorem phaseDot_J_J (z v : PlanePhase ι) :
    phaseDot (phaseJ z) (phaseJ v) = phaseDot z v := by
  rw [phaseDot_J_left,phaseArea_J_right]

theorem phaseSq_eq_zero_iff (z : PlanePhase ι) : phaseSq z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have hi : (z i).1*(z i).1+(z i).2*(z i).2 ≤ phaseSq z := by
      rw [phaseSq,phaseDot_apply]
      exact Finset.single_le_sum (f := fun j => (z j).1*(z j).1+(z j).2*(z j).2) (fun j _ =>
        add_nonneg (mul_self_nonneg (z j).1) (mul_self_nonneg (z j).2)) (Finset.mem_univ i)
    rw [hz] at hi
    apply Prod.ext <;> dsimp
    · nlinarith [sq_nonneg (z i).2]
    · nlinarith [sq_nonneg (z i).1]
  · rintro rfl
    simp [phaseSq]

theorem phaseSq_pos {z : PlanePhase ι} (hz : z ≠ 0) : 0 < phaseSq z :=
  lt_of_le_of_ne (phaseSq_nonneg z) (fun h => hz ((phaseSq_eq_zero_iff z).mp h.symm))

theorem phase_complex_cauchy (z v : PlanePhase ι) :
    (phaseDot z v)^2+(phaseArea z v)^2 ≤ phaseSq z*phaseSq v := by
  by_cases hz : z=0
  · subst z
    simp [phaseSq]
  have hq := phaseSq_pos hz
  have h := phaseSq_nonneg (phaseSq z • v - phaseDot z v • z - phaseArea z v • phaseJ z)
  have he : phaseSq (phaseSq z • v - phaseDot z v • z - phaseArea z v • phaseJ z) =
      (phaseSq z)^2*phaseSq v-phaseSq z*((phaseDot z v)^2+(phaseArea z v)^2) := by
    simp only [phaseSq,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,
      phaseDot_J_left,phaseDot_J_right,phaseArea_J_left,phaseArea_self]
    rw [phaseDot_symm v z,phaseArea_skew v z]
    ring
  rw [he] at h
  have hm : 0 ≤ phaseSq z*(phaseSq z*phaseSq v-((phaseDot z v)^2+(phaseArea z v)^2)) := by
    nlinarith only [h]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hq).mp hm)

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem finrank_continuous_dual : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldMapDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold
open scoped ContDiff Topology
open Set Function Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclidean_manifold_pullback_germ {α : ManifoldOneForm E M}
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x)
    {c : M} (hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) =ᶠ[𝓝 x]
      staticPullbackOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c ∘ g) := by
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  filter_upwards [hg',hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)] with y hy hcy
  exact euclideanPullbackOneForm_chart (α := fun _ => α) (p := (0,y))
    (hy.mdifferentiableAt (by simp)) hcy

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vector_chartOneForm (α : E → E →L[ℝ] ℝ) (c y : E) :
    chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

theorem vector_exteriorOneForm (α : E → E →L[ℝ] ℝ) :
    manifoldExteriorOneForm α=euclideanExteriorOneForm α := by
  funext y
  simp only [manifoldExteriorOneForm,
    chartDifferential,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
    mfderiv_eq_fderiv,fderiv_id,id_eq]
  rw [show chartOneForm α y=α from funext (vector_chartOneForm α y)]
  ext v w
  rfl

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartOneForm_manifoldPullback_at {α : ℝ → ManifoldOneForm E M} {e : N → M}
    {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e ((extChartAt 𝓘(ℝ,F) b).symm p.2)) :
    chartOneForm (manifoldPullbackOneForm α e p.1) b p.2 =
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := (he.hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackOneForm,hd,chartOneForm,manifoldPullbackOneForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v
  rfl

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclidean_manifold_pullback_exterior_at {α : ManifoldOneForm E M}
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x)
    (hα : ContDiffAt ℝ ∞ (chartOneForm α (g x)) (extChartAt 𝓘(ℝ,E) (g x) (g x))) :
    euclideanExteriorOneForm (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) x =
      (manifoldExteriorOneForm α (g x)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) g x)
        (manifoldMapDifferential (E := E) (F := F) g x) := by
  let c := g x
  have hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have hgc : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) x := (ho.comp x hg).contDiffAt
  have he := euclidean_manifold_pullback_germ (α := α) hg hc
  let A : F →L[ℝ] E := (chartDifferential c (g x)).comp
    (manifoldMapDifferential (E := E) (F := F) g x)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A x :=
    hasMFDerivAt_iff_hasFDerivAt.mp
      ((ho.mdifferentiableAt (by simp)).hasMFDerivAt.comp x
        (hg.mdifferentiableAt (by simp)).hasMFDerivAt)
  have hd := hf.fderiv
  have hfd : fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x =
      (chartDifferential (E := E) c (g x)).comp
        (manifoldMapDifferential (E := E) (F := F) g x) := hd
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c ∘ g)) x := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := by
      rw [staticPullbackOneForm_exterior
        (g := extChartAt 𝓘(ℝ,E) c ∘ g) hα hgc,hfd]
      rfl

end

section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem manifold_pullback_exterior_at {α : ManifoldOneForm E M}
    {g : N → M} {b : N}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α (g b))
      (extChartAt 𝓘(ℝ,E) (g b) (g b)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    manifoldExteriorOneForm (E := F) (M := N)
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =
      manifoldPullbackTwoForm (E := E) (F := F) (fun _ => manifoldExteriorOneForm α) g 0 b := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y ∈ (extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hgy : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]
    exact hg
  have hc : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y :=
    hgy.comp y hi
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hgy.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hu := hi.continuousAt.preimage_mem_nhds hn
  have hh : chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =ᶠ[𝓝 y]
      fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy,hu] with z hz hzU
    exact chartOneForm_manifoldPullback_at (α := fun _ => α) (b := b) (p := (0,z)) hz
      (hzU.mdifferentiableAt (by simp))
  have hder : euclideanExteriorOneForm
      (chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b) y =
      (manifoldExteriorOneForm α (g b)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
        (manifoldMapDifferential (E := E) (F := F) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y) := by
    calc
      _ = euclideanExteriorOneForm
          (fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z)) y := by
        unfold euclideanExteriorOneForm
        rw [hh.fderiv_eq]
      _ = _ := by
        have hα' : ContDiffAt ℝ ∞
            (chartOneForm α ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y))
            (extChartAt 𝓘(ℝ,E) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
              ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)) := by
          simpa only [Function.comp_apply,he] using hα
        simpa only [Function.comp_apply,he] using euclidean_manifold_pullback_exterior_at hc hα'
  have hd := mfderiv_comp y (hgy.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  have hD : manifoldMapDifferential (E := E) (F := F)
      (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y =
      (manifoldMapDifferential (E := E) (F := F) g b).comp
        (chartDifferential (E := F) b b).inverse := by
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y = _
    rw [hd,← chartDifferential_inverse hy]
    change (manifoldMapDifferential (E := E) (F := F) g
      ((extChartAt 𝓘(ℝ,F) b).symm y)).comp
      (chartDifferential (E := F) b ((extChartAt 𝓘(ℝ,F) b).symm y)).inverse = _
    rw [he]
  have H : (chartDifferential (E := F) b b).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,F)) hb using 1
    all_goals try with_reducible_and_instances rfl
  change (euclideanExteriorOneForm
    (chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b) y).bilinearComp
      (chartDifferential (E := F) b b) (chartDifferential (E := F) b b)=_
  rw [hder,hD]
  ext u v
  change manifoldExteriorOneForm α (g b)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g b ((chartDifferential (E := F) b b).inverse (chartDifferential (E := F) b b u)))
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g b ((chartDifferential (E := F) b b).inverse (chartDifferential (E := F) b b v)))=_
  rw [H.inverse_apply_self,H.inverse_apply_self]
  rfl

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {ι : Type*} [Fintype ι]

theorem complexPairing_re (z v : ι → ℂ) :
    (complexPairing z v).re=phaseDot (complexCartesian z) (complexCartesian v) := by
  simp only [complexPairing,Complex.re_sum,Complex.mul_re,Complex.star_def,
    Complex.conj_re,Complex.conj_im,phaseDot_apply,complexCartesian_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexPairing_im (z v : ι → ℂ) :
    (complexPairing z v).im=phaseArea (complexCartesian z) (complexCartesian v) := by
  simp only [complexPairing,Complex.im_sum,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,phaseArea_apply,complexCartesian_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexCartesian_I (z : ι → ℂ) :
    complexCartesian (Complex.I • z)=phaseJ (complexCartesian z) := by
  ext i <;> simp [Pi.smul_apply,Complex.mul_re,Complex.mul_im,phaseJ]

theorem complexDiagonal_pairing (u z v : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1) :
    complexPairing (complexDiagonal u z) (complexDiagonal u v)=complexPairing z v := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [complexDiagonal_apply,star_mul,Complex.star_def]
  calc
    starRingEnd ℂ (z i)*starRingEnd ℂ (u i)*(u i*v i)=
        (starRingEnd ℂ (u i)*u i)*(starRingEnd ℂ (z i)*v i) := by ring
    _=starRingEnd ℂ (z i)*v i := by rw [←Complex.normSq_eq_conj_mul_self,hu]; simp

theorem phaseDiagonal_dot (u : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1)
    (z v : PlanePhase ι) : phaseDot (phaseDiagonal u z) (phaseDiagonal u v)=phaseDot z v := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  obtain ⟨v,rfl⟩ := complexCartesian.surjective v
  rw [phaseDiagonal_cartesian,phaseDiagonal_cartesian,←complexPairing_re,←complexPairing_re,
    complexDiagonal_pairing u z v hu]

theorem phaseDiagonal_area (u : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1)
    (z v : PlanePhase ι) : phaseArea (phaseDiagonal u z) (phaseDiagonal u v)=phaseArea z v := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  obtain ⟨v,rfl⟩ := complexCartesian.surjective v
  rw [phaseDiagonal_cartesian,phaseDiagonal_cartesian,←complexPairing_im,←complexPairing_im,
    complexDiagonal_pairing u z v hu]

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartOneForm_reconstruct_target {α : ManifoldOneForm E M} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartOneForm α c y).comp (chartDifferential c ((extChartAt 𝓘(ℝ,E) c).symm y)) =
      α ((extChartAt 𝓘(ℝ,E) c).symm y) := by
  have hC : (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
    all_goals try with_reducible_and_instances rfl
  ext v
  exact congrArg (α ((extChartAt 𝓘(ℝ,E) c).symm y)) (hC.inverse_apply_self v)


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators

variable {ι : Type*} [Fintype ι]

 theorem hopfPrimitive_smoothAt (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    ContDiffAt ℝ ∞ (hopfPrimitive c) z := by
  exact (contDiffAt_const.div (contDiffAt_const.mul phaseSq_smooth.contDiffAt)
    (mul_ne_zero (by norm_num) (phaseSq_pos hz).ne')).smul (phaseArea (ι := ι)).contDiff.contDiffAt

 theorem hopfPrimitive_fderiv (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v w : PlanePhase ι) :
    fderiv ℝ (hopfPrimitive c) z v w=
      c/(2*phaseSq z)*phaseArea v w-c/(phaseSq z)^2*phaseDot z v*phaseArea z w := by
  have hc := ((hasDerivAt_inv (phaseSq_pos hz).ne').comp_hasFDerivAt z
    (phaseSq_hasFDerivAt z)).const_mul (c/2)
  have hc' : HasFDerivAt (fun y : PlanePhase ι => c/(2*phaseSq y))
      ((-c/(phaseSq z)^2) • phaseDot z) z := by
    have he : (fun y : PlanePhase ι => c/(2*phaseSq y))=(fun y => c/2*(phaseSq y)⁻¹) := by
      funext y
      ring
    rw [he]
    apply hc.congr_fderiv
    ext v
    simp only [smul_apply,smul_eq_mul,smul_smul]
    ring
  have hd := hc'.smul (phaseArea (ι := ι)).hasFDerivAt
  rw [show fderiv ℝ (hopfPrimitive c) z=_ from hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

 theorem hopfForm_apply (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v w : PlanePhase ι) :
    hopfForm c z v w=c/phaseSq z*phaseArea v w-
      c/(phaseSq z)^2*(phaseDot z v*phaseArea z w-phaseDot z w*phaseArea z v) := by
  simp only [hopfForm,euclideanExteriorOneForm,sub_apply,
    ContinuousLinearMap.flip_apply,hopfPrimitive_fderiv c hz,phaseArea_skew w v]
  ring

 theorem hopfPrimitive_circle (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    hopfPrimitive c z (phaseJ z)=c/2 := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseArea_J_right,phaseSq]
  calc
    c/(2*phaseDot z z)*phaseDot z z=c/2*(phaseDot z z/phaseDot z z) := by ring
    _=c/2 := by rw [div_self (show phaseDot z z≠0 from (phaseSq_pos hz).ne'),mul_one]

 theorem hopfForm_radial (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z z v=0 := by
  rw [hopfForm_apply c hz]
  simp only [phaseArea_self,mul_zero,sub_zero,phaseSq]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

 theorem hopfForm_circle (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z (phaseJ z) v=0 := by
  rw [hopfForm_apply c hz]
  simp only [phaseDot_J_right,phaseArea_J_left,phaseArea_self,neg_zero,zero_mul,
    phaseArea_J_right,phaseSq,zero_sub]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

 theorem hopfForm_complex_diagonal (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z v (phaseJ v)=c/(phaseSq z)^2*
      (phaseSq z*phaseSq v-((phaseDot z v)^2+(phaseArea z v)^2)) := by
  rw [hopfForm_apply c hz]
  simp only [phaseArea_J_right,phaseDot_J_right,phaseSq]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

 theorem hopfForm_semipositive {c : ℝ} (hc : 0 ≤ c) {z : PlanePhase ι} (hz : z≠0)
    (v : PlanePhase ι) : 0≤hopfForm c z v (phaseJ v) := by
  rw [hopfForm_complex_diagonal c hz]
  exact mul_nonneg (div_nonneg hc (sq_nonneg _)) (sub_nonneg.mpr (phase_complex_cauchy z v))

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem SmoothOneFormFamily.time_contDiffAt {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (x : M) : ContDiffAt ℝ ∞ (fun s => Γ s x) t := by
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hcam := ((hΓ x).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      (show (t,extChartAt 𝓘(ℝ,E) x x) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) x).target from ⟨mem_univ t,hxt⟩))).comp t (contDiffAt_id.prodMk contDiffAt_const)
  have hsm := hcam.clm_comp (contDiffAt_const (c := chartDifferential x x))
  apply hsm.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [(extChartAt 𝓘(ℝ,E) x).left_inv hx,Function.comp_def,id_eq] using (chartOneForm_reconstruct_target
      (α := Γ s) hxt).symm)

theorem manifoldTimePrimitive_eval_constant {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {x : M} {Z : E}
    (hz : ∀ t, Γ t x Z=Γ 0 x Z) (t : ℝ) : manifoldTimePrimitive Γ t x Z=0 := by
  have hd := (((hΓ.time_contDiffAt t x).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt).clm_apply
    (hasDerivAt_const t Z)
  have he : (fun s => Γ s x Z) = fun _ : ℝ => Γ 0 x Z := funext hz
  change HasDerivAt (fun s => Γ s x Z) _ t at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const t (Γ 0 x Z))
  simpa only [manifoldTimePrimitive,ContinuousLinearMap.map_zero,add_zero] using hh

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_FlowSmoothExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem timeLiftField_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)).tangent) ∞
      (fun p => (⟨p,timeLiftField χ V p⟩ : TangentBundle ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (ℝ × M))) := by
  have hc : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,ℝ)).tangent ∞
      (fun p : ℝ × M => (⟨p.1,(1:ℝ)⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) := by
    have hp : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ)).tangent ∞
        (fun r : ℝ => (⟨r,(1:ℝ)⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact hp.comp contMDiff_fst
  have hu : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)).tangent) ∞
      (fun p : ℝ × M => (⟨p,((1:ℝ),V p)⟩ : TangentBundle ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (ℝ × M))) :=
    contMDiff_equivTangentBundleProd_symm.comp (hc.prodMk hV)
  exact (hχ.contMDiff.comp contMDiff_fst).smul_section hu


end

open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_MovingPrimitiveNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem primitivePullback_smoothAt {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (primitivePullback α g) x :=
  (hα.comp x hg).clm_comp (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem primitivePullback_exteriorAt {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (primitivePullback α g) x=
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  have hh := manifold_pullback_exterior_at (α := α) (g := g)
    (by rw [show chartOneForm α (g x)=α from funext (vector_chartOneForm α (g x))]
        simpa only [extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using hα) hg.contMDiffAt
  have he : manifoldPullbackOneForm (fun _ => α) g 0=primitivePullback α g := by
    funext z
    simp [manifoldPullbackOneForm,manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback]
  rw [he] at hh
  simpa only [vector_exteriorOneForm,manifoldPullbackOneForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback] using hh

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_SixLargeQuadricPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped BigOperators
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 theorem radialSymplectization_apply (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) (v w : PlanePhase ι) :
    radialSymplectization z α C v w=
      2*(phaseDot z v*α w-α v*phaseDot z w)+phaseSq z*C v w := by
  simp only [radialSymplectization,add_apply,smul_apply,sub_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]

 theorem radialSymplectization_nondegenerate {z : PlanePhase ι} (hz : z≠0)
    (α : PlanePhase ι →L[ℝ] ℝ) (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hαJ : α (phaseJ z)=c)
    (hCr : ∀ v,C v z=0) (hCJr : ∀ v,C v (phaseJ z)=0)
    (hCJl : ∀ v,C (phaseJ z) v=0)
    (hpos : ∀ v,phaseDot z v=0 → phaseArea z v=0 → v≠0 → 0<C v (phaseJ v)) :
    (radialSymplectization z α C).IsInvertible := by
  let Ω := radialSymplectization z α C
  have hq := phaseSq_pos hz
  have hinj : Injective Ω := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change Ω v=0 at hv
    have hval (w : PlanePhase ι) : Ω v w=0 := by rw [hv]; rfl
    have hdz : phaseDot z v=0 := by
      have h := hval (phaseJ z)
      change radialSymplectization z α C v (phaseJ z)=0 at h
      rw [radialSymplectization_apply,hαJ,hCJr,phaseDot_J_right,phaseArea_self] at h
      nlinarith
    have hαv : α v=0 := by
      have h := hval z
      change radialSymplectization z α C v z=0 at h
      rw [radialSymplectization_apply,hdz,hCr] at h
      change 2*(0*α z-α v*phaseSq z)+phaseSq z*0=0 at h
      nlinarith
    let b := phaseArea z v/phaseSq z
    let w := v-b•phaseJ z
    have hwd : phaseDot z w=0 := by
      simp only [w,map_sub,map_smul,phaseDot_J_right,phaseArea_self,neg_zero,smul_eq_mul,
        mul_zero,sub_zero,hdz]
    have hwa : phaseArea z w=0 := by
      simp only [w,map_sub,map_smul,smul_eq_mul,phaseArea_J_right]
      change phaseArea z v-(phaseArea z v/phaseSq z)*phaseSq z=0
      field_simp [hq.ne']
      ring
    have hCw : C w (phaseJ w)=0 := by
      have h := hval (phaseJ w)
      change radialSymplectization z α C v (phaseJ w)=0 at h
      rw [radialSymplectization_apply,hdz,hαv] at h
      have he : C w (phaseJ w)=C v (phaseJ w) := by
        simp only [w,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,hCJl,mul_zero,sub_zero]
      rw [he]
      nlinarith
    have hw : w=0 := by
      by_contra hn
      have hh := hpos w hwd hwa hn
      linarith
    have hvw : v=b•phaseJ z := sub_eq_zero.mp hw
    have hb : b=0 := by
      rw [hvw,map_smul,hαJ,smul_eq_mul] at hαv
      exact (mul_eq_zero.mp hαv).resolve_right hc.ne'
    rw [hvw,hb,zero_smul]
  have hsurj : Surjective Ω :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuous_dual (E := PlanePhase ι)).symm).mp hinj
  exact ⟨(LinearEquiv.ofBijective Ω.toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv,rfl⟩

 theorem radialSymplectization_circle (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) {c : ℝ}
    (hα : α (phaseJ z)=c) (hC : ∀ v,C v (phaseJ z)=0) (v : PlanePhase ι) :
    radialSymplectization z α C v (phaseJ z)=2*c*phaseDot z v := by
  rw [radialSymplectization_apply,hα,hC,phaseDot_J_right,phaseArea_self]
  ring

theorem mixedHopfPrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    ContDiffAt ℝ ∞ (mixedHopfPrimitive F c d) z :=
  ((hopfPrimitive_smoothAt c hz).const_smul (1-2*d)).add
    ((primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).const_smul d)

theorem mixedHopfForm_eq {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    mixedHopfForm F c d z=(1-2*d)•hopfForm c z+
      d•(hopfForm c (F z)).bilinearComp (fderiv ℝ F z) (fderiv ℝ F z) := by
  have h₀ := (hopfPrimitive_smoothAt c hz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h₁ := (primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).differentiableAt (by simp)
  rw [mixedHopfForm,mixedHopfPrimitive,euclideanExteriorOneForm_add (h₀.const_smul _) (h₁.const_smul _),
    euclideanExteriorOneForm_smul _ h₀,euclideanExteriorOneForm_smul _ h₁,
    primitivePullback_exteriorAt (hopfPrimitive_smoothAt c hFz) hF]
  rfl

theorem mixedHopfPrimitive_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z)) (c d : ℝ) :
    mixedHopfPrimitive F c d z (phaseJ z)=c/2 := by
  simp only [mixedHopfPrimitive,Pi.add_apply,Pi.smul_apply,add_apply,smul_apply,
    smul_eq_mul,primitivePullback,ContinuousLinearMap.comp_apply,hD,map_smul,
    hopfPrimitive_circle c hz,hopfPrimitive_circle c hFz]
  ring

theorem mixedHopfForm_radial {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=(2:ℝ)•F z) (c d : ℝ) (v : PlanePhase ι) :
    mixedHopfForm F c d z z v=0 := by
  rw [mixedHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hD,
    map_smul,hopfForm_radial c hz,hopfForm_radial c hFz,mul_zero,add_zero]

theorem mixedHopfForm_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z)) (c d : ℝ) (v : PlanePhase ι) :
    mixedHopfForm F c d z (phaseJ z) v=0 := by
  rw [mixedHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hD,
    map_smul,hopfForm_circle c hz,hopfForm_circle c hFz,mul_zero,add_zero]

theorem mixedHopfForm_skew (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (z v w : PlanePhase ι) : mixedHopfForm F c d z v w= -mixedHopfForm F c d z w v := by
  simp only [mixedHopfForm,euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]
  ring

theorem mixedHopfForm_horizontal_positive {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2)
    {v : PlanePhase ι} (hdv : phaseDot z v=0) (hav : phaseArea z v=0) (hv : v≠0) :
    0 < mixedHopfForm F c d z v (phaseJ v) := by
  rw [mixedHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hJ]
  have hp : 0<hopfForm c z v (phaseJ v) := by
    rw [hopfForm_complex_diagonal c hz,hdv,hav]
    simp only [zero_pow (by norm_num : 2≠0),zero_add,sub_zero]
    exact mul_pos (div_pos hc (sq_pos_of_pos (phaseSq_pos hz)))
      (mul_pos (phaseSq_pos hz) (phaseSq_pos hv))
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp)
    (mul_nonneg hd (hopfForm_semipositive hc.le hFz _))

theorem homogeneousConePrimitive_exterior {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    euclideanExteriorOneForm (homogeneousConePrimitive F c d) z=
      radialSymplectization z (mixedHopfPrimitive F c d z) (mixedHopfForm F c d z) := by
  have ha := (mixedHopfPrimitive_smoothAt hF hz hFz c d).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := (phaseSq_hasFDerivAt z).smul ha.hasFDerivAt
  rw [euclideanExteriorOneForm,show fderiv ℝ (homogeneousConePrimitive F c d) z=_ from he.fderiv]
  ext v w
  simp only [sub_apply,ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,radialSymplectization_apply,
    mixedHopfForm,euclideanExteriorOneForm]
  ring

theorem homogeneousConePrimitive_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) :
    (euclideanExteriorOneForm (homogeneousConePrimitive F c d) z).IsInvertible := by
  have hDJ : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z) := by rw [hJ,hD,map_smul]
  rw [homogeneousConePrimitive_exterior hF hz hFz]
  apply radialSymplectization_nondegenerate hz _ _ (half_pos hc)
    (mixedHopfPrimitive_circle hz hFz hDJ c d)
  · intro v
    rw [mixedHopfForm_skew,mixedHopfForm_radial hF hz hFz hD,neg_zero]
  · intro v
    rw [mixedHopfForm_skew,mixedHopfForm_circle hF hz hFz hDJ,neg_zero]
  · exact mixedHopfForm_circle hF hz hFz hDJ c d
  · intro v hdv hav hv
    exact mixedHopfForm_horizontal_positive hF hz hFz hJ hc hd hdhalf hdv hav hv

theorem homogeneousConePrimitive_circle_contraction {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hDJ : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z)) (c d : ℝ) (v : PlanePhase ι) :
    euclideanExteriorOneForm (homogeneousConePrimitive F c d) z v (phaseJ z)=c*phaseDot z v := by
  rw [homogeneousConePrimitive_exterior hF hz hFz,
    radialSymplectization_circle z _ _ (mixedHopfPrimitive_circle hz hFz hDJ c d)
      (fun v => by rw [mixedHopfForm_skew,mixedHopfForm_circle hF hz hFz hDJ,neg_zero])]
  ring

theorem homogeneousConePrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    ContDiffAt ℝ ∞ (homogeneousConePrimitive F c d) z :=
  phaseSq_smooth.contDiffAt.smul (mixedHopfPrimitive_smoothAt hF hz hFz c d)

theorem homogeneousConePrimitive_affine (F : PlanePhase ι → PlanePhase κ)
    (c d s : ℝ) (z : PlanePhase ι) :
    (1-s)•homogeneousConePrimitive F c 0 z+s•homogeneousConePrimitive F c d z=
      homogeneousConePrimitive F c (s*d) z := by
  ext v
  simp only [homogeneousConePrimitive,mixedHopfPrimitive,Pi.add_apply,Pi.smul_apply,
    add_apply,smul_apply,smul_eq_mul]
  ring

theorem homogeneousConePrimitive_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z)) (c d : ℝ) :
    homogeneousConePrimitive F c d z (phaseJ z)=phaseSq z*(c/2) := by
  simp only [homogeneousConePrimitive,smul_apply,smul_eq_mul,mixedHopfPrimitive_circle hz hFz hD c d]

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldExteriorNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem nonautonomous_curve_lift
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2} {γ : ℝ → M} {t : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t)))) :
    HasMFDerivAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (fun s => (s,γ s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeLiftField (fun _ => 1) V (t,γ t))) := by
  apply ((hasMFDerivAt_id (I := 𝓘(ℝ,ℝ)) t).prodMk hγ).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change (a,a • V (t,γ t)) = a • ((1:ℝ) • ((1:ℝ),V (t,γ t)))
  simp only [one_smul,Prod.smul_mk,smul_eq_mul,mul_one]

variable [T2Space M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem nonautonomous_curve_eqOn
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) {γ δ : ℝ → M}
    (hγ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t))))
    (hδ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) δ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,δ t))))
    (h0 : γ t₀ = δ t₀) : EqOn γ δ (Ioo a b) := by
  have hγl : IsMIntegralCurveOn (fun t => (t,γ t)) (timeLiftField (fun _ => 1) V) (Ioo a b) :=
    fun t ht => (nonautonomous_curve_lift (hγ t ht)).hasMFDerivWithinAt
  have hδl : IsMIntegralCurveOn (fun t => (t,δ t)) (timeLiftField (fun _ => 1) V) (Ioo a b) :=
    fun t ht => (nonautonomous_curve_lift (hδ t ht)).hasMFDerivWithinAt
  have he := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀
    ((timeLiftField_smooth contDiff_const hV).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hγl hδl (by rw [h0])
  intro t ht
  exact congrArg Prod.snd (he ht)

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem reparametrizedTimeField_smooth {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,reparametrizedTimeField τ V p⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  apply timeField_smooth_of_coordinates
  intro p
  have hq := (timeChartField_contDiffOn hV p.2).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p.2)).mem_nhds
      (show (τ p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) p.2).target
        from ⟨mem_univ _,mem_extChartAt_target p.2⟩))
  have hdτ : ContDiff ℝ ∞ (deriv τ) := hτ.deriv'
  have hd : ContDiffAt ℝ ∞ (fun q : ℝ × E => deriv τ q.1)
      (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) := hdτ.contDiffAt.comp _ contDiffAt_fst
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × E => (τ q.1,q.2))
      (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) :=
    (hτ.contDiffAt.comp _ contDiffAt_fst).prodMk contDiffAt_snd
  have hspace := hq.comp (f := fun q : ℝ × E => (τ q.1,q.2))
    (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) hcoord
  have hs := hd.smul hspace
  apply hs.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro q
  dsimp only [timeChartField,reparametrizedTimeField]
  exact (chartDifferential p.2 _).map_smul _ _

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem reparametrizedTimeField_curve {τ : ℝ → ℝ} {t : ℝ}
    (hτ : DifferentiableAt ℝ τ t)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2} {γ : ℝ → M}
    (hγ : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ (τ t)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (τ t,γ (τ t))))) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (γ ∘ τ) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (reparametrizedTimeField τ V (t,γ (τ t)))) := by
  apply (hγ.comp t (hasMFDerivAt_iff_hasFDerivAt.mpr hτ.hasFDerivAt)).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change (fderiv ℝ τ t a) • V (τ t,γ (τ t)) = a • (deriv τ t • V (τ t,γ (τ t)))
  rw [hτ.hasDerivAt.hasFDerivAt.fderiv]
  change ((a : ℝ) * deriv τ t) • V (τ t,γ (τ t)) = (a : ℝ) • (deriv τ t • V (τ t,γ (τ t)))
  exact mul_smul (a : ℝ) (deriv τ t) _

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [T2Space M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem nonautonomous_curve_eqOn_Icc
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) {γ δ : ℝ → M}
    (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t))))
    (hδ : ∀ t ∈ Icc (0:ℝ) 1, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) δ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,δ t))))
    (h0 : γ 0 = δ 0) : EqOn γ δ (Icc (0:ℝ) 1) := by
  let τ : ℝ → ℝ := fun s => Real.sin s ^ 2
  have hτ : ContDiff ℝ ∞ τ := by dsimp [τ]; fun_prop
  have hτI (s : ℝ) : τ s ∈ Icc (0:ℝ) 1 := ⟨sq_nonneg _,Real.sin_sq_le_one s⟩
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτ1 : τ (Real.pi/2) = 1 := by simp [τ]
  have heq : EqOn (γ ∘ τ) (δ ∘ τ) (Ioo (-2:ℝ) 2) :=
    nonautonomous_curve_eqOn (reparametrizedTimeField_smooth hτ hV)
      (by norm_num : (0:ℝ) ∈ Ioo (-2:ℝ) 2)
      (fun s _ => reparametrizedTimeField_curve (hτ.differentiable (by simp) s) (hγ _ (hτI s)))
      (fun s _ => reparametrizedTimeField_curve (hτ.differentiable (by simp) s) (hδ _ (hτI s)))
      (by simp only [Function.comp_apply,hτ0,h0])
  intro t ht
  have hsubset := intermediate_value_Icc (by positivity : (0:ℝ) ≤ Real.pi/2)
    hτ.continuous.continuousOn
  have hti : t ∈ Icc (τ 0) (τ (Real.pi/2)) := by simpa only [hτ0,hτ1] using ht
  obtain ⟨s,hs,hst⟩ := hsubset hti
  have hs' : s ∈ Ioo (-2:ℝ) 2 := by
    constructor
    · linarith [hs.1]
    · linarith [hs.2,Real.pi_lt_four]
  have h := heq hs'
  simpa only [Function.comp_apply,hst] using h

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_CircleRelativeRadialMoser
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped BigOperators
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem phaseShell_isCompact (a b : ℝ) : IsCompact (phaseShell (ι := ι) a b) := by
  apply (isCompact_closedBall (0:PlanePhase ι) (max b 0+1)).of_isClosed_subset
    (isClosed_Icc.preimage phaseSq_smooth.continuous)
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ max b 0+1)).mpr
  intro i
  have hi : (z i).1*(z i).1+(z i).2*(z i).2≤phaseSq z := by
    simpa only [phaseSq,phaseDot_apply] using Finset.single_le_sum (f := fun j => (z j).1*(z j).1+(z j).2*(z j).2)
      (fun j _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Finset.mem_univ i)
  have hb := hz.2
  change phaseSq z≤b at hb
  rw [Prod.norm_def,max_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (z i).2,sq_nonneg (|(z i).1|-1),sq_abs (z i).1,le_max_left b 0,le_max_right b 0]
  · rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (z i).1,sq_nonneg (|(z i).2|-1),sq_abs (z i).2,le_max_left b 0,le_max_right b 0]

theorem phaseShell_nonzero {a b : ℝ} (ha : 0<a) {z : PlanePhase ι}
    (hz : z∈phaseShell a b) : z≠0 := by
  intro h
  have hh := hz.1
  change a≤phaseSq z at hh
  rw [h,phaseSq] at hh
  simp only [map_zero] at hh
  linarith

theorem phaseShell_radial (a b : ℝ) {x : PlanePhase ι} (hx : x∈phaseShell a b)
    {y : PlanePhase ι} (h : phaseSq y=phaseSq x) : y∈phaseShell a b := by
  change phaseSq y∈Icc a b
  rw [h]
  exact hx

theorem exists_global_homogeneous_cone_path
    {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ z,z≠0 → F z≠0) {K : Set (PlanePhase ι)} (hK : IsCompact K)
    (hK0 : ∀ z∈K,z≠0) (c d : ℝ) :
    ∃ Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι),
      SmoothOneFormFamily Γ ∧ ∃ O : Set (PlanePhase ι),IsOpen O ∧ K⊆O ∧
      (∀ z∈O,z≠0) ∧ ∀ s,EqOn (Γ s) (homogeneousConePrimitive F c (s*d)) O := by
  let f : PlanePhase ι → (PlanePhase ι →L[ℝ] ℝ) × (PlanePhase ι →L[ℝ] ℝ) :=
    fun z => (homogeneousConePrimitive F c 0 z,homogeneousConePrimitive F c d z)
  have hf : ContDiffOn ℝ ∞ f ({0}ᶜ : Set (PlanePhase ι)) := by
    intro z hz
    exact ((homogeneousConePrimitive_smoothAt hF.contDiffAt hz (hF0 z hz) c 0).prodMk
      (homogeneousConePrimitive_smoothAt hF.contDiffAt hz (hF0 z hz) c d)).contDiffWithinAt
  obtain ⟨χ,_hχ,_hχc,_hχs,_hχr,_hχ1,hg,_hgc,hge⟩ :=
    exists_smooth_compact_extension hK isClosed_singleton.isOpen_compl hK0 hf
  let g := fun z => χ z • f z
  let Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι) :=
    fun s z => (1-s)•(g z).1+s•(g z).2
  have hΓe : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => Γ p.1 p.2) :=
    ((contDiff_const.sub contDiff_fst).smul (hg.fst.comp contDiff_snd)).add
      (contDiff_fst.smul (hg.snd.comp contDiff_snd))
  have hΓ : SmoothOneFormFamily Γ := by
    intro z
    simpa only [vector_chartOneForm] using hΓe.contDiffOn
  obtain ⟨A,hA,hKA,hAe⟩ := mem_nhdsSet_iff_exists.mp hge
  let O := A∩({0}ᶜ : Set (PlanePhase ι))
  refine ⟨Γ,hΓ,O,hA.inter isClosed_singleton.isOpen_compl,
    fun z hz => ⟨hKA hz,hK0 z hz⟩,fun _ hz => hz.2,?_⟩
  intro s z hz
  have he : g z=f z := hAe hz.1
  dsimp only [Γ]
  rw [he]
  exact homogeneousConePrimitive_affine F c d s z

theorem homogeneous_cone_path_properties
    {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ z,z≠0 → F z≠0)
    (hD : ∀ z,fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2)
    {Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)} (hΓ : SmoothOneFormFamily Γ)
    {O : Set (PlanePhase ι)} (hO : IsOpen O) (hO0 : ∀ z∈O,z≠0)
    (heq : ∀ s,EqOn (Γ s) (homogeneousConePrimitive F c (s*d)) O) :
    (∀ s,∀ z∈O,manifoldExteriorOneForm (Γ s) z=
      euclideanExteriorOneForm (homogeneousConePrimitive F c (s*d)) z) ∧
    (∀ s,∀ z∈O,∀ v,manifoldExteriorOneForm (Γ s) z v (phaseJ z)=c*phaseDot z v) ∧
    (∀ s,∀ z∈O,manifoldTimePrimitive Γ s z (phaseJ z)=0) ∧
    (∀ s∈Icc (0:ℝ) 1,∀ z∈O,(manifoldExteriorOneForm (Γ s) z).IsInvertible) := by
  have he (s : ℝ) (z : PlanePhase ι) (hz : z∈O) :
      manifoldExteriorOneForm (Γ s) z=euclideanExteriorOneForm (homogeneousConePrimitive F c (s*d)) z := by
    rw [vector_exteriorOneForm,euclideanExteriorOneForm,euclideanExteriorOneForm]
    rw [Filter.EventuallyEq.fderiv_eq ((heq s).eventuallyEq_of_mem (hO.mem_nhds hz))]
  have hDJ (z : PlanePhase ι) : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z) := by
    rw [hJ,hD,map_smul]
  refine ⟨he,?_,?_,?_⟩
  · intro s z hz v
    rw [he s z hz]
    exact homogeneousConePrimitive_circle_contraction hF.contDiffAt (hO0 z hz) (hF0 z (hO0 z hz)) (hDJ z) c (s*d) v
  · intro s z hz
    apply manifoldTimePrimitive_eval_constant hΓ _ s
    intro t
    rw [heq t hz,heq 0 hz,homogeneousConePrimitive_circle (hO0 z hz) (hF0 z (hO0 z hz)) (hDJ z),
      homogeneousConePrimitive_circle (hO0 z hz) (hF0 z (hO0 z hz)) (hDJ z)]
  · intro s hs z hz
    rw [he s z hz]
    apply homogeneousConePrimitive_nondegenerate hF.contDiffAt (hO0 z hz)
      (hF0 z (hO0 z hz)) (hD z) (hJ z) hc (mul_nonneg hs.1 hd)
    exact lt_of_le_of_lt (by nlinarith [hs.2]) hdhalf

theorem homogeneousCone_timePrimitive
    {F : PlanePhase ι → PlanePhase κ} {c d : ℝ}
    {Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)} {z : PlanePhase ι}
    (he : ∀ s,Γ s z=homogeneousConePrimitive F c (s*d) z) (s : ℝ) :
    manifoldTimePrimitive Γ s z=homogeneousConePrimitive F c d z-homogeneousConePrimitive F c 0 z := by
  have he' : (fun s => Γ s z)=(fun s : ℝ => (1-s)•homogeneousConePrimitive F c 0 z+
      s•homogeneousConePrimitive F c d z) :=
    funext fun s => (he s).trans (homogeneousConePrimitive_affine F c d s z).symm
  have hd := (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).smul_const
    (homogeneousConePrimitive F c 0 z)).add
    ((hasDerivAt_id s).smul_const (homogeneousConePrimitive F c d z))
  simp only [Pi.sub_apply,id_eq] at hd
  rw [manifoldTimePrimitive,he']
  convert! hd.deriv using 1
  all_goals try with_reducible_and_instances rfl
  simp [sub_eq_add_neg,add_comm]

 theorem exists_homogeneousCone_shell_flow
    {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ z,z≠0 → F z≠0)
    (hD : ∀ z,fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d a b : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) (ha : 0<a) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ s∈Icc (0:ℝ) 1,∀ x,Ψ (s,Φ (s,x))=x ∧ Φ (s,Ψ (s,x))=x) ∧
      (∀ s∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (s,x))=phaseSq x) ∧
      (∀ s∈Icc (0:ℝ) 1,∀ x∈phaseShell a b,∀ v w,
        euclideanExteriorOneForm (homogeneousConePrimitive F c (s*d)) (Φ (s,x))
            (fderiv ℝ (fun y => Φ (s,y)) x v) (fderiv ℝ (fun y => Φ (s,y)) x w)=
          euclideanExteriorOneForm (homogeneousConePrimitive F c 0) x v w) ∧
      ∃ V : ℝ × PlanePhase ι → PlanePhase ι,
        ContDiff ℝ ∞ V ∧
        (∀ x s,s∈Ioo (-2:ℝ) 2 → HasDerivAt (fun r => Φ (r,x)) (V (s,Φ (s,x))) s) ∧
        ∀ s∈Icc (0:ℝ) 1,∀ x∈phaseShell a b,V (s,x)=homogeneousConeField F c d s x := by
  obtain ⟨Γ,hΓ,O,hO,hKO,hO0,heq⟩ := exists_global_homogeneous_cone_path hF hF0
    (phaseShell_isCompact a b) (fun _ hz => phaseShell_nonzero ha hz) c d
  obtain ⟨he,hcircle,hβ,hinv⟩ := homogeneous_cone_path_properties hF hF0 hD hJ hc hd hdhalf hΓ hO hO0 heq
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hΦr,hΦω,V,hV,hODE,hVe⟩ :=
    exists_compact_radial_exact_moser_bp240 hΓ (phaseShell_isCompact a b) hO hKO
      (fun _ hx _ he => phaseShell_radial a b hx he) hc.ne' hcircle hβ
      (fun s hs z hz => hinv s hs z (hKO hz))
  refine ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hΦr,?_,V,hV,hODE,?_⟩
  · intro s hs x hx v w
    have hh := hΦω s hs x hx v w
    have hx' := hKO (phaseShell_radial a b hx (hΦr s hs x))
    simpa only [manifoldPullback,ContinuousLinearMap.bilinearComp_apply,
      preferredDifferential,mfderiv_eq_fderiv,he s _ hx',he 0 x (hKO hx),zero_mul] using hh
  · intro s hs x hx
    rw [hVe s hs x hx,manifoldMoserField,he s x (hKO hx),
      homogeneousCone_timePrimitive (fun r => heq r (hKO hx))]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem moser_vector_natural
    {Ω₀ Ω₁ : E →L[ℝ] E →L[ℝ] ℝ} {α₀ α₁ : E →L[ℝ] ℝ} {L : E →L[ℝ] E}
    (h₀ : Ω₀.IsInvertible) (h₁ : Ω₁.IsInvertible) (hL : Function.Surjective L)
    (hΩ : ∀ u v, Ω₁ (L u) (L v) = Ω₀ u v)
    (hα : ∀ v, α₁ (L v) = α₀ v) :
    L (-Ω₀.inverse α₀) = -Ω₁.inverse α₁ := by
  apply h₁.injective
  ext w
  obtain ⟨v,rfl⟩ := hL w
  rw [hΩ,map_neg,h₀.self_apply_inverse,map_neg,h₁.self_apply_inverse]
  exact congrArg Neg.neg (hα v).symm

theorem linear_equivariant_fderiv {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (T : PlanePhase κ →L[ℝ] PlanePhase κ) (hFT : ∀ z,F (U z)=T (F z))
    (z v : PlanePhase ι) : fderiv ℝ F (U z) (U v)=T (fderiv ℝ F z v) := by
  have he : (fun z => F (U z))=(fun z => T (F z)) := funext hFT
  have h₁ := ((hF.differentiable (by simp) (U z)).hasFDerivAt).comp z U.hasFDerivAt
  have h₂ := T.hasFDerivAt.comp z ((hF.differentiable (by simp) z).hasFDerivAt)
  change HasFDerivAt (fun z => F (U z)) _ z at h₁
  rw [he] at h₁
  exact congrArg (fun L => L v) (h₁.unique h₂)

theorem hopfPrimitive_linear_invariant (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (hD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (c : ℝ) (z v : PlanePhase ι) : hopfPrimitive c (U z) (U v)=hopfPrimitive c z v := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseSq,hD,hA]

theorem mixedHopfPrimitive_linear_invariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (T : PlanePhase κ →L[ℝ] PlanePhase κ) (hFT : ∀ z,F (U z)=T (F z))
    (hUD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hUA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (hTD : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
    (hTA : ∀ z v,phaseArea (T z) (T v)=phaseArea z v)
    (c d : ℝ) (z v : PlanePhase ι) :
    mixedHopfPrimitive F c d (U z) (U v)=mixedHopfPrimitive F c d z v := by
  simp only [mixedHopfPrimitive,Pi.add_apply,Pi.smul_apply,add_apply,smul_apply,smul_eq_mul,primitivePullback,
    ContinuousLinearMap.comp_apply,hopfPrimitive_linear_invariant U hUD hUA,
    linear_equivariant_fderiv hF U T hFT,hFT,hopfPrimitive_linear_invariant T hTD hTA]

theorem homogeneousConePrimitive_linear_invariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (T : PlanePhase κ →L[ℝ] PlanePhase κ) (hFT : ∀ z,F (U z)=T (F z))
    (hUD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hUA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (hTD : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
    (hTA : ∀ z v,phaseArea (T z) (T v)=phaseArea z v)
    (c d : ℝ) (z v : PlanePhase ι) :
    homogeneousConePrimitive F c d (U z) (U v)=homogeneousConePrimitive F c d z v := by
  simp only [homogeneousConePrimitive,smul_apply,smul_eq_mul,phaseSq,hUD,
    mixedHopfPrimitive_linear_invariant hF U T hFT hUD hUA hTD hTA]

theorem exterior_linear_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E →L[ℝ] ℝ} (U : E →L[ℝ] E) {z : E}
    (hα : ContDiffAt ℝ ∞ α (U z)) (he : ∀ x v,α (U x) (U v)=α x v) (v w : E) :
    euclideanExteriorOneForm α (U z) (U v) (U w)=euclideanExteriorOneForm α z v w := by
  have he' : primitivePullback α U=α := by
    funext x
    ext v
    simpa only [primitivePullback,ContinuousLinearMap.comp_apply,U.fderiv] using he x v
  have hh := primitivePullback_exteriorAt hα U.contDiff.contDiffAt
  rw [he',U.fderiv] at hh
  exact (congrArg (fun B => B v w) hh).symm

theorem homogeneousConeField_linear_invariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0)
    (hD : ∀ z,fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (U : PlanePhase ι ≃L[ℝ] PlanePhase ι) (T : PlanePhase κ →L[ℝ] PlanePhase κ)
    (hFT : ∀ z,F (U z)=T (F z))
    (hUD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hUA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (hTD : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
    (hTA : ∀ z v,phaseArea (T z) (T v)=phaseArea z v)
    {c d s : ℝ} (hc : 0 < c) (hd : 0 ≤ s * d) (hdhalf : s * d < 1/2)
    {z : PlanePhase ι} (hz : z≠0) :
    homogeneousConeField F c d s (U z)=U (homogeneousConeField F c d s z) := by
  have hUz : U z≠0 := fun h => hz (U.injective (h.trans (map_zero U).symm))
  have hI (e : ℝ) (x v : PlanePhase ι) :=
    homogeneousConePrimitive_linear_invariant hF U.toContinuousLinearMap T hFT hUD hUA hTD hTA c e x v
  symm
  unfold homogeneousConeField
  apply moser_vector_natural (L := U.toContinuousLinearMap)
    (homogeneousConePrimitive_nondegenerate hF.contDiffAt hz (hF0 z hz) (hD z) (hJ z) hc hd hdhalf)
    (homogeneousConePrimitive_nondegenerate hF.contDiffAt hUz (hF0 _ hUz) (hD _) (hJ _) hc hd hdhalf)
    U.surjective
  · exact exterior_linear_invariant U.toContinuousLinearMap
      (homogeneousConePrimitive_smoothAt hF.contDiffAt hUz (hF0 _ hUz) c (s*d)) (hI (s*d))
  · intro v
    exact congrArg₂ (· - ·) (hI d z v) (hI 0 z v)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricLargeAmbientPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Function Filter
open Set
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem euclideanTimeField_smooth {V : ℝ × E → E} (hV : ContDiff ℝ ∞ V) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) E)) := by
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have h := (contDiff_snd.prodMk hV).contMDiff
  have hh := contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ,E)) (n := ∞)
  rw [ModelWithCorners.tangent, ← modelWithCornersSelf_prod] at hh
  exact hh.comp h

theorem euclidean_nonautonomous_curve_eqOn_Icc
    {V : ℝ × E → E} (hV : ContDiff ℝ ∞ V) {γ δ : ℝ → E}
    (hγ : ∀ s∈Icc (0:ℝ) 1,HasDerivAt γ (V (s,γ s)) s)
    (hδ : ∀ s∈Icc (0:ℝ) 1,HasDerivAt δ (V (s,δ s)) s)
    (h0 : γ 0=δ 0) : EqOn γ δ (Icc (0:ℝ) 1) := by
  exact nonautonomous_curve_eqOn_Icc (euclideanTimeField_smooth hV)
    (fun s hs => hasMFDerivAt_iff_hasFDerivAt.mpr (hγ s hs).hasFDerivAt)
    (fun s hs => hasMFDerivAt_iff_hasFDerivAt.mpr (hδ s hs).hasFDerivAt) h0

theorem closed_flow_linear_equivariant_on
    {V Φ : ℝ × E → E} (hV : ContDiff ℝ ∞ V)
    (hODE : ∀ x s,s∈Icc (0:ℝ) 1 → HasDerivAt (fun r => Φ (r,x)) (V (s,Φ (s,x))) s)
    (hΦ0 : ∀ x,Φ (0,x)=x) {K : Set E}
    (hstay : ∀ s∈Icc (0:ℝ) 1,∀ x∈K,Φ (s,x)∈K)
    (U : E →L[ℝ] E)
    (hrel : ∀ s∈Icc (0:ℝ) 1,∀ x∈K,V (s,U x)=U (V (s,x))) :
    ∀ s∈Icc (0:ℝ) 1,∀ x∈K,Φ (s,U x)=U (Φ (s,x)) := by
  intro s hs x hx
  apply euclidean_nonautonomous_curve_eqOn_Icc hV
    (fun r hr => hODE (U x) r hr) ?_ ?_ hs
  · intro r hr
    have hd := U.hasFDerivAt.comp_hasDerivAt r (hODE x r hr)
    simpa only [Function.comp_def, hrel r hr _ (hstay r hr x hx)] using hd
  · simp only [hΦ0]

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem homogeneousCone_shell_flow_linear_equivariant
    {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ z,z≠0 → F z≠0)
    (hD : ∀ z,fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d a b : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) (ha : 0<a)
    {Φ V : ℝ × PlanePhase ι → PlanePhase ι}
    (hΦ0 : ∀ x,Φ (0,x)=x)
    (hΦr : ∀ s∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (s,x))=phaseSq x)
    (hV : ContDiff ℝ ∞ V)
    (hODE : ∀ x s,s∈Ioo (-2:ℝ) 2 → HasDerivAt (fun r => Φ (r,x)) (V (s,Φ (s,x))) s)
    (hVe : ∀ s∈Icc (0:ℝ) 1,∀ x∈phaseShell a b,V (s,x)=homogeneousConeField F c d s x)
    (U : PlanePhase ι ≃L[ℝ] PlanePhase ι) (T : PlanePhase κ →L[ℝ] PlanePhase κ)
    (hFT : ∀ z,F (U z)=T (F z))
    (hUD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hUA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (hTD : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
    (hTA : ∀ z v,phaseArea (T z) (T v)=phaseArea z v) :
    ∀ s∈Icc (0:ℝ) 1,∀ x∈phaseShell a b,Φ (s,U x)=U (Φ (s,x)) := by
  apply closed_flow_linear_equivariant_on hV
    (fun x s hs => hODE x s ⟨by linarith [hs.1],by linarith [hs.2]⟩) hΦ0
    (fun s hs x hx => phaseShell_radial a b hx (hΦr s hs x)) U.toContinuousLinearMap
  intro s hs x hx
  have hUx : U x∈phaseShell a b :=
    phaseShell_radial a b hx (hUD x x)
  change V (s,U x)=U (V (s,x))
  rw [hVe s hs _ hUx,hVe s hs x hx]
  exact homogeneousConeField_linear_invariant hF hF0 hD hJ U T hFT hUD hUA hTD hTA
    hc (mul_nonneg hs.1 hd) (lt_of_le_of_lt (by nlinarith [hs.2]) hdhalf)
    (phaseShell_nonzero ha hx)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Hamiltonian

variable {m : ℕ}

theorem homogeneousPolynomial_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℂ ∞ (homogeneousPolynomial a t) := by
  apply contDiff_pi.mpr
  rintro (_|((⟨b,i⟩|⟨i,j⟩)|j))
  · exact (contDiff_apply ℂ ℂ none).pow 2
  · exact (contDiff_apply ℂ ℂ none).mul (contDiff_apply ℂ ℂ (some i))
  · exact (contDiff_apply ℂ ℂ (some i)).mul (contDiff_apply ℂ ℂ (some j))
  · exact contDiff_const.mul (((contDiff_apply ℂ ℂ (some (some j))).pow 2).sub
      ((contDiff_apply ℂ ℂ (some none)).pow 2) |>.add
      (contDiff_const.mul ((contDiff_apply ℂ ℂ none).pow 2)))

theorem homogeneousPolynomial_homogeneous (a : Fin m → ℂ) (t : ℝ)
    (b : ℂ) (z : HomogeneousInput m) :
    homogeneousPolynomial a t (b•z)=b^2•homogeneousPolynomial a t z := by
  funext i
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  all_goals simp only [homogeneousPolynomial,Pi.smul_apply,smul_eq_mul]; ring

theorem homogeneousPolynomial_zero_iff (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    homogeneousPolynomial a t z=0 ↔ z=0 := by
  constructor
  · intro h
    funext i
    cases i with
    | none =>
      have hh := congrFun h none
      change z none^2=0 at hh
      exact eq_zero_of_pow_eq_zero hh
    | some i =>
      have hh := congrFun h (some (.inl (.inr (i,i))))
      change z (some i)*z (some i)=0 at hh
      exact (mul_self_eq_zero.mp hh)
  · rintro rfl
    funext i
    rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
    all_goals simp [homogeneousPolynomial]

theorem homogeneousPolynomial_euler (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    fderiv ℂ (homogeneousPolynomial a t) z z= (2:ℂ)•homogeneousPolynomial a t z := by
  have hf := (homogeneousPolynomial_smooth a t).differentiable (by simp) z
  have hf' : HasFDerivAt (homogeneousPolynomial a t)
      (fderiv ℂ (homogeneousPolynomial a t) z) ((1:ℂ)•z) := by
    simpa only [one_smul] using hf.hasFDerivAt
  have hd := hf'.comp_hasDerivAt (1:ℂ) ((hasDerivAt_id (1:ℂ)).smul_const z)
  have he : (fun b : ℂ => homogeneousPolynomial a t (b•z))=
      (fun b : ℂ => b^2•homogeneousPolynomial a t z) :=
    funext (fun b => homogeneousPolynomial_homogeneous a t b z)
  have hd' : HasDerivAt (fun b : ℂ => b^2•homogeneousPolynomial a t z)
      ((2:ℂ)•homogeneousPolynomial a t z) 1 := by
    convert! (((hasDerivAt_id (1:ℂ)).pow 2).smul_const (homogeneousPolynomial a t z)) using 1; simp
  simp only [Function.comp_def,id_eq] at hd
  rw [he] at hd
  simpa only [one_smul] using hd.unique hd'

theorem homogeneousCartesian_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℝ ∞ (homogeneousCartesian a t) :=
  (complexCartesian (ι := Option (NormalPolynomialIndex m))).contDiff.comp
    (((homogeneousPolynomial_smooth a t).restrict_scalars ℝ).comp
      (complexCartesian (ι := Option (Option (Fin m)))).symm.contDiff)

theorem homogeneousCartesian_nonzero (a : Fin m → ℂ) (t : ℝ)
    {z : PlanePhase (Option (Option (Fin m)))} (hz : z≠0) : homogeneousCartesian a t z≠0 := by
  intro h
  have hP : homogeneousPolynomial a t (complexCartesian.symm z)=0 :=
    complexCartesian.injective (h.trans (map_zero _).symm)
  have hh := (homogeneousPolynomial_zero_iff a t _).mp hP
  exact hz (by simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using congrArg complexCartesian hh)

theorem homogeneousCartesian_fderiv (a : Fin m → ℂ) (t : ℝ)
    (z v : PlanePhase (Option (Option (Fin m)))) :
    fderiv ℝ (homogeneousCartesian a t) z v=complexCartesian
      (fderiv ℂ (homogeneousPolynomial a t) (complexCartesian.symm z) (complexCartesian.symm v)) := by
  have hh := ((homogeneousPolynomial_smooth a t).differentiable (by simp)
    (complexCartesian.symm z)).hasFDerivAt.restrictScalars ℝ
  have hd := complexCartesian.toContinuousLinearMap.hasFDerivAt.comp z
    (hh.comp z (complexCartesian (ι := Option (Option (Fin m)))).symm.hasFDerivAt)
  exact congrArg (fun L => L v) hd.fderiv

theorem homogeneousCartesian_euler (a : Fin m → ℂ) (t : ℝ)
    (z : PlanePhase (Option (Option (Fin m)))) :
    fderiv ℝ (homogeneousCartesian a t) z z=(2:ℝ)•homogeneousCartesian a t z := by
  rw [homogeneousCartesian_fderiv,homogeneousPolynomial_euler]
  rw [show (2:ℂ)•homogeneousPolynomial a t (complexCartesian.symm z)=
    (2:ℝ)•homogeneousPolynomial a t (complexCartesian.symm z) by
      ext i; simp [Pi.smul_apply,Complex.real_smul]]
  exact map_smul _ _ _

theorem homogeneousCartesian_J (a : Fin m → ℂ) (t : ℝ)
    (z v : PlanePhase (Option (Option (Fin m)))) :
    fderiv ℝ (homogeneousCartesian a t) z (phaseJ v)=
      phaseJ (fderiv ℝ (homogeneousCartesian a t) z v) := by
  have hJ : complexCartesian.symm (phaseJ v)=Complex.I•complexCartesian.symm v := by
    apply complexCartesian.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply,complexCartesian_I]
  rw [homogeneousCartesian_fderiv,homogeneousCartesian_fderiv,hJ,map_smul,complexCartesian_I]

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem complexDiagonal_infinity_fixed (z : Option ι → ℂ) :
    complexDiagonal infinitySign z=z ↔ z none=0 := by
  constructor
  · intro h
    have h₀ := congrFun h none
    change (-1:ℂ)*z none=z none at h₀
    have hh : (2:ℂ)*z none=0 := by linear_combination -h₀
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  · intro h
    ext i
    cases i <;> simp [complexDiagonal_apply,infinitySign,h]

theorem phaseUnitDiagonal_infinity_fixed (z : PlanePhase (Option ι)) :
    phaseUnitDiagonal infinitySign infinitySign_unit z=z ↔
      complexCartesian.symm z none=0 := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  simp only [phaseUnitDiagonal_apply,phaseDiagonal_cartesian,
    ContinuousLinearEquiv.symm_apply_apply,complexCartesian.injective.eq_iff,
    complexDiagonal_infinity_fixed]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff BigOperators
open Hamiltonian

variable {m : ℕ}

theorem homogeneousInfinityOutputSign_unit (i : Option (NormalPolynomialIndex m)) :
    Complex.normSq (homogeneousInfinityOutputSign i)=1 := by
  rcases i with _|((_ |_)|_)
  all_goals norm_num [homogeneousInfinityOutputSign]

theorem homogeneousPolynomial_infinity (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    homogeneousPolynomial a t (complexDiagonal infinitySign z)=
      complexDiagonal homogeneousInfinityOutputSign (homogeneousPolynomial a t z) := by
  ext i
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  all_goals simp [homogeneousPolynomial,complexDiagonal_apply,infinitySign,
    homogeneousInfinityOutputSign]

theorem homogeneousCartesian_diagonal (a : Fin m → ℂ) (t : ℝ)
    (u : Option (Option (Fin m)) → ℂ) (hu : ∀ i,Complex.normSq (u i)=1)
    (v : Option (NormalPolynomialIndex m) → ℂ)
    (he : ∀ z,homogeneousPolynomial a t (complexDiagonal u z)=
      complexDiagonal v (homogeneousPolynomial a t z))
    (z : PlanePhase (Option (Option (Fin m)))) :
    homogeneousCartesian a t (phaseUnitDiagonal u hu z)=
      phaseDiagonal v (homogeneousCartesian a t z) := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  simp only [homogeneousCartesian,phaseUnitDiagonal_apply,phaseDiagonal_cartesian,
    ContinuousLinearEquiv.symm_apply_apply,he]

theorem homogeneousCartesian_circle (a : Fin m → ℂ) (t : ℝ) (ζ : ℂ)
    (hζ : Complex.normSq ζ=1) (z : PlanePhase (Option (Option (Fin m)))) :
    homogeneousCartesian a t (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
      phaseDiagonal (fun _ => ζ^2) (homogeneousCartesian a t z) := by
  apply homogeneousCartesian_diagonal
  intro z
  change homogeneousPolynomial a t (ζ•z)=ζ^2•homogeneousPolynomial a t z
  exact homogeneousPolynomial_homogeneous a t ζ z

theorem homogeneousCartesian_infinity (a : Fin m → ℂ) (t : ℝ)
    (z : PlanePhase (Option (Option (Fin m)))) :
    homogeneousCartesian a t (phaseUnitDiagonal infinitySign infinitySign_unit z)=
      phaseDiagonal homogeneousInfinityOutputSign (homogeneousCartesian a t z) :=
  homogeneousCartesian_diagonal a t infinitySign infinitySign_unit homogeneousInfinityOutputSign
    (homogeneousPolynomial_infinity a t) z

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricRelativeShellFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open Hamiltonian
section
variable {m : ℕ}

theorem exists_quadric_relative_shell_map_bp240_oai (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ f g : PlanePhase (Option (Option (Fin m))) → PlanePhase (Option (Option (Fin m))),
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
      LeftInverse g f ∧ RightInverse g f ∧
      (∀ z,phaseSq (f z)=phaseSq z) ∧ (∀ z,phaseSq (g z)=phaseSq z) ∧
      (∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
        f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
          phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z)) ∧
      (∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
        g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
          phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z)) ∧
      (∀ z,phaseSq z=1 → (complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0)) ∧
      (∀ z,phaseSq z=1 → (complexCartesian.symm (g z) none=0 ↔ complexCartesian.symm z none=0)) ∧
      ∀ z∈phaseShell (1/2:ℝ) 2,∀ v w,
        euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c d) (f z)
            (fderiv ℝ f z v) (fderiv ℝ f z w)=
          euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c 0) z v w := by
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hΦr,hΦω,V,hV,hODE,hVe⟩ :=
    exists_homogeneousCone_shell_flow (homogeneousCartesian_smooth a t)
      (fun _ hz => homogeneousCartesian_nonzero a t hz) (homogeneousCartesian_euler a t)
      (homogeneousCartesian_J a t) (b := 2) hc hd hdhalf (by norm_num : 0<(1/2:ℝ))
  have h1 : (1:ℝ)∈Icc (0:ℝ) 1 := by simp
  let f := fun z => Φ (1,z)
  let g := fun z => Ψ (1,z)
  have hfg : LeftInverse g f := fun z => (hΦi 1 h1 z).1
  have hgf : RightInverse g f := fun z => (hΦi 1 h1 z).2
  have hfr : ∀ z,phaseSq (f z)=phaseSq z := hΦr 1 h1
  have hgr (z) : phaseSq (g z)=phaseSq z := by
    have h := hfr (g z)
    rw [hgf z] at h
    exact h.symm
  have hK (z : PlanePhase (Option (Option (Fin m)))) (hz : phaseSq z=1) :
      z∈phaseShell (1/2:ℝ) 2 := by
    change (1/2:ℝ)≤phaseSq z ∧ phaseSq z≤2
    rw [hz]
    norm_num
  have heq (U : PlanePhase (Option (Option (Fin m))) ≃L[ℝ] PlanePhase (Option (Option (Fin m))))
      (T : PlanePhase (Option (NormalPolynomialIndex m)) →L[ℝ] PlanePhase (Option (NormalPolynomialIndex m)))
      (he : ∀ z,homogeneousCartesian a t (U z)=T (homogeneousCartesian a t z))
      (hU₁ : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
      (hU₂ : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
      (hT₁ : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
      (hT₂ : ∀ z v,phaseArea (T z) (T v)=phaseArea z v)
      (z) (hz : phaseSq z=1) : f (U z)=U (f z) :=
    homogeneousCone_shell_flow_linear_equivariant (homogeneousCartesian_smooth a t)
      (fun _ hz => homogeneousCartesian_nonzero a t hz) (homogeneousCartesian_euler a t)
      (homogeneousCartesian_J a t) hc hd hdhalf (by norm_num : 0<(1/2:ℝ))
      hΦ0 hΦr hV hODE hVe U T he hU₁ hU₂ hT₁ hT₂ 1 h1 z (hK z hz)
  have hfζ (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z) (hz : phaseSq z=1) :
      f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
        phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z) := by
    have hζ₂ : Complex.normSq (ζ^2)=1 := by rw [map_pow,hζ,one_pow]
    exact heq _ (phaseDiagonal (fun _ => ζ^2)) (homogeneousCartesian_circle a t ζ hζ)
      (phaseDiagonal_dot _ (fun _ => hζ)) (phaseDiagonal_area _ (fun _ => hζ))
      (phaseDiagonal_dot _ (fun _ => hζ₂)) (phaseDiagonal_area _ (fun _ => hζ₂)) z hz
  have hgζ (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z) (hz : phaseSq z=1) :
      g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
        phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z) := by
    apply hfg.injective
    rw [hgf,hfζ ζ hζ (g z) ((hgr z).trans hz),hgf]
  have hfinf (z) (hz : phaseSq z=1) :
      complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0 := by
    have he := heq (phaseUnitDiagonal infinitySign infinitySign_unit)
      (phaseDiagonal homogeneousInfinityOutputSign) (homogeneousCartesian_infinity a t)
      (phaseDiagonal_dot _ infinitySign_unit) (phaseDiagonal_area _ infinitySign_unit)
      (phaseDiagonal_dot _ homogeneousInfinityOutputSign_unit)
      (phaseDiagonal_area _ homogeneousInfinityOutputSign_unit) z hz
    rw [←phaseUnitDiagonal_infinity_fixed,←phaseUnitDiagonal_infinity_fixed]
    constructor
    · intro h
      apply hfg.injective
      exact he.trans h
    · intro h
      exact (he.symm.trans (congrArg f h))
  have hginf (z) (hz : phaseSq z=1) :
      complexCartesian.symm (g z) none=0 ↔ complexCartesian.symm z none=0 := by
    have h := hfinf (g z) ((hgr z).trans hz)
    rw [hgf z] at h
    exact h.symm
  refine ⟨f,g,hΦ.comp (contDiff_const.prodMk contDiff_id),hΨ.comp (contDiff_const.prodMk contDiff_id),
    hfg,hgf,hfr,hgr,hfζ,hgζ,hfinf,hginf,?_⟩
  intro z hz v w
  simpa only [one_mul] using hΦω 1 h1 z hz v w

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map_bp240_oai := @OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map_bp240_oai
