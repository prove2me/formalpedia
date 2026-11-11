-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:17.078714+00:00
-- url     : https://prove2.me/submissions/dac0dd6e-6c94-43fa-90c8-036a3b4fd6dd

import Mathlib
import Definitions.Def_OAIQ240Bp015
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_manifold_exact_sublevel_moser_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_BackgroundDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_clm_eval {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → E →L[ℝ] F} {x : E} (hg : DifferentiableAt ℝ g x) (u v : E) :
    fderiv ℝ (fun y => g y v) x u = fderiv ℝ g x u v := by
  rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
  simp



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

section
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bilinearComp_isInvertible {A : E →L[ℝ] E →L[ℝ] ℝ} {C : E →L[ℝ] E}
    (hA : A.IsInvertible) (hC : C.IsInvertible) : (A.bilinearComp C C).IsInvertible := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨c,rfl⟩ := hC
  refine ⟨(c.trans a).trans (c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)),?_⟩
  ext u v
  rfl


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldMoserField
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
open scoped NNReal
open MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartTwoForm_isInvertible {Ω : ManifoldTwoForm E M} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : (Ω ((extChartAt 𝓘(ℝ,E) c).symm y)).IsInvertible) :
    (chartTwoForm Ω c y).IsInvertible := by
  apply bilinearComp_isInvertible hΩ
  apply ContinuousLinearMap.IsInvertible.inverse
  convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
    ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
  all_goals try with_reducible_and_instances rfl

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SymplecticFamily
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem hamiltonianField_contraction {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : A.IsInvertible)
    (H : ℝ × E → ℝ) (p : ℝ × E) (w : E) :
    A (hamiltonianField A H p) w = -fderiv ℝ H p (0,w) := by
  exact congrArg (fun α : E →L[ℝ] ℝ => α w) (formMoserField_solve (fun _ => hA) p)



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

theorem euclideanPullbackOneForm_contDiffAt
    {α : ℝ → ManifoldOneForm E M} {g : F → M} {p : ℝ × F}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (euclideanPullbackOneForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := ((hα c).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩)).comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  have hsm := hform.clm_comp hder
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackOneForm_chart (hq.mdifferentiableAt (by simp)) hqc


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



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ChartSupportedDensity
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
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem SmoothOneFormFamily.spatial_smooth {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) (p : P) (c : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    ContDiffAt ℝ ∞ (chartOneForm (α p) c) y :=
  ((hα c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds ⟨mem_univ p,hy⟩)).comp y
    (contDiffAt_const.prodMk contDiffAt_id)


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



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
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartOneForm_manifoldPullback {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target) :
    chartOneForm (manifoldPullbackOneForm α e p.1) b p.2 =
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := ((he.mdifferentiable (by simp) _).hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackOneForm,hd,chartOneForm,manifoldPullbackOneForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v
  rfl

theorem manifoldPullbackOneForm_smooth {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (b : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) b q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,F) b).target) := by
  intro p hp
  have hg := he.contMDiffAt.comp p.2 ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2))
  apply ((euclideanPullbackOneForm_contDiffAt hα hg).congr_of_eventuallyEq _).contDiffWithinAt
  have hh := continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2)
  filter_upwards [hh] with q hq
  exact chartOneForm_manifoldPullback he hq

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartOneForm_transition {α : ManifoldOneForm E M} {b c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    chartOneForm α b y =
      staticPullbackOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have he := euclideanPullbackOneForm_chart (α := fun _ => α) (p := (0,y)) hi hc
  simpa only [euclideanPullbackOneForm,chartOneForm,chartDifferential_inverse hy,
    staticPullbackOneForm,Function.comp_apply] using he

theorem chartOneForm_exterior_transition {α : ManifoldOneForm E M} {b c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source)
    (hα : ContDiffAt ℝ ∞ (chartOneForm α c)
      (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))) :
    euclideanExteriorOneForm (chartOneForm α b) y =
      (euclideanExteriorOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y) := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have ht : ContDiffAt ℝ ∞
      (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y :=
    (ho.comp y hi).contDiffAt
  have he : chartOneForm α b =ᶠ[𝓝 y]
      staticPullbackOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy,
      hi.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)]
      with z hz hzc
    exact chartOneForm_transition hz hzc
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c)
          (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm)) y := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := staticPullbackOneForm_exterior hα ht

theorem manifoldExteriorOneForm_chart {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {b : M} {y : E} (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target) :
    chartTwoForm (manifoldExteriorOneForm α) b y =
      euclideanExteriorOneForm (chartOneForm α b) y := by
  let x := (extChartAt 𝓘(ℝ,E) b).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := x)
    (by simpa only [extChartAt_source] using hx)
  let A : E →L[ℝ] E := (chartDifferential x x).comp
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) b).symm y)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) x ∘ (extChartAt 𝓘(ℝ,E) b).symm) A y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (ho.hasMFDerivAt.comp y hi.hasMFDerivAt)
  have he := hf.fderiv
  dsimp only [A,chartDifferential] at he
  rw [chartOneForm_exterior_transition hy hx ((hα x).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds
      ((extChartAt 𝓘(ℝ,E) x).map_source hx)))]
  change fderiv ℝ (extChartAt 𝓘(ℝ,E) x ∘ (extChartAt 𝓘(ℝ,E) b).symm) y = _ at he
  rw [he]
  simp only [chartTwoForm,manifoldExteriorOneForm,chartDifferential_inverse hy]
  rfl

end
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

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem parameterEuclideanPullbackOneForm_contDiffAt
    {α : P → ManifoldOneForm E M} {g : F → M} {p : P × F}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (α q.1) (g p.2) q.2)
      (p.1,extChartAt 𝓘(ℝ,E) (g p.2) (g p.2)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (parameterEuclideanPullbackOneForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : P × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := hα.comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  apply (hform.clm_comp hder).congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackOneForm_chart (α := fun _ => α q.1) (p := (0,q.2))
    (hq.mdifferentiableAt (by simp)) hqc

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

section

variable {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_fst_smooth : ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,E) ∞
    (Prod.fst : M × V → M) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact contMDiff_fst

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_snd_smooth : ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,V) ∞
    (Prod.snd : M × V → V) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact contMDiff_snd

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_fst_derivative (z : M × V) :
    mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,E) (Prod.fst : M × V → M) z=
      ContinuousLinearMap.fst ℝ E V := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact mfderiv_fst

variable [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem productHorizontalLift_chart (Γ : V → ManifoldOneForm E M) (c : M × V)
    {y : E × V} (hy : y∈(extChartAt 𝓘(ℝ,E × V) c).target) :
    chartOneForm (productHorizontalLift Γ) c y=
      parameterEuclideanPullbackOneForm Γ
        (Prod.fst ∘ (extChartAt 𝓘(ℝ,E × V) c).symm)
        (((extChartAt 𝓘(ℝ,E × V) c).symm y).2,y) := by
  let v := ((extChartAt 𝓘(ℝ,E × V) c).symm y).2
  have he : chartOneForm (productHorizontalLift Γ) c y=
      chartOneForm (manifoldPullbackOneForm (E := E) (F := E × V)
        (fun _ => Γ v) (Prod.fst : M × V → M) 0) c y := by
    simp only [chartOneForm,productHorizontalLift,manifoldPullbackOneForm,
      manifoldMapDifferential,flatProduct_fst_derivative]
    rfl
  exact he.trans (chartOneForm_manifoldPullback (α := fun _ => Γ v)
    (p := (0,y)) flatProduct_fst_smooth hy)

theorem productHorizontalLift_smooth {Γ : P × V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (fun p => productHorizontalLift (fun v => Γ (p,v))) := by
  intro c q hq
  let g : E × V → M := Prod.fst ∘ (extChartAt 𝓘(ℝ,E × V) c).symm
  let v : E × V → V := Prod.snd ∘ (extChartAt 𝓘(ℝ,E × V) c).symm
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E × V)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hg : ContMDiffAt 𝓘(ℝ,E × V) 𝓘(ℝ,E) ∞ g q.2 :=
    flatProduct_fst_smooth.contMDiffAt.comp q.2 hi
  have hv : ContDiffAt ℝ ∞ v q.2 :=
    (flatProduct_snd_smooth.contMDiffAt.comp q.2 hi).contDiffAt
  have hx : ((q.1,v q.2),extChartAt 𝓘(ℝ,E) (g q.2) (g q.2))∈
      univ ×ˢ (extChartAt 𝓘(ℝ,E) (g q.2)).target :=
    ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) (g q.2)).map_source (mem_extChartAt_source _)⟩
  have hs := parameterEuclideanPullbackOneForm_contDiffAt
    (α := Γ) (p := ((q.1,v q.2),q.2))
    ((hΓ (g q.2)).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target _)).mem_nhds hx)) hg
  have hc := hs.comp q ((contDiffAt_fst.prodMk (hv.comp q contDiffAt_snd)).prodMk contDiffAt_snd)
  apply (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E × V)) c).mem_nhds hq.2)] with z hz
  exact productHorizontalLift_chart (fun w => Γ (z.1,w)) c hz

end

section

variable {F E V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem flatProductMap_smoothAt {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    ContMDiffAt 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) ∞ (flatProductMap g) x := by
  have h := hg.prodMap (contMDiffAt_id (I := 𝓘(ℝ,V)) (x := x.2))
  simp +instances only [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
  exact h

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem flatProductMap_derivative {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    mfderiv 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) (flatProductMap g) x=
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V) := by
  have hf := (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : F × V → F)).contMDiff.contMDiffAt (x := x)
  have hs := (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : F × V → V)).contMDiff.contMDiffAt (x := x)
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  have hd := mfderiv_prodMk (I := 𝓘(ℝ,F × V)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,V))
    (f := g ∘ Prod.fst) (g := Prod.snd) (x := x)
    ((hg.comp x hf).mdifferentiableAt (by simp)) (hs.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ,F × V) ((𝓘(ℝ,E)).prod 𝓘(ℝ,V))
    (fun y : F × V => (g y.1,y.2)) x=_
  apply hd.trans
  erw [mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_fst,fderiv_snd]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem productHorizontalLift_pullback_apply (Γ : V → ManifoldOneForm E M)
    {g : F → M} {x : F × V} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1)
    (w : F × V) :
    euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,x) w=
      euclideanPullbackOneForm (fun _ => Γ x.2) g (0,x.1) w.1 := by
  change Γ x.2 (g x.1)
    ((mfderiv 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) (flatProductMap g) x w).1)=
      Γ x.2 (g x.1) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1 w.1)
  rw [flatProductMap_derivative hg]
  rfl

theorem productHorizontalLift_exterior_pullback {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    euclideanExteriorOneForm
      (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,y)) x=
      (manifoldExteriorOneForm (productHorizontalLift Γ) (flatProductMap g x)).bilinearComp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V))
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V)) := by
  have hfam : SmoothOneFormFamily (fun _ : ℝ => productHorizontalLift Γ) := by
    apply productHorizontalLift_smooth (Γ := fun p : ℝ × V => Γ p.2)
    intro c
    have hm : ContDiffOn ℝ ∞ (fun p : (ℝ × V) × E => (p.1.2,p.2))
        (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
    exact (hΓ c).comp hm (fun _ hp => ⟨mem_univ _,hp.2⟩)
  have he := euclidean_manifold_pullback_exterior_at (flatProductMap_smoothAt hg)
    (hfam.spatial_smooth 0 (flatProductMap g x) (mem_extChartAt_target _))
  simpa only [manifoldMapDifferential,flatProductMap_derivative hg] using he

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem SmoothOneFormFamily.add {α β : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) (hβ : SmoothOneFormFamily β) :
    SmoothOneFormFamily (fun p => α p+β p) := by
  intro c
  simpa only [chartOneForm_add] using (hα c).add (hβ c)

theorem SmoothOneFormFamily.comp {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) {f : Q → P} (hf : ContDiff ℝ ∞ f) :
    SmoothOneFormFamily (α ∘ f) := by
  intro c
  have hm : ContDiffOn ℝ ∞ (fun q : Q × E => (f q.1,q.2))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    ((hf.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
  exact (hα c).comp hm (fun _ hq => ⟨mem_univ _,hq.2⟩)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

theorem pathSpatialExterior_eq_slice {Γ : ℝ × E → E →L[ℝ] ℝ} {p : ℝ × E}
    (hΓ : DifferentiableAt ℝ Γ p) :
    pathSpatialExterior Γ p = euclideanExteriorOneForm (fun y => Γ (p.1,y)) p.2 := by
  have hi : HasFDerivAt (fun y : E => (p.1,y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hh : HasFDerivAt Γ (fderiv ℝ Γ p) (p.1,p.2) := hΓ.hasFDerivAt
  have hd := (hh.comp p.2 hi).fderiv
  change fderiv ℝ (fun y => Γ (p.1,y)) p.2 = _ at hd
  unfold euclideanExteriorOneForm
  rw [hd]
  rfl

theorem manifoldExteriorOneForm_path_chart {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {c : M} {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartTwoForm (manifoldExteriorOneForm (Γ t)) c y =
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) (t,y) := by
  rw [manifoldExteriorOneForm_chart (fun b z hz => (hΓ.spatial_smooth t b hz).contDiffWithinAt) hy]
  exact (pathSpatialExterior_eq_slice ((hΓ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ t,hy⟩))
      |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).symm

theorem manifoldExteriorOneForm_path_smooth {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothTwoFormFamily (fun t => manifoldExteriorOneForm (Γ t)) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((pathSpatialExterior_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  exact manifoldExteriorOneForm_path_chart hΓ hq.2


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldExteriorAlgebra
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_manifold_cutoff {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ (∀ x, χ x ∈ Icc (0:ℝ) 1) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨D,hD,hKD,hDU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχ⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hK.isClosed hKD
  have hs : tsupport (χ : M → ℝ) ⊆ D :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hχ0 x hn)) hD.isClosed
  exact ⟨χ,χ.contMDiff,HasCompactSupport.of_support_subset_isCompact hD
    ((subset_tsupport χ).trans hs),hs.trans hDU,hχ1,hχ⟩


end


open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators

section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_add_at {α β : ManifoldOneForm E M} {x : M}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x))
    (hβ : ContDiffAt ℝ ∞ (chartOneForm β x) (extChartAt 𝓘(ℝ,E) x x)) :
    manifoldExteriorOneForm (α+β) x=manifoldExteriorOneForm α x+manifoldExteriorOneForm β x := by
  have he : chartOneForm (α+β) x=chartOneForm α x+chartOneForm β x :=
    funext (chartOneForm_add α β x)
  simp only [manifoldExteriorOneForm,he,euclideanExteriorOneForm_add
    (hα.differentiableAt (by simp)) (hβ.differentiableAt (by simp))]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rfl

end

section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem chartOneForm_model (α : V → V →L[ℝ] ℝ) (c y : V) : chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem manifoldExteriorOneForm_model (α : V → V →L[ℝ] ℝ) (x : V) :
    manifoldExteriorOneForm α x=euclideanExteriorOneForm α x := by
  rw [manifoldExteriorOneForm,show chartOneForm α x=α from funext (chartOneForm_model α x)]
  simp only [chartDifferential,
    extChartAt_model_space_eq_id,PartialEquiv.refl_coe,mfderiv_eq_fderiv,fderiv_id,id_eq]
  ext u v
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem linearLiouville_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ) : ContDiff ℝ ∞ (linearLiouville Ω) :=
  Ω.contDiff.const_smul _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem linearLiouville_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ) (hs : ∀ u v,Ω u v= -Ω v u) (x : V) :
    manifoldExteriorOneForm (linearLiouville Ω) x=Ω := by
  rw [manifoldExteriorOneForm_model]
  have hd : fderiv ℝ (linearLiouville Ω) x=(1/2:ℝ) • Ω :=
    ((Ω.hasFDerivAt).const_smul (1/2:ℝ)).fderiv
  simp only [euclideanExteriorOneForm,hd]
  ext u v
  change (1/2:ℝ)*Ω u v-(1/2:ℝ)*Ω v u=Ω u v
  rw [hs v u]
  ring

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem flatProduct_snd_derivative (z : M × V) :
    mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,V) (Prod.snd : M × V → V) z=
      ContinuousLinearMap.snd ℝ E V := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact mfderiv_snd

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem productVerticalLiouville_apply (Ω : V →L[ℝ] V →L[ℝ] ℝ) (z : M × V) (v : E × V) :
    productVerticalLiouville Ω z v=(1/2:ℝ)*Ω z.2 v.2 := by
  simp only [productVerticalLiouville,manifoldPullbackOneForm,manifoldMapDifferential,
    flatProduct_snd_derivative,ContinuousLinearMap.comp_apply]
  rfl

 theorem productVerticalLiouville_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => (productVerticalLiouville Ω : ManifoldOneForm (E × V) (M × V))) := by
  exact manifoldPullbackOneForm_smooth (α := fun _ => linearLiouville Ω)
    (e := (Prod.snd : M × V → V)) flatProduct_snd_smooth (fun c => by
    simpa only [chartOneForm_model,Function.comp_def] using
      ((linearLiouville_smooth Ω).comp (contDiff_snd (E := ℝ))).contDiffOn)

 theorem productVerticalLiouville_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hs : ∀ u v,Ω u v= -Ω v u) (z : M × V) :
    manifoldExteriorOneForm (productVerticalLiouville Ω) z=
      Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V) (ContinuousLinearMap.snd ℝ E V) := by
  have ha : ContDiffAt ℝ ∞ (chartOneForm (linearLiouville Ω) z.2)
      (extChartAt 𝓘(ℝ,V) z.2 z.2) := by
    rw [show chartOneForm (linearLiouville Ω) z.2=linearLiouville Ω from
      funext (chartOneForm_model (linearLiouville Ω) z.2)]
    exact (linearLiouville_smooth Ω).contDiffAt
  rw [productVerticalLiouville,manifold_pullback_exterior_at ha flatProduct_snd_smooth.contMDiffAt]
  simp only [manifoldPullbackTwoForm,linearLiouville_exterior Ω hs,manifoldMapDifferential,
    flatProduct_snd_derivative]

 theorem productCouplingPrimitive_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (fun t => productCouplingPrimitive Ω (fun v => Γ (t,v))) :=
  (productVerticalLiouville_smooth Ω).add (productHorizontalLift_smooth hΓ)

 theorem productCouplingPrimitive_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hs : ∀ u v,Ω u v= -Ω v u) {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × V) :
    manifoldExteriorOneForm (productCouplingPrimitive Ω Γ) z=globalHorizontalCoupling Ω Γ z := by
  have hg : SmoothOneFormFamily (fun q : ℝ × V => Γ q.2) := hΓ.comp contDiff_snd
  have hh := productHorizontalLift_smooth hg
  rw [productCouplingPrimitive,manifoldExteriorOneForm_add_at
    ((productVerticalLiouville_smooth Ω).spatial_smooth 0 z (mem_extChartAt_target z))
    (hh.spatial_smooth 0 z (mem_extChartAt_target z)),productVerticalLiouville_exterior Ω hs]
  rfl

end

section
variable {ι : Type*} [Fintype ι]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem verticalLiouville_apply (z : M × PlanePhase ι) (v : E × PlanePhase ι) :
    verticalLiouville z v=(1/2:ℝ)*phaseArea z.2 v.2 := by
  change standardLiouville z.2 (mfderiv 𝓘(ℝ,E × PlanePhase ι) 𝓘(ℝ,PlanePhase ι) Prod.snd z v)=_
  rw [flatProduct_snd_derivative]
  rfl

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold MeasureTheory

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
 theorem manifoldExteriorOneForm_congr_germ {α β : ManifoldOneForm E M} {x : M}
    (h : α =ᶠ[𝓝 x] β) : manifoldExteriorOneForm α x=manifoldExteriorOneForm β x := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have ht := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
    ((isOpen_extChartAt_target x).mem_nhds ht)).continuousAt
  change Filter.Tendsto _ _ (𝓝 ((extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))) at hi
  rw [(extChartAt 𝓘(ℝ,E) x).left_inv hx] at hi
  have he : chartOneForm α x =ᶠ[𝓝 (extChartAt 𝓘(ℝ,E) x x)] chartOneForm β x := by
    filter_upwards [hi.eventually h] with y hy
    exact congrArg (fun L : E →L[ℝ] ℝ => L.comp
      (chartDifferential x ((extChartAt 𝓘(ℝ,E) x).symm y)).inverse) hy
  simp only [manifoldExteriorOneForm,euclideanExteriorOneForm,he.fderiv_eq]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_AnnularFinalPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {M V ι : Type*}

 theorem baseFiber_bounds {a c : ι → ℝ} (h : ∀ i,a i < c i) :
    ∀ i,baseFiberInner a i<baseFiberOuter c i := by
  rintro (_|i)
  · norm_num [baseFiberInner,baseFiberOuter]
  · exact h i

 theorem baseFiber_domain (χ : M → ℝ) (μ : ι → V → ℝ) (c : ι → ℝ) :
    {z | ∀ i,baseFiberMoment χ μ i z≤baseFiberOuter c i}=
      {x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v ≤ c i} := by
  ext z
  simp only [mem_ofPred_eq,Option.forall,baseFiberMoment,baseFiberOuter,mem_prod]
  constructor
  · rintro ⟨hb,hy⟩
    exact ⟨by linarith,hy⟩
  · rintro ⟨hb,hy⟩
    exact ⟨by linarith,hy⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem baseFiberMoment_smooth [NormedAddCommGroup V] [NormedSpace ℝ V]
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ)
    {μ : ι → V → ℝ} (hμ : ∀ i,ContDiff ℝ ∞ (μ i)) :
    ∀ i,ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) ∞ (baseFiberMoment χ μ i) := by
  rintro (_|i)
  · exact (hχ.comp flatProduct_fst_smooth).neg
  · exact (hμ i).contMDiff.comp flatProduct_snd_smooth

variable [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem exists_base_moser_cutoff {S D : Set M} (hS : IsCompact S) (hSD : S⊆interior D) :
    ∃ χ : M → ℝ,ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ ∧
      IsCompact {x | (1/2:ℝ)≤χ x} ∧ {x | (1/2:ℝ)≤χ x}⊆D ∧
      (∀ x∈S,χ x=1) := by
  obtain ⟨χ,hχ,hχc,hχs,hχ1,_⟩ := exists_smooth_manifold_cutoff (E := E) hS isOpen_interior hSD
  have hc : IsClosed {x | (1/2:ℝ)≤χ x} := isClosed_le continuous_const hχ.continuous
  have hh : {x | (1/2:ℝ)≤χ x}⊆tsupport χ := by
    intro x hx
    apply subset_tsupport χ
    change χ x≠0
    have h : (1/2:ℝ)≤χ x := hx
    linarith
  exact ⟨χ,hχ,hχc.isCompact.of_isClosed_subset hc hh,
    hh.trans (hχs.trans interior_subset),hχ1.self_of_nhdsSet⟩

end

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

 theorem horizontalModel_exterior_vertical
    {A : E × V → E →L[ℝ] ℝ} {x : E × V} (hA : DifferentiableAt ℝ A x)
    (Z : V) (w : E × V) :
    euclideanExteriorOneForm (fun q => (A q).comp (ContinuousLinearMap.fst ℝ E V)) x (0,Z) w=
      fderiv ℝ (fun v => A (x.1,v)) x.2 Z w.1 := by
  let α : (E × V) → (E × V) →L[ℝ] ℝ := fun q => (A q).comp (ContinuousLinearMap.fst ℝ E V)
  have hα : DifferentiableAt ℝ α x := hA.clm_comp (differentiableAt_const _)
  have hz : (fun q => α q (0,Z))=fun _ => (0:ℝ) := by funext q; simp [α]
  have hw : (fun q => α q w)=fun q => A q w.1 := rfl
  have hd : HasFDerivAt (fun v : V => (x.1,v)) (ContinuousLinearMap.inr ℝ E V) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hs := hA.hasFDerivAt.comp x.2 hd
  have he := congrArg (fun L : V →L[ℝ] E →L[ℝ] ℝ => L Z w.1) hs.fderiv
  change fderiv ℝ (fun v => A (x.1,v)) x.2 Z w.1=fderiv ℝ A x (0,Z) w.1 at he
  change fderiv ℝ α x (0,Z) w-fderiv ℝ α x w (0,Z)=_
  rw [← fderiv_clm_eval hα,← fderiv_clm_eval hα,hz,hw,fderiv_const_apply,
    zero_apply,sub_zero]
  rw [(hA.hasFDerivAt.clm_apply (hasFDerivAt_const w.1 x)).fderiv]
  simpa using he.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem SmoothOneFormFamily.parameter_contDiffAt {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (v : V) (x : M) : ContDiffAt ℝ ∞ (fun w => Γ w x) v := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hcam := ((hΓ x).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      (show (v,extChartAt 𝓘(ℝ,E) x x)∈univ ×ˢ (extChartAt 𝓘(ℝ,E) x).target from ⟨mem_univ v,hxt⟩))).comp v
        (contDiffAt_id.prodMk contDiffAt_const)
  have hsm := hcam.clm_comp (contDiffAt_const (c := chartDifferential x x))
  apply hsm.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun w => by
    simpa only [(extChartAt 𝓘(ℝ,E) x).left_inv hx,Function.comp_def,id_eq] using
      (chartOneForm_reconstruct_target (α := Γ w) hxt).symm)

 theorem productHorizontalLift_exterior_vertical {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × V) (Z : V)
    (hZ : fderiv ℝ (fun v => Γ v z.1) z.2 Z=0) (w : E × V) :
    manifoldExteriorOneForm (productHorizontalLift Γ) z (0,Z) w=0 := by
  let c := z.1
  let y := extChartAt 𝓘(ℝ,E) c c
  have hc := mem_extChartAt_source (I := 𝓘(ℝ,E)) c
  have hy := (extChartAt 𝓘(ℝ,E) c).map_source hc
  have he := (extChartAt 𝓘(ℝ,E) c).left_inv hc
  have hg := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hy)
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm y
  have hC : (chartDifferential (E := E) c c).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hc using 1
    all_goals try with_reducible_and_instances rfl
  have hD : D (chartDifferential c c w.1)=w.1 := by
    have hDi := chartDifferential_inverse hy
    rw [he] at hDi
    change (chartDifferential (E := E) c c).inverse=D at hDi
    rw [← hDi]
    exact hC.inverse_apply_self _
  let A : E × V → E →L[ℝ] ℝ := fun q => chartOneForm (Γ q.2) c q.1
  have hA : ContDiffAt ℝ ∞ A (y,z.2) :=
    ((hΓ c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds
      ⟨mem_univ _,hy⟩)).comp (y,z.2) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hAz : fderiv ℝ (fun v => A (y,v)) z.2 Z=0 := by
    have hparam := (hΓ.parameter_contDiffAt z.2 c).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hh : (fun v => A (y,v))=fun v => (Γ v c).comp (chartDifferential c c).inverse := by
      funext v
      simp only [A,chartOneForm,y,he]
    rw [hh]
    have hd := hparam.hasFDerivAt.clm_comp (hasFDerivAt_const (chartDifferential (E := E) c c).inverse z.2)
    rw [hd.fderiv]
    ext u
    simp [hZ,c]
  have hp : (fun q => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ)
        (flatProductMap (extChartAt 𝓘(ℝ,E) c).symm) (0,q)) =ᶠ[𝓝 (y,z.2)]
      fun q => (A q).comp (ContinuousLinearMap.fst ℝ E V) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target c).mem_nhds hy)] with q hq
    have hqg := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
      ((isOpen_extChartAt_target c).mem_nhds hq)
    apply ContinuousLinearMap.ext
    intro v
    rw [productHorizontalLift_pullback_apply _ hqg]
    simp only [euclideanPullbackOneForm,chartOneForm,chartDifferential_inverse hq,A,
      ContinuousLinearMap.comp_apply]
    rfl
  have hpb := productHorizontalLift_exterior_pullback hΓ hg (x := (y,z.2))
  have hz := horizontalModel_exterior_vertical (hA.differentiableAt (by simp)) Z
    (chartDifferential c c w.1,w.2)
  have hh := congrArg (fun B : (E × V) →L[ℝ] (E × V) →L[ℝ] ℝ =>
    B (0,Z) (chartDifferential c c w.1,w.2)) hpb
  have hpe : euclideanExteriorOneForm (fun q => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ)
      (flatProductMap (extChartAt 𝓘(ℝ,E) c).symm) (0,q)) (y,z.2)=
      euclideanExteriorOneForm (fun q => (A q).comp (ContinuousLinearMap.fst ℝ E V)) (y,z.2) := by
    unfold euclideanExteriorOneForm
    rw [hp.fderiv_eq]
  rw [hpe,hz,hAz,zero_apply] at hh
  have hpoint : flatProductMap (extChartAt 𝓘(ℝ,E) c).symm (y,z.2)=z := by
    simp [flatProductMap,y,c]
  rw [hpoint] at hh
  change 0=manifoldExteriorOneForm (productHorizontalLift Γ) z (D 0,Z)
    (D (chartDifferential c c w.1),w.2) at hh
  simpa only [map_zero,hD,Prod.mk.eta] using hh.symm

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
open scoped Manifold
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E →L[ℝ] ℝ}

theorem autonomousField_contraction (hA : A.IsInvertible) {f : E → ℝ}
    (hf : Differentiable ℝ f) (x v : E) :
    A (autonomousField A f x) v = -fderiv ℝ f x v := by
  rw [autonomousField,hamiltonianField_contraction hA]
  have hd := (hf x).hasFDerivAt.comp (0,x) (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt
  change HasFDerivAt (fun p : ℝ × E => f p.2) _ _ at hd
  change -fderiv ℝ (fun p : ℝ × E => f p.2) (0,x) (0,v) = _
  rw [hd.fderiv]
  rfl

end
section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem globalHorizontalCoupling_face
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible)
    {μ : V → ℝ} (hμ : ContDiff ℝ ∞ μ) {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × V)
    (hZ : fderiv ℝ (fun v => Γ v z.1) z.2 (autonomousField Ω μ z.2)=0) :
    globalHorizontalCoupling Ω Γ z (0,autonomousField Ω μ z.2)=
      -mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) (fun y : M × V => μ y.2) z := by
  have hd : mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) (fun y : M × V => μ y.2) z=
      (fderiv ℝ μ z.2).comp (ContinuousLinearMap.snd ℝ E V) := by
    simpa only [Function.comp_def,flatProduct_snd_derivative,mfderiv_eq_fderiv] using!
      (mfderiv_comp z (hμ.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (flatProduct_snd_smooth.contMDiffAt.mdifferentiableAt (by simp)))
  apply ContinuousLinearMap.ext
  intro w
  rw [hd]
  change Ω (autonomousField Ω μ z.2) w.2+
    manifoldExteriorOneForm (productHorizontalLift Γ) z (0,autonomousField Ω μ z.2) w=
      -fderiv ℝ μ z.2 w.2
  rw [productHorizontalLift_exterior_vertical hΓ z _ hZ w,add_zero]
  exact autonomousField_contraction hΩ (hμ.differentiable (by simp)) z.2 w.2

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem productCouplingPrimitive_vertical_value
    (Ω : V →L[ℝ] V →L[ℝ] ℝ) (Γ : V → ManifoldOneForm E M)
    (z : M × V) (Z : V) :
    productCouplingPrimitive Ω Γ z (0,Z)=(1/2:ℝ)*Ω z.2 Z := by
  simp only [productCouplingPrimitive,Pi.add_apply,add_apply,
    productVerticalLiouville_apply,productHorizontalLift_vertical,add_zero]

 theorem productCouplingPrimitive_face
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {μ : V → ℝ} (hμ : ContDiff ℝ ∞ μ) {Γ : ℝ × V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {a : ℝ}
    (hInv : ∀ t x,CollarInvariant Ω μ a (fun v => Γ (t,v) x))
    (p : ℝ × (M × V)) (hp : a<μ p.2.2) :
    manifoldExteriorOneForm (productCouplingPrimitive Ω (fun v => Γ (p.1,v))) p.2
        (0,autonomousField Ω μ p.2.2)=
        -mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) (fun y : M × V => μ y.2) p.2 ∧
      ∀ t, productCouplingPrimitive Ω (fun v => Γ (t,v)) p.2 (0,autonomousField Ω μ p.2.2)=
        productCouplingPrimitive Ω (fun v => Γ (0,v)) p.2 (0,autonomousField Ω μ p.2.2) := by
  have hsΓ : SmoothOneFormFamily (fun v => Γ (p.1,v)) :=
    hΓ.comp (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun v : V => v)))
  constructor
  · rw [productCouplingPrimitive_exterior Ω hs hsΓ]
    exact globalHorizontalCoupling_face hΩ hμ hsΓ p.2 ((hInv p.1 p.2.1).2 p.2.2 hp)
  · intro t
    rw [productCouplingPrimitive_vertical_value,productCouplingPrimitive_vertical_value]

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem isInvertible_of_chartTwoForm {Ω : ManifoldTwoForm E M} {c x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ,E) c).source)
    (hΩ : (chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c x)).IsInvertible) :
    (Ω x).IsInvertible := by
  have hC : (chartDifferential (E := E) c x).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hx using 1
    all_goals try with_reducible_and_instances rfl
  have hB : ((Ω x).bilinearComp (chartDifferential c x).inverse
      (chartDifferential c x).inverse).IsInvertible := by
    simpa only [chartTwoForm,(extChartAt 𝓘(ℝ,E) c).left_inv hx] using hΩ
  have hi := bilinearComp_isInvertible hB hC
  have he : ((Ω x).bilinearComp (chartDifferential c x).inverse
      (chartDifferential c x).inverse).bilinearComp
      (chartDifferential c x) (chartDifferential c x) = Ω x := by
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply,hC.inverse_apply_self]
  rwa [he] at hi

variable [CompleteSpace E]

theorem manifoldTwoForm_isOpen_nondegenerate
    {Ω : ℝ → ManifoldTwoForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) :
    IsOpen {p : ℝ × M | (Ω p.1 p.2).IsInvertible} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  let c := p.2
  let y := extChartAt 𝓘(ℝ,E) c c
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target := mem_extChartAt_target c
  have hi : (chartTwoForm (Ω p.1) c y).IsInvertible := by
    apply chartTwoForm_isInvertible hy
    simpa only [y,(extChartAt 𝓘(ℝ,E) c).left_inv (mem_extChartAt_source c)] using (show (Ω p.1 c).IsInvertible from hp)
  have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 (p.1,y) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,hy⟩
  have hC : ContinuousAt (fun q : ℝ × M => (q.1,extChartAt 𝓘(ℝ,E) c q.2)) p :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt (I := 𝓘(ℝ,E)) c).comp continuousAt_snd)
  have hO : ContinuousAt (fun q : ℝ × M =>
      chartTwoForm (Ω q.1) c (extChartAt 𝓘(ℝ,E) c q.2)) p :=
    ContinuousAt.comp (f := fun q : ℝ × M => (q.1,extChartAt 𝓘(ℝ,E) c q.2))
      ((hΩ c).continuousOn.continuousAt hn) hC
  have hni : ∀ᶠ A : E →L[ℝ] E →L[ℝ] ℝ in 𝓝 (chartTwoForm (Ω p.1) c y),
      A.IsInvertible := ContinuousLinearEquiv.isOpen.mem_nhds hi
  have hsource : ∀ᶠ q : ℝ × M in 𝓝 p, q.2 ∈ (extChartAt 𝓘(ℝ,E) c).source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds c)
  filter_upwards [hO.preimage_mem_nhds hni,hsource] with q hq hqs
  exact isInvertible_of_chartTwoForm hqs hq

end

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M] [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem productCouplingPrimitive_stationary
    (Ω : V →L[ℝ] V →L[ℝ] ℝ) (Γ : ℝ × V → ManifoldOneForm E M) (z : M × V)
    (hz : ∀ t,Γ (t,z.2) z.1=Γ (0,z.2) z.1) (t : ℝ) :
    productCouplingPrimitive Ω (fun v => Γ (t,v)) z=
      productCouplingPrimitive Ω (fun v => Γ (0,v)) z := by
  change productVerticalLiouville Ω z+(Γ (t,z.2) z.1).comp (ContinuousLinearMap.fst ℝ E V)=
    productVerticalLiouville Ω z+(Γ (0,z.2) z.1).comp (ContinuousLinearMap.fst ℝ E V)
  rw [hz t]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M] in
 theorem productCouplingPrimitive_baseFiber_face
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {χ : M → ℝ} (hstation : ∀ x,χ x<3/4→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i)) (a : ι → ℝ)
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (i : Option ι) (p : ℝ × (M × V)) (hp : baseFiberInner a i<baseFiberMoment χ μ i p.2) :
      (∀ t,productCouplingPrimitive Ω (fun v => Γ (t,v)) p.2=
        productCouplingPrimitive Ω (fun v => Γ (0,v)) p.2) ∨
      (manifoldExteriorOneForm (productCouplingPrimitive Ω (fun v => Γ (p.1,v))) p.2
          (baseFiberField Ω μ i p.2)=
        -mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) (baseFiberMoment χ μ i) p.2 ∧
        ∀ t,productCouplingPrimitive Ω (fun v => Γ (t,v)) p.2 (baseFiberField Ω μ i p.2)=
          productCouplingPrimitive Ω (fun v => Γ (0,v)) p.2 (baseFiberField Ω μ i p.2)) := by
  cases i with
  | none =>
    left
    exact productCouplingPrimitive_stationary Ω Γ p.2
      (fun t => hstation p.2.1 (by change -3/4 < -χ p.2.1 at hp; linarith) t p.2.2)
  | some i =>
    right
    exact productCouplingPrimitive_face hΩ hs (hμ i) hΓ (hInv i) p hp
 theorem horizontal_sublevel_moser
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ)
    (hCb : IsCompact {x | (1/2:ℝ)≤χ x})
    (hstation : ∀ x,χ x<3/4→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i,a i < c i)
    (hY : IsCompact {v | ∀ i,μ i v ≤ c i})
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (hnon : ∀ t∈Icc (0:ℝ) 1,∀ z∈{x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v ≤ c i},
      (globalHorizontalCoupling Ω (fun v => Γ (t,v)) z).IsInvertible) :
    ∃ Φ Ψ : ℝ × (M × V) → M × V,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × V)) 𝓘(ℝ,E × V) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × V)) 𝓘(ℝ,E × V) ∞ Ψ ∧
      (∀ z,Φ (0,z)=z) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ z,Ψ (t,Φ (t,z))=z ∧ Φ (t,Ψ (t,z))=z) ∧
      (∃ C : Set (M × V),IsCompact C ∧ ∀ t z,z∉C→Φ (t,z)=z) ∧
      (∀ z,(∀ t,Γ (t,z.2) z.1=Γ (0,z.2) z.1)→∀ t,Φ (t,z)=z) ∧
      (∀ t∈Icc (0:ℝ) 1,
        (fun z => Φ (t,z)) '' ({x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v ≤ c i})=
          {x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v ≤ c i}) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ z∈{x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v ≤ c i},∀ u w,
        manifoldPullback Φ (fun s => globalHorizontalCoupling Ω (fun v => Γ (s,v))) t z u w=
          globalHorizontalCoupling Ω (fun v => Γ (0,v)) z u w) := by
  let Λ : ℝ → ManifoldOneForm (E × V) (M × V) :=
    fun t => productCouplingPrimitive Ω (fun v => Γ (t,v))
  have hΛ : SmoothOneFormFamily Λ := productCouplingPrimitive_smooth Ω hΓ
  have hΛe : ∀ t z,manifoldExteriorOneForm (Λ t) z=
      globalHorizontalCoupling Ω (fun v => Γ (t,v)) z := by
    intro t z
    exact productCouplingPrimitive_exterior Ω hs
      (hΓ.comp (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun v : V => v)))) z
  let U := {p : ℝ × (M × V) | (manifoldExteriorOneForm (Λ p.1) p.2).IsInvertible}
  have hU : IsOpen U := manifoldTwoForm_isOpen_nondegenerate
    (Ω := fun s => manifoldExteriorOneForm (Λ s)) (manifoldExteriorOneForm_path_smooth hΛ)
  have hCU : Icc (0:ℝ) 1 ×ˢ {z | ∀ i,baseFiberMoment χ μ i z≤baseFiberOuter c i}⊆U := by
    intro p hp
    rw [baseFiber_domain] at hp
    change (manifoldExteriorOneForm (Λ p.1) p.2).IsInvertible
    rw [hΛe]
    exact hnon p.1 hp.1 p.2 hp.2
  obtain ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hcomp,hfix,hpres,hpull⟩  := manifold_exact_sublevel_moser_bp240 (E := E × V) (M := M × V)
    hΛ (baseFiberMoment χ μ) (baseFiberMoment_smooth hχ hμ)
    (baseFiberInner a) (baseFiberOuter c) (baseFiber_bounds hac)
    ((baseFiber_domain χ μ c).symm ▸ hCb.prod hY) hU hCU (fun _ hp => hp) (baseFiberField Ω μ)
    (fun i p _ hp => productCouplingPrimitive_baseFiber_face hΩ hs hΓ hstation μ hμ a hInv i p hp)
  refine ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hcomp,?_,?_,?_⟩
  · intro z hz t
    exact hfix z (productCouplingPrimitive_stationary Ω Γ z hz) t
  · intro t ht
    exact baseFiber_domain χ μ c ▸ (hpres t ht).1
  · intro t ht z hz u w
    have he : (fun s => manifoldExteriorOneForm (Λ s))=
        (fun s => globalHorizontalCoupling Ω (fun v => Γ (s,v))) := funext (fun s => funext (hΛe s))
    simpa only [he,hΛe] using hpull t ht z (by
      change z∈{y | ∀ i,baseFiberMoment χ μ i y≤baseFiberOuter c i}
      rw [baseFiber_domain]
      exact hz) u w

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_StationaryManifoldPullback
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem manifoldPullback_of_stationary_germ
    {Φ : ℝ × M → M} {Γ : ℝ → ManifoldOneForm E M} {t : ℝ} {x : M}
    (hΦ : (fun y => Φ (t,y)) =ᶠ[𝓝 x] id)
    (hΓ : Γ t =ᶠ[𝓝 x] Γ 0) :
    manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x =
      manifoldExteriorOneForm (Γ 0) x := by
  have hd : preferredDifferential (E := E) (fun y => Φ (t,y)) x=ContinuousLinearMap.id ℝ E := by
    unfold preferredDifferential
    rw [hΦ.mfderiv_eq,mfderiv_id]
    rfl
  have hv : Φ (t,x)=x := hΦ.eq_of_nhds
  unfold manifoldPullback
  rw [hv,hd]
  ext v w
  change manifoldExteriorOneForm (Γ t) x v w=manifoldExteriorOneForm (Γ 0) x v w
  rw [manifoldExteriorOneForm_congr_germ hΓ]

end
section

variable {M : Type*}

 theorem image_eq_of_fixed_complement {f : M → M} {C D : Set M}
    (hCD : C⊆D) (hC : f '' C=C) (hfix : ∀ x∈D,x∉C→f x=x) : f '' D=D := by
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    by_cases hc : x∈C
    · exact hCD (hC ▸ mem_image_of_mem f hc)
    · simpa only [hfix x hx hc] using hx
  · intro x hx
    by_cases hc : x∈C
    · obtain ⟨y,hy,he⟩ := show x∈f '' C from hC.symm ▸ hc
      exact ⟨y,hCD hy,he⟩
    · exact ⟨x,hx,hfix x hx hc⟩

 theorem image_interior_eq_of_inverse [TopologicalSpace M]
    {f g : M → M} (hf : Continuous f) (hg : Continuous g)
    (hgf : LeftInverse g f) (hfg : RightInverse g f)
    {D : Set M} (hD : f '' D=D) : f '' interior D=interior D := by
  let e : M ≃ₜ M :=
    { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg,
      continuous_toFun := hf, continuous_invFun := hg }
  have he := e.image_interior D
  change f '' interior D=interior (f '' D) at he
  rwa [hD] at he

end

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem horizontal_compact_moser
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {D S : Set M} (hS : IsCompact S) (hSD : S⊆interior D)
    (hstation : ∀ x,x∉S→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i,a i < c i)
    (hY : IsCompact {v | ∀ i,μ i v ≤ c i})
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (hnon : ∀ t∈Icc (0:ℝ) 1,∀ z∈D ×ˢ {v | ∀ i,μ i v ≤ c i},
      (globalHorizontalCoupling Ω (fun v => Γ (t,v)) z).IsInvertible) :
    ∃ Φ Ψ : ℝ × (M × V) → M × V,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × V)) 𝓘(ℝ,E × V) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × V)) 𝓘(ℝ,E × V) ∞ Ψ ∧
      (∀ z,Φ (0,z)=z) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ z,Ψ (t,Φ (t,z))=z ∧ Φ (t,Ψ (t,z))=z) ∧
      (∃ C : Set (M × V),IsCompact C ∧ ∀ t z,z∉C→Φ (t,z)=z) ∧
      (∀ t z,z.1∉S→Φ (t,z)=z) ∧
      (∀ t∈Icc (0:ℝ) 1,
        (fun z => Φ (t,z)) '' (D ×ˢ {v | ∀ i,μ i v ≤ c i})=D ×ˢ {v | ∀ i,μ i v ≤ c i} ∧
        (fun z => Φ (t,z)) '' interior (D ×ˢ {v | ∀ i,μ i v ≤ c i})=
          interior (D ×ˢ {v | ∀ i,μ i v ≤ c i})) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ z∈D ×ˢ {v | ∀ i,μ i v ≤ c i},∀ u w,
        manifoldPullback Φ (fun s => globalHorizontalCoupling Ω (fun v => Γ (s,v))) t z u w=
          globalHorizontalCoupling Ω (fun v => Γ (0,v)) z u w) := by
  obtain ⟨χ,hχ,hCb,hCbD,hχ1⟩ := exists_base_moser_cutoff (E := E) hS hSD
  let Y : Set V := {v | ∀ i,μ i v ≤ c i}
  let Cb : Set M := {x | (1/2:ℝ)≤χ x}
  have hSCb : S⊆Cb := by
    intro x hx
    change (1/2:ℝ)≤χ x
    rw [hχ1 x hx]
    norm_num
  have hsmall : ∀ x,χ x<3/4→∀ t v,Γ (t,v) x=Γ (0,v) x := by
    intro x hx t v
    apply hstation x
    intro hs
    rw [hχ1 x hs] at hx
    norm_num at hx
  obtain ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hcomp,hfix,hpres,hpull⟩ := horizontal_sublevel_moser
    hΩ hs hΓ hχ hCb hsmall μ hμ a c hac hY hInv
    (fun t ht z hz => hnon t ht z ⟨hCbD hz.1,hz.2⟩)
  have hf : ∀ t z,z.1∉S→Φ (t,z)=z := fun t z hz => hfix z (fun s => hstation z.1 hz s z.2) t
  refine ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hcomp,hf,?_,?_⟩
  · intro t ht
    have hpC : (fun z => Φ (t,z)) '' (Cb ×ˢ Y)=Cb ×ˢ Y := hpres t ht
    have hpD : (fun z => Φ (t,z)) '' (D ×ˢ Y)=D ×ˢ Y :=
      image_eq_of_fixed_complement (prod_mono hCbD Subset.rfl) hpC (by
        intro z hz hzc
        apply hf t z
        intro hs
        exact hzc ⟨hSCb hs,hz.2⟩)
    refine ⟨hpD,?_⟩
    exact image_interior_eq_of_inverse
      (hΦ.continuous.comp (continuous_const.prodMk continuous_id))
      (hΨ.continuous.comp (continuous_const.prodMk continuous_id))
      (fun z => (hi t ht z).1) (fun z => (hi t ht z).2) hpD
  · intro t ht z hz u w
    by_cases hc : z∈Cb ×ˢ Y
    · exact hpull t ht z hc u w
    · have hn : z.1∉S := fun hs => hc ⟨hSCb hs,hz.2⟩
      have hnh : ∀ᶠ y : M × V in 𝓝 z,y.1∉S :=
        continuousAt_fst.eventually (hS.isClosed.isOpen_compl.mem_nhds hn)
      let Λ : ℝ → ManifoldOneForm (E × V) (M × V) :=
        fun t => productCouplingPrimitive Ω (fun v => Γ (t,v))
      have hΛstation : ∀ y : M × V,y.1∉S→Λ t y=Λ 0 y := by
        intro y hy
        change productVerticalLiouville Ω y+(Γ (t,y.2) y.1).comp (ContinuousLinearMap.fst ℝ E V)=
          productVerticalLiouville Ω y+(Γ (0,y.2) y.1).comp (ContinuousLinearMap.fst ℝ E V)
        rw [hstation y.1 hy t y.2]
      have hp := manifoldPullback_of_stationary_germ
        (hnh.mono (fun y hy => hf t y hy))
        (hnh.mono (fun y hy => hΛstation y hy))
      have he : ∀ s,manifoldExteriorOneForm (Λ s)=globalHorizontalCoupling Ω (fun v => Γ (s,v)) := by
        intro s
        funext y
        exact productCouplingPrimitive_exterior Ω hs
          (hΓ.comp (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun v : V => v)))) y
      rw [funext he,he] at hp
      exact congrArg (fun L : (E × V) →L[ℝ] (E × V) →L[ℝ] ℝ => L u w) hp

 theorem horizontal_moser_endpoint_bp240_oai
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {D S : Set M} (hS : IsCompact S) (hSD : S⊆interior D)
    (hstation : ∀ x,x∉S→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i,a i < c i)
    (hY : IsCompact {v | ∀ i,μ i v ≤ c i})
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (hnon : ∀ t∈Icc (0:ℝ) 1,∀ z∈D ×ˢ {v | ∀ i,μ i v ≤ c i},
      (globalHorizontalCoupling Ω (fun v => Γ (t,v)) z).IsInvertible) :
    ∃ e : (M × V) ≃ₘ⟮𝓘(ℝ,E × V),𝓘(ℝ,E × V)⟯ (M × V),
      e '' (D ×ˢ {v | ∀ i,μ i v ≤ c i})=D ×ˢ {v | ∀ i,μ i v ≤ c i} ∧
      e '' interior (D ×ˢ {v | ∀ i,μ i v ≤ c i})=interior (D ×ˢ {v | ∀ i,μ i v ≤ c i}) ∧
      PreservesTwoFormOn e (globalHorizontalCoupling Ω (fun v => Γ (0,v)))
        (globalHorizontalCoupling Ω (fun v => Γ (1,v))) (D ×ˢ {v | ∀ i,μ i v ≤ c i}) ∧
      (∃ C : Set (M × V),IsCompact C ∧ ∀ z,z∉C→e z=z) ∧
      (∀ z,z.1∉S→e z=z) := by
  obtain ⟨Φ,Ψ,hΦ,hΨ,_,hi,hC,hfix,hpres,hpull⟩ := horizontal_compact_moser
    hΩ hs hΓ hS hSD hstation μ hμ a c hac hY hInv hnon
  have h1 : (1:ℝ)∈Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  let e : (M × V) ≃ₘ⟮𝓘(ℝ,E × V),𝓘(ℝ,E × V)⟯ (M × V) :=
    { toFun := fun z => Φ (1,z)
      invFun := fun z => Ψ (1,z)
      left_inv := fun z => (hi 1 h1 z).1
      right_inv := fun z => (hi 1 h1 z).2
      contMDiff_toFun := hΦ.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hΨ.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨e,(hpres 1 h1).1,(hpres 1 h1).2,(fun z hz u w => hpull 1 h1 z hz u w),?_,?_⟩
  · obtain ⟨C,hc,h⟩ := hC
    exact ⟨C,hc,fun z hz => h 1 z hz⟩
  · exact fun z hz => hfix 1 z hz

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint_bp240_oai.{u_1, u_2, u_3, u_4} := @OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint_bp240_oai.{u_1, u_2, u_3, u_4}
