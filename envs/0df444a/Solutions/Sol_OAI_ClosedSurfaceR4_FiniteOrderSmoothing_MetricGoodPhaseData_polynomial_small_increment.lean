-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_small_increment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:35:53.451818+00:00
-- url     : https://prove2.me/submissions/09c241b5-faaa-4ba7-b7c7-e2d3836118bb

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_full_linearized_representatives
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_profiled_polynomial_atlas_small_increment
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_linear_perturbed_mean_family_all_profiles

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



lemma secondQuadratic_smul {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (w : ℝ) :
    secondQuadratic B (w • v) = w ^ 2 • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodPhases
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma continuous_secondQuadratic {n : ℕ} :
    Continuous (fun z : (Fin 3 → RVec n) × Base => secondQuadratic z.1 z.2) := by
  unfold secondQuadratic
  fun_prop

lemma isOpen_good {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} (hB : Continuous B) (hξ : Continuous ξ) :
    IsOpen {p : X | Good (B p) (ξ p)} := by
  change IsOpen ({p : X | ξ p ≠ 0} ∩
    {p : X | secondQuadratic (B p) (-(ξ p).2, (ξ p).1) ≠ 0})
  apply (isOpen_ne_fun hξ continuous_const).inter
  apply isOpen_ne_fun _ continuous_const
  exact continuous_secondQuadratic.comp (hB.prodMk ((hξ.snd.neg).prodMk hξ.fst))



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes



lemma gramDet_ne_zero_of_injective (A : Base →L[ℝ] RVec 4) (hA : Function.Injective A) :
    NormalFrame.gramDet (A dx) (A dy) ≠ 0 := by
  let X := A dx
  let Y := A dy
  have hX : X ≠ 0 := by
    intro hx
    have he : dx = 0 := hA (by simpa [X] using hx)
    exact one_ne_zero (congrArg Prod.fst he)
  have hXX : X ⬝ᵥ X ≠ 0 := (dotProduct_self_eq_zero).not.mpr hX
  intro hD
  let v : Base := -(X ⬝ᵥ Y) • dx + (X ⬝ᵥ X) • dy
  have hv : A v = -(X ⬝ᵥ Y) • X + (X ⬝ᵥ X) • Y := by simp [v,X,Y]
  have hsq : A v ⬝ᵥ A v = (X ⬝ᵥ X) * NormalFrame.gramDet X Y := by
    rw [hv]
    simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hz : A v = 0 := dotProduct_self_eq_zero.mp (by rw [hsq]; change _ * NormalFrame.gramDet (A dx) (A dy) = 0; rw [hD,mul_zero])
  have hv0 : v = 0 := hA (by simpa using hz)
  have hy0 := congrArg Prod.snd hv0
  exact hXX (by simpa [v,dx,dy] using hy0)

lemma injective_of_gramDet_ne_zero (A : Base →L[ℝ] RVec 4)
    (hD : NormalFrame.gramDet (A dx) (A dy) ≠ 0) : Function.Injective A := by
  have hz : ∀ v : Base, A v = 0 → v = 0 := by
    intro v hv
    have hb : A v = v.1 • A dx + v.2 • A dy := by
      calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
           _ = _ := by simp
    have hx := congrArg (fun W => A dx ⬝ᵥ W) hv
    have hy := congrArg (fun W => A dy ⬝ᵥ W) hv
    rw [hb] at hx hy
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      dotProduct_comm (A dy) (A dx)] at hx hy
    have hvx : v.1 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.1 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dy ⬝ᵥ A dy) * hx - (A dx ⬝ᵥ A dy) * hy)).resolve_left hD
    have hvy : v.2 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.2 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dx ⬝ᵥ A dx) * hy - (A dx ⬝ᵥ A dy) * hx)).resolve_left hD
    exact Prod.ext hvx hvy
  intro p q hpq
  exact sub_eq_zero.mp (hz (p-q) (by simpa using sub_eq_zero.mpr hpq))

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma contDiffAt_realSecondTensor {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    ContDiffAt ℝ ∞ (realSecondTensor F) p := by
  have hx := (contDiff_real_coordDeriv hF dx).contDiffAt (x := p)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffAt (x := p)
  have hb (v w : Base) : ContDiffAt ℝ ∞ (fun q => realSecondForm F v w q) p :=
    contDiffAt_realNormalPart hx hy
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hb dx dx
  · exact hb dx dy
  · exact hb dy dy

lemma continuous_gramDet_field {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p => NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p)) := by
  have hx := (contDiff_real_coordDeriv hF dx).continuous
  have hy := (contDiff_real_coordDeriv hF dy).continuous
  unfold NormalFrame.gramDet dotProduct
  fun_prop

lemma good_eventually {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} {p : X}
    (hB : ContinuousAt B p) (hξ : ContinuousAt ξ p) (hg : Good (B p) (ξ p)) :
    ∀ᶠ q in 𝓝 p, Good (B q) (ξ q) := by
  have ho : IsOpen {z : (Fin 3 → RVec n) × Base | Good z.1 z.2} :=
    isOpen_good continuous_fst continuous_snd
  exact (hB.prodMk hξ).preimage_mem_nhds (ho.mem_nhds hg)




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPartition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

lemma finite_positive_threshold {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ i, z ≤ v i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image v)
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,Finset.min'_le s 1 (Finset.mem_insert_self _ _),?_⟩
  · have hm := s.min'_mem hs
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hm
    rcases hm with he | ⟨i,hi⟩
    · rw [he]; norm_num
    · rw [← hi]; exact hv i
  · intro i
    exact Finset.min'_le s (v i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseWeights
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_smul {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base} {w : ℝ}
    (hw : w ≠ 0) (h : Good B ξ) : Good B (w • ξ) := by
  constructor
  · exact smul_ne_zero hw h.1
  · have he : (-(w • ξ).2, (w • ξ).1) = w • (-ξ.2, ξ.1) := by ext <;> simp
    rw [he, secondQuadratic_smul]
    exact smul_ne_zero (pow_ne_zero 2 hw) h.2



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

variable [CompactSpace M]

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_rc5bd98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasSupportedWeights
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas cutoffs as actual compactly supported fields, and their
transport to a phase chart with the required inverse-frequency factor. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold Bundle PhaseMean WeightedEstimates
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseWeightCutoff_apply (i : A.centers)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hK : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ e.source)
    (w : ℝ) {x : SmallModes.Base} (hx : x ∈ e.source) :
    A.phaseWeightCutoff i e he hK w (e x) = A.planeWeight i x / w := by
  change w⁻¹ * chartPush e he (modeSupport (A.chartWeightCompact i)) hK
    (A.supportedPlaneWeight i) (e x) = _
  rw [chartPush_eval_source e he _ hK _ hx, A.supportedPlaneWeight_apply]
  exact (div_eq_inv_mul _ _).symm

lemma planeWeight_support_chart (i : A.centers)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (hK : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ e.source) :
    tsupport (A.planeWeight i) ⊆ e.source := by
  have hh := (A.supportedPlaneWeight i).tsupport_subset
  have hsub : tsupport (A.planeWeight i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := hh
  exact hsub.trans hK

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas bounds for the genuine smooth coordinate representatives.
The constants precede the map and scale, and no derivative order is lost. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma localize_outer_restore (i j : A.centers) (f : JetPolynomial.Base → V) :
    localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f) =
      fun x => localize (i : M) (A.outer i) (A.outer j) x •
        f (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize,restore,indicator_of_mem hi,indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hj (A.outer_support j h))
      simp only [localize,restore,indicator_of_mem hi,indicator_of_notMem hj,hz,smul_zero,zero_smul]
  · simp only [localize,indicator_of_notMem hi,zero_smul]

lemma localize_outer_restore_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f)) := by
  let K := (chart (i : M)) '' (tsupport (A.outer i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => A.outer_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨(chart (i : M)).map_source (A.outer_support i hp.1),?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (A.outer_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D,hD,hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (A.outer_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [A.localize_outer_restore]
  exact hd f s C hs hs1 hC hf hb

theorem vectorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorChartRead i F) := by
  classical
  choose D hD hd using fun j : A.centers => A.localize_outer_restore_bound (V := V) i j m
  refine ⟨∑ j : A.centers, D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro F s C hs hs1 hC hF hb
  have he : A.vectorChartRead i F = fun x => ∑ j : A.centers,
      localize (i : M) (A.outer i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    unfold vectorChartRead
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he,Finset.sum_mul]
  apply WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn
  · intro j _
    exact hd j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j)

theorem vectorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorPlaneRead i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := V) i m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth i hF) (hd F s C hs hs1 hC hF hb)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_rc5bd98_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_rc5bd98_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_rc5bd98_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_rc5bd98_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_rc5bd98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_rc5bd98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_plane (i : A.centers) (F : M → Space) :
    A.jetChartMap i F ∘ planeCoordinateIsometry.symm = spaceCoordinates ∘ A.vectorPlaneRead i F := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasOuterDomains
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded open coordinate domains containing every outer cutoff support. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_outer_domains :
    ∃ (U : A.centers → Set JetPolynomial.Base) (K : A.centers → Compacts JetPolynomial.Base),
      (∀ i, IsOpen (U i)) ∧ (∀ i, U i ⊆ K i) ∧
      (∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i) ∧
      (∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i) := by
  classical
  have hc (i : A.centers) : IsCompact ((chart (i : M)) '' tsupport (A.outer i)) :=
    (isClosed_tsupport (A.outer i)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (A.outer_support i))
  choose U hU hKU hUc _ using fun i => CollarVelocity.compact_open_thickening
    (hc i) isOpen_univ (subset_univ _)
  refine ⟨U,fun i => ⟨closure (U i),hUc i⟩,hU,fun _ => subset_closure,?_,hKU⟩
  intro i x hx
  obtain ⟨p,hp,rfl⟩ := hx
  apply hKU i
  refine ⟨p,subset_tsupport (A.outer i) ?_,rfl⟩
  change A.outer i p ≠ 0
  rw [A.outer_one i p hp]
  exact one_ne_zero

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

/-- An unweighted prefix of any lower order is controlled by a shifted bound. -/
lemma ShiftedBound.prefix {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {j : ℕ} (hj : j ≤ q + m) :
    WeightedBound Set.univ 1 j (C / s ^ (j - q)) f := by
  intro i hi x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  apply (h.deriv_le hs (hi.trans hj) x).trans
  exact div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le_sub_right hi q))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadPrefixBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart readings retain the unweighted derivative prefix of the true map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem vectorPlaneRead_prefix_bounds (i : A.centers) (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound q m s C F → ∀ j ≤ q+m,
      WeightedEstimates.WeightedBound univ 1 j (D*C/s^(j-q)) (A.vectorPlaneRead i F) := by
  classical
  choose D hD hd using fun j => A.vectorPlaneRead_bound (V := V) i j
  let T := ∑ j ∈ Finset.range (q+m+1), D j
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => hD j)
  refine ⟨T,hT,?_⟩
  intro F s C hs hs1 hC hF hb j hj
  have hp : A.WeightedBound 1 j (C/s^(j-q)) F := fun k => (hb k).prefix hs hs1 hC hj
  have hh := hd j F 1 (C/s^(j-q)) zero_lt_one le_rfl (by positivity) hF hp
  apply hh.mono_const
  calc
    D j*(C/s^(j-q)) = D j*C/s^(j-q) := by ring
    _ ≤ T*C/s^(j-q) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC)
      (pow_nonneg hs.le _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealJetPrefixBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-jet bounds retain the two unscaled derivatives of a smoothed immersion. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates FiniteOrderSmoothing

/-- Fixed smooth coordinates preserve the shifted two-derivative bound.
The constant is independent of the map and of the smoothing scale. -/
theorem compact_realTwoJet_comp_prefix_bound {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (K : Compacts Base) {U : Set Base} (hU : IsOpen U) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : RField 4), ContDiff ℝ ∞ F → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m+2, WeightedBound univ 1 j (C/s^(j-2)) F) →
      WeightedBound U s m (D*C) (realTwoJet (F ∘ T)) := by
  obtain ⟨B,hB,hb⟩ := compact_local_weighted_bound hU isOpen_univ K.isCompact hUK
    (subset_univ _) hT.contDiffOn (m+2)
  let D : ℝ := ((m+2).factorial : ℝ)*B^(m+2)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (m+2))) (one_le_pow₀ hB)
  refine ⟨D,hD,?_⟩
  intro F hF s C hs hs1 hC hp
  have hcomp (j : ℕ) (hj : j ≤ m+2) :
      WeightedBound U 1 j (D*C/s^(j-2)) (F ∘ T) := by
    have hc (k : ℕ) (_ : 1 ≤ k) (hk : k ≤ j) (x : Base) (hx : x ∈ U) :
        ‖iteratedFDerivWithin ℝ k T U x‖ ≤ B := by
      simpa only [one_pow,one_mul] using hb 1 zero_le_one le_rfl k (hk.trans hj) x hx
    have hh := (hp j hj).comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ
      zero_lt_one le_rfl hB (div_nonneg hC (pow_nonneg hs.le _))
      hT.contDiffOn hF.contDiffOn (mapsTo_univ _ _) hc
    apply hh.mono_const
    calc
      (j.factorial : ℝ)*(C/s^(j-2))*B^j = ((j.factorial : ℝ)*B^j)*C/s^(j-2) := by ring
      _ ≤ D*C/s^(j-2) := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
        apply mul_le_mul_of_nonneg_right _ hC
        dsimp [D]
        gcongr
  have hfirst (v : Base) (hv : ‖v‖ = 1) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound U 1 j (D*C/s^(j-1)) (coordDeriv v (F ∘ T)) := by
    have hh := (hcomp (j+1) (by omega)).directional hU zero_lt_one (hF.comp hT).contDiffOn v
    change WeightedBound U 1 j (D*C/s^(j-1)) (fun x => fderiv ℝ (F ∘ T) x v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hv,one_mul,div_one,he] using hh
  have hC' : 0 ≤ D*C := mul_nonneg (zero_le_one.trans hD) hC
  have hd (f : RField 4) (hf : ContDiff ℝ ∞ f)
      (hf' : ∀ j ≤ m+1, WeightedBound U 1 j (D*C/s^(j-1)) f)
      (v : Base) (hv : ‖v‖ = 1) : WeightedBound U s m (D*C) (coordDeriv v f) := by
    intro j hj x hx
    have hh := ((hf' (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn v)
      j le_rfl x hx
    simp only [one_pow,one_mul,div_one,hv,Nat.add_sub_cancel] at hh
    calc
      _ ≤ s^j*(D*C/s^j) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ = D*C := by field_simp
  have hf (v : Base) (hv : ‖v‖ = 1) :
      WeightedBound U s m (D*C) (coordDeriv v (F ∘ T)) := by
    apply hd (F ∘ T) (hF.comp hT) _ v hv
    intro j hj
    apply (hcomp j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC' (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have hdd (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      WeightedBound U s m (D*C) (coordDeriv v (coordDeriv w (F ∘ T))) :=
    hd _ (contDiff_real_coordDeriv (hF.comp hT) w) (hfirst w hw) v hv
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  change WeightedBound U s m (D*C) (fun x i => realTwoJet (F ∘ T) x i)
  apply WeightedBound.pi hU.uniqueDiffOn hs hC'
  · intro i
    fin_cases i <;> first
      | exact (contDiff_real_coordDeriv (hF.comp hT) _).contDiffOn
      | exact (contDiff_real_coordDeriv (contDiff_real_coordDeriv (hF.comp hT) _) _).contDiffOn
  · intro i
    fin_cases i
    · exact hf dx hx
    · exact hf dy hy
    · exact hdd dx dx hx hx
    · exact hdd dx dy hx hy
    · exact hdd dy dy hy hy

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseJetBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted two-jet estimates in a fixed phase chart from the global input norm. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phaseChart_twoJet_bound (i : A.centers)
    {T : SmallModes.Base → SmallModes.Base} (hT : ContDiff ℝ ∞ T)
    (K : Compacts SmallModes.Base) {U : Set SmallModes.Base}
    (hU : IsOpen U) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : M → Space) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel spaceModel ∞ F →
      A.ShiftedBound 2 m s C F →
      WeightedEstimates.WeightedBound U s m (D*C)
        (realTwoJet ((spaceCoordinates ∘ A.vectorPlaneRead i F) ∘ T)) := by
  obtain ⟨B,hB,hb⟩ := A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  obtain ⟨E,hE,he⟩ := compact_realTwoJet_comp_prefix_bound hT K hU hUK m
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖*B
  let D : ℝ := 1+E*L
  have hL : 0 ≤ L := mul_nonneg (norm_nonneg _) hB
  have hD : 1 ≤ D := le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hE) hL)
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hp
  have hlocal := A.vectorPlaneRead_smooth i hF
  have hprefix (j : ℕ) (hj : j ≤ m+2) :
      WeightedEstimates.WeightedBound univ 1 j (L*C/s^(j-2))
        (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    have hh := (hb F s C hs hs1 hC hF hp j (by omega)).linear
      uniqueDiffOn_univ zero_le_one hlocal.contDiffOn spaceCoordinates.toContinuousLinearMap
    simpa only [L,mul_div_assoc,mul_assoc,ContinuousLinearEquiv.coe_coe] using hh
  have hh := he (spaceCoordinates ∘ A.vectorPlaneRead i F)
    (spaceCoordinates.contDiff.comp hlocal) s (L*C) hs hs1 (mul_nonneg hL hC) hprefix
  apply hh.mono_const
  calc
    E*(L*C) = (E*L)*C := (mul_assoc _ _ _).symm
    _ ≤ D*C := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed local good-phase charts persist under a global C2 perturbation. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorPlaneRead_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F-G) = A.vectorPlaneRead i F - A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactCoefficientMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive phase coefficients admit an actual compact neighborhood and
uniform inner and outer trial-ball margins. -/
noncomputable section
open Set
open scoped Topology
namespace ClosedSurfaceR4.PhaseMean
open SmallModes (Base)

theorem compact_coefficient_margins {K Ω : Set Base} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) {reference : Base → Tensor}
    (href : ContinuousOn reference Ω) (Q : Tensor →L[ℝ] ℝ)
    (hpos : ∀ x ∈ K, 0 < Q (reference x)) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ Ω ∧
      ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
        ∀ x ∈ closure U, ρ + ‖Q‖*r ≤ Q (reference x) ∧
          Q (reference x) ≤ R - ‖Q‖*r := by
  have hf : ContinuousOn (fun x => Q (reference x)) Ω := Q.continuous.comp_continuousOn href
  obtain ⟨a,ha,hab⟩ := hK.exists_forall_le' (hf.mono hKΩ) hpos
  let O := Ω ∩ (fun x => Q (reference x)) ⁻¹' Ioi (a/2)
  have hO : IsOpen O := hf.isOpen_inter_preimage hΩ isOpen_Ioi
  have hKO : K ⊆ O := by
    intro x hx
    exact ⟨hKΩ hx,lt_of_lt_of_le (by linarith) (hab x hx)⟩
  obtain ⟨U,hU,hKU,hUc,hUO⟩ := CollarVelocity.compact_open_thickening hK hO hKO
  have hUΩ : closure U ⊆ Ω := fun x hx => (hUO hx).1
  obtain ⟨C,hC⟩ := hUc.exists_bound_of_continuousOn (hf.mono hUΩ)
  let r := (a/8)/(‖Q‖+1)
  have hr : 0 < r := div_pos (by linarith) (by positivity)
  have heq : (‖Q‖+1)*r = a/8 := by
    dsimp [r]
    field_simp
  have hnr : ‖Q‖*r ≤ a/8 := by nlinarith [norm_nonneg Q]
  refine ⟨U,hU,hKU,hUc,hUΩ,r,a/8,|C|+‖Q‖*r+1,hr,by linarith,by positivity,?_⟩
  intro x hx
  have hl : a/2 < Q (reference x) := (hUO hx).2
  have hu : Q (reference x) ≤ |C| :=
    (le_abs_self _).trans ((hC x hx).trans (le_abs_self C))
  constructor <;> linarith

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PhaseMeanDomains
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact good geometry supplies the open domains and strict coefficient
margins needed by the actual local mean construction. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean

theorem compact_good_phase_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (K : Compacts Base) (hImm : ∀ x ∈ (K : Set Base), Function.Injective (fderiv ℝ F x))
    (ξ : Base) (hgood : ∀ x ∈ (K : Set Base), Good (realSecondTensor F x) ξ) :
    ∃ Ω : Set Base, IsOpen Ω ∧ (K : Set Base) ⊆ Ω ∧
      ∀ x ∈ Ω, Function.Injective (fderiv ℝ F x) ∧ Good (realSecondTensor F x) ξ := by
  let Ω : Set Base := {x | NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0 ∧
    Good (realSecondTensor F x) ξ}
  have hΩ : IsOpen Ω := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hd := (continuous_gramDet_field hF).continuousAt.eventually_ne hx.1
    have hg := good_eventually (contDiffAt_realSecondTensor hF x hx.1).continuousAt
      continuousAt_const hx.2
    exact hd.and hg
  refine ⟨Ω,hΩ,?_,?_⟩
  · intro x hx
    exact ⟨gramDet_ne_zero_of_injective _ (hImm x hx),hgood x hx⟩
  · intro x hx
    exact ⟨injective_of_gramDet_ne_zero _ hx.1,hx.2⟩

/-- The three phases share positive trial and coefficient radii. All domains
and radii are chosen from the fixed compact reference geometry. -/
theorem compact_phase_mean_domains {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (K : Compacts Base) (hImm : ∀ x ∈ (K : Set Base), Function.Injective (fderiv ℝ F x))
    (ξ : Fin 3 → Base)
    (hgood : ∀ j x, x ∈ (K : Set Base) → Good (realSecondTensor F x) (ξ j))
    (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ) (H : Base → PhaseMean.Tensor) (hH : Continuous H)
    (hpos : ∀ j x, x ∈ (K : Set Base) → 0 < Q j (H x)) :
    ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
      ∃ U K₁ Ω : Fin 3 → Set Base,
        (∀ j, IsOpen (U j)) ∧ (∀ j, IsCompact (K₁ j)) ∧ (∀ j, IsOpen (Ω j)) ∧
        (∀ j, (K : Set Base) ⊆ U j) ∧ (∀ j, U j ⊆ K₁ j) ∧ (∀ j, K₁ j ⊆ Ω j) ∧
        (∀ j x, x ∈ Ω j → Function.Injective (fderiv ℝ F x) ∧
          Good (realSecondTensor F x) (ξ j)) ∧
        (∀ j x, x ∈ K₁ j → ρ + ‖Q j‖*r ≤ Q j (H x) ∧
          Q j (H x) ≤ R - ‖Q j‖*r) := by
  classical
  choose Ω hΩ hKΩ hgeom using fun j =>
    compact_good_phase_neighborhood hF K hImm (ξ j) (hgood j)
  choose U hU hKU hUc hUΩ a b c ha hb hc hmargin using fun j =>
    compact_coefficient_margins K.isCompact (hΩ j) (hKΩ j) hH.continuousOn (Q j) (hpos j)
  let r := min (a 0) (min (a 1) (a 2))
  let ρ := min (b 0) (min (b 1) (b 2))
  let R := ∑ j : Fin 3, c j
  have hr : 0 < r := lt_min (ha 0) (lt_min (ha 1) (ha 2))
  have hρ : 0 < ρ := lt_min (hb 0) (lt_min (hb 1) (hb 2))
  have hra (j : Fin 3) : r ≤ a j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hρb (j : Fin 3) : ρ ≤ b j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hcR (j : Fin 3) : c j ≤ R :=
    Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ j)
  have hR : 0 < R := (hc 0).trans_le (hcR 0)
  refine ⟨r,ρ,R,hr,hρ,hR,U,(fun j => closure (U j)),Ω,
    hU,hUc,hΩ,hKU,(fun _ => subset_closure),hUΩ,hgeom,?_⟩
  intro j x hx
  have hm := hmargin j x hx
  have hn : ‖Q j‖*r ≤ ‖Q j‖*a j :=
    mul_le_mul_of_nonneg_left (hra j) (norm_nonneg _)
  have hl := hρb j
  have hu := hcR j
  constructor <;> linarith

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPhaseMeanDomains
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed mean domains and common margins obtained from compact atlas geometry. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Strict positivity and good geometry on the actual compact supports
supply all domain and margin data for the mean constructor. -/
theorem exists_phaseMeanDomains (F : M → Space)
    (hF : ContMDiff planeModel spaceModel ∞ F) (Q : A.centers → PhaseBasis)
    (hImm : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (reference : A.centers → SmallModes.Base → Tensor)
    (href : ∀ i, Continuous (reference i))
    (hpos : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      0 < (Q i).Q j (reference i x)) : Nonempty (A.PhaseMeanDomains F Q reference) := by
  classical
  choose r ρ R hr hρ hR U K Ω hU hK hΩ hs hUK hKΩ hg hm using fun i : A.centers =>
    compact_phase_mean_domains
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF))
      (modeSupport (A.chartWeightCompact i)) (hImm i) (Q i).ξ (hgood i)
      (Q i).Q (reference i) (href i) (hpos i)
  obtain ⟨r₀,hr₀,_,hrr⟩ := finite_positive_threshold r hr
  obtain ⟨ρ₀,hρ₀,_,hρρ⟩ := finite_positive_threshold ρ hρ
  let R₀ : ℝ := 1 + ∑ i : A.centers, R i
  have hR₀ : 0 < R₀ := by
    have hsum : 0 ≤ ∑ i : A.centers, R i := Finset.sum_nonneg (fun i _ => (hR i).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hRR (i : A.centers) : R i ≤ R₀ := by
    have hh := Finset.single_le_sum (fun j _ => (hR j).le) (Finset.mem_univ i)
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  choose U₀ hU₀ hKU₀ hUc₀ _ using fun i : A.centers =>
    CollarVelocity.compact_open_thickening (A.chartWeightCompact i).isCompact
      isOpen_univ (subset_univ _)
  refine ⟨{
    r := r₀, ρ := ρ₀, R := R₀, r_pos := hr₀, ρ_pos := hρ₀, R_pos := hR₀
    Ω := Ω, U := U, K := K, openΩ := hΩ, openU := hU, compactK := hK
    UK := hUK, KΩ := hKΩ, support := hs
    immersion := fun i j x hx => (hg i j x hx).1
    good := fun i j x hx => (hg i j x hx).2
    U₀ := U₀, K₀ := fun i => ⟨closure (U₀ i),hUc₀ i⟩
    openU₀ := hU₀, U₀K₀ := fun _ => subset_closure, supportU₀ := hKU₀
    margin := ?_
  }⟩
  intro i j x hx
  have hh := hm i j x (hUK i j hx)
  have hn := mul_le_mul_of_nonneg_left (hrr i) (norm_nonneg ((Q i).Q j))
  have hl := hρρ i
  have hu := hRR i
  constructor <;> linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticOverlapSupports
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic targets retain the original support intersections on the surface. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance overlapTargetsFiberNormed_rc5bd98_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance overlapTargetsFiberSpace_rc5bd98_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance overlapTargetsDualAdd_rc5bd98_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapTargetsDualSmul_rc5bd98_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance overlapTargetsSectionNormed_rc5bd98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance overlapTargetsSectionSpace_rc5bd98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [Fintype ι] [DecidableEq ι] in
lemma quadraticOverlapCompact_subset (S : ι → Set M) (hS : ∀ a, IsClosed (S a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    (A.quadraticOverlapCompact S hS k l : Set JetPolynomial.Base) ⊆ A.chartWeightCompact k := by
  rintro x ⟨p,hp,rfl⟩
  exact ⟨p,hp.1,rfl⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformPolynomialAtlasMeanData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual perturbed polynomial mean families on a fixed smoothing atlas.
The common geometric radius precedes the derivative profiles, the nearby
map, and both scales. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The fixed local geometry determines all mean profiles and one global C2
radius before the nearby map, the scales, and the smaller trial radius. -/
theorem uniform_polynomial_input_atlas_mean_data_all_profiles {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k j, (P i k j).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (ξ : A.centers → Fin 3 → SmallModes.Base) (hξ : ∀ i j, ξ i j ≠ 0)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) (ξ i j))
    (S : A.centers → Fin 3 → Compacts JetPolynomial.Base)
    (hS : ∀ i j, (modeSupport (S i j) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i) (hSU₀ : ∀ i j, (S i j : Set JetPolynomial.Base) ⊆ U₀ i)
    (φ : A.centers → Fin 3 → JetPolynomial.Base → ℝ)
    (hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
    (hphase : ∀ i j, coordinatePhase (φ i j) = phaseLinear (ξ i j))
    (ψ : ∀ i j, SupportedField (F := ℝ)
      (JetPolynomial.chartSupport (linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j))
        (modeSupport (S i j)) (hS i j)))
    (Q : A.centers → Fin 3 → Tensor →L[ℝ] ℝ) {r ρ R : ℝ}
    (reference : A.centers → SmallModes.Base → Tensor)
    (hmargin : ∀ i j x, x ∈ U i j → ρ + ‖Q i j‖*r ≤ Q i j (reference i x) ∧
      Q i j (reference i x) ≤ R - ‖Q i j‖*r)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (Pinput : ℕ → ℝ), (∀ m, 0 ≤ Pinput m) →
    ∃ p : ∀ i : A.centers, Fin 3 → ChartedMeanProfile (P i),
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ₀ → A.WeightedBound 1 2 B (G-F) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (Pinput m) G) →
        ∀ (τ ε r' : ℝ), r' ≤ r → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
        ∃ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s r' ρ R (reference i),
          (∀ i, (d i).Fits (p i)) ∧
          (∀ i, (d i).G = A.jetChartMap i G) ∧
          (∀ i, (d i).phase = φ i) ∧ (∀ i, (d i).support = S i) ∧
          (∀ i j, ((d i).solver j).e =
            linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j)) ∧
          (∀ i j x, ((d i).data j).cutoff x = ψ i j x) ∧
          (∀ i j, ((d i).data j).form = fun _ => Q i j) := by
  classical
  let e := fun i j => linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j)
  let KV : A.centers → Fin 3 → Compacts SmallModes.Base := fun i j =>
    ⟨(phaseEquiv (ξ i j) (hξ i j)) '' K i j,
      (hK i j).image (phaseEquiv (ξ i j) (hξ i j)).continuous⟩
  have htarget (i j) : (e i j).target ⊆ KV i j := image_mono (hUK i j)
  choose E hE he using fun (i : A.centers) (j : Fin 3) (m : ℕ) =>
    A.phaseChart_twoJet_bound i (linearPhaseChart_smooth (ξ i j) (hξ i j) (U i j) (hU i j)).2
      (KV i j) (e i j).open_target (htarget i j) m
  choose V hV hv using fun (i : A.centers) (m : ℕ) =>
    A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  choose V₀ hV₀ hv₀ using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i 2
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖
  choose a ha hall using fun i : A.centers => uniform_linear_perturbed_mean_family_all_profiles
    (P i) (hP i) (A.jetChartMap_smooth i hF) (Ω i) (U i) (K i) (hΩ i) (hU i) (hK i) (hUK i) (hKΩ i)
    (ξ i) (hξ i)
    (by simpa only [A.jetChartMap_plane] using hImm i)
    (by simpa only [A.jetChartMap_plane] using hgood i)
    (S i) (hS i) (hU₀ i) (K₀ i) (hU₀K i) (hSU₀ i) (φ i) (hφ i) (hphase i)
    (ψ i) (Q i) (hmargin i)
  have hL₀ (i) : 0 ≤ L * V₀ i := mul_nonneg (norm_nonneg _) (hV₀ i)
  obtain ⟨ρ₀,hρ₀,_,hρa⟩ := finite_positive_threshold
    (fun i : A.centers => a i / (1 + L * V₀ i))
    (fun i => div_pos (ha i) (by linarith [hL₀ i]))
  refine ⟨ρ₀,hρ₀,?_⟩
  intro Pinput hPinput
  let H : A.centers → Fin 3 → ℕ → ℝ := fun i j m => 1 + E i j m * Pinput m
  let Pjet : A.centers → ℕ → ℝ := fun i m => L * V i m * Pinput m
  have hH (i j m) : 1 ≤ H i j m :=
    le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans (hE i j m)) (hPinput m))
  have hPjet (i m) : 0 ≤ Pjet i m :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (hV i m)) (hPinput m)
  choose p _ _ _ hdata using fun i => hall i (H i) (Pjet i) (hH i) (hPjet i)
  refine ⟨p,?_⟩
  intro G hG B hB hBρ hclose s hs hs1 hp τ ε r' hr hτ hτs hε hε1
  have hsmall (i) : L * V₀ i * B < a i := by
    have hh := (lt_div_iff₀ (show 0 < 1 + L * V₀ i by linarith [hL₀ i])).mp
      (hBρ.trans_le (hρa i))
    nlinarith
  have hlocalClose (i) : WeightedEstimates.WeightedBound univ 1 2 (L * V₀ i * B)
      ((A.jetChartMap i G ∘ planeCoordinateIsometry.symm) -
        (A.jetChartMap i F ∘ planeCoordinateIsometry.symm)) := by
    have hh := (hv₀ i (G-F) 1 B zero_lt_one le_rfl hB (hG.sub hF) hclose).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    simp only [ContinuousLinearEquiv.coe_coe] at hh
    change WeightedEstimates.WeightedBound univ 1 2 _
      (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hh
    have hsub : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
        (spaceCoordinates ∘ A.vectorPlaneRead i G) -
          (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
      rw [A.vectorPlaneRead_sub]
      funext x
      exact map_sub spaceCoordinates _ _
    rw [hsub] at hh
    simpa only [A.jetChartMap_plane,L,mul_assoc] using hh
  have hlocalJets (i j m) : WeightedEstimates.WeightedBound (e i j).target s m (H i j m)
      (realTwoJet ((A.jetChartMap i G ∘ planeCoordinateIsometry.symm) ∘ (e i j).symm)) := by
    have hh := he i j m G s (Pinput m) hs hs1 (hPinput m) hG (hp m)
    apply (show WeightedEstimates.WeightedBound (e i j).target s m (E i j m * Pinput m)
      (realTwoJet ((A.jetChartMap i G ∘ planeCoordinateIsometry.symm) ∘ (e i j).symm)) from
      by simpa only [A.jetChartMap_plane] using hh).mono_const
    exact le_add_of_nonneg_left zero_le_one
  have hprefix (i m j) (hj : j ≤ m+2) : WeightedEstimates.WeightedBound (U₀ i) 1 j
      (Pjet i m / (s : ℝ)^(j-2)) (A.jetChartMap i G) := by
    have hread := (hv i m G s (Pinput m) hs hs1 (hPinput m) hG (hp m) j (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    have hcoordinate := weightedBound_comp_isometry planeCoordinateIsometry
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) hread
    have heq : (spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry =
        A.jetChartMap i G := by
      funext x
      have hx := congrFun (A.jetChartMap_plane i G) (planeCoordinateIsometry x)
      simpa only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hx.symm
    rw [heq] at hcoordinate
    have hjet : WeightedEstimates.WeightedBound univ 1 j
        (Pjet i m / (s : ℝ)^(j-2)) (A.jetChartMap i G) := by
      simpa only [Pjet,L,mul_div_assoc,mul_assoc] using hcoordinate
    exact hjet.restrict_open (hU₀ i)
  choose d hfit hmap hphase' hsupp he' hcut hform using fun i : A.centers =>
    hdata i (A.jetChartMap i G) (A.jetChartMap_smooth i hG) (L * V₀ i * B)
      (mul_nonneg (hL₀ i) hB) (hsmall i) (hlocalClose i) s hs hs1 (hlocalJets i)
      (hprefix i) τ ε r' hr hτ hτs hε hε1
  exact ⟨d,hfit,hmap,hphase',hsupp,he',hcut,hform⟩

/-- The supported cutoff, phase, and coefficient form are constructed from
the fixed atlas weights and phase bases. No solver or cutoff is supplied for
the varying map. -/
theorem uniform_polynomial_atlas_phase_mean_data_all_profiles {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k j, (P i k j).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (hsupport : ∀ i j, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i)
    (hSU₀ : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U₀ i)
    {r ρ R : ℝ} (reference : A.centers → SmallModes.Base → Tensor)
    (hmargin : ∀ i j x, x ∈ U i j →
      ρ + ‖(Q i).Q j‖*r ≤ (Q i).Q j (reference i x) ∧
      (Q i).Q j (reference i x) ≤ R - ‖(Q i).Q j‖*r)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (Pinput : ℕ → ℝ), (∀ m, 0 ≤ Pinput m) →
    ∃ p : ∀ i : A.centers, Fin 3 → ChartedMeanProfile (P i),
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ₀ → A.WeightedBound 1 2 B (G-F) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (Pinput m) G) →
        ∀ (τ ε r' : ℝ), r' ≤ r → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
        ∃ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s r' ρ R (reference i),
          (∀ i, (d i).Fits (p i)) ∧
          (∀ i, (d i).G = A.jetChartMap i G) ∧
          (∀ i, (d i).phase = fun j =>
            phaseLinear (w i j • (Q i).ξ j) ∘ planeCoordinateIsometry) ∧
          (∀ i, (d i).support = fun _ => A.chartWeightCompact i) ∧
          (∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j)) ∧
          (∀ i j x, x ∈ ((d i).solver j).e.source →
            ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) ∧
          (∀ i j x, x ∈ ((d i).solver j).e.source →
            ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) ∧
          (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) := by
  classical
  let ξ := fun i j => w i j • (Q i).ξ j
  have hξ (i j) : ξ i j ≠ 0 := smul_ne_zero (hw i j) ((Q i).nonzero j)
  let e := fun i j => linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j)
  let φ : A.centers → Fin 3 → JetPolynomial.Base → ℝ :=
    fun i j => phaseLinear (ξ i j) ∘ planeCoordinateIsometry
  have hφ (i j) : ContDiff ℝ ∞ (φ i j) :=
    (phaseLinear (ξ i j)).contDiff.comp planeCoordinateIsometry.contDiff
  have hphase (i j) : coordinatePhase (φ i j) = phaseLinear (ξ i j) := by
    funext x
    change phaseLinear (ξ i j) (planeCoordinateIsometry (planeCoordinateIsometry.symm x)) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  let ψ := fun i j => A.phaseWeightCutoff i (e i j)
    (linearPhaseChart_smooth (ξ i j) (hξ i j) (U i j) (hU i j)).2.contDiffOn
    (hsupport i j) (w i j)
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.uniform_polynomial_input_atlas_mean_data_all_profiles P hP F hF Ω U K hΩ hU hK hUK hKΩ
    ξ hξ hImm (fun i j x hx => good_smul (hw i j) (hgood i j x hx))
    (fun i _ => A.chartWeightCompact i) hsupport U₀ hU₀ K₀ hU₀K (fun i _ => hSU₀ i)
    φ hφ hphase ψ (fun i j => (Q i).Q j) reference hmargin
  refine ⟨ρ₀,hρ₀,?_⟩
  intro Pinput hPinput
  obtain ⟨p,hdata⟩ := hall Pinput hPinput
  refine ⟨p,?_⟩
  intro G hG B hB hBρ hclose s hs hs1 hp τ ε r' hr hτ hτs hε hε1
  obtain ⟨d,hfit,hmap,hphases,hsupp,he,hcut,hform⟩ :=
    hdata G hG B hB hBρ hclose s hs hs1 hp τ ε r' hr hτ hτs hε hε1
  refine ⟨d,hfit,hmap,hphases,hsupp,?_,?_,?_,?_⟩
  · intro i j
    rw [hphases i]
    exact hphase i j
  · intro i j x hx
    have hx' : x ∈ (e i j).source := by simpa only [he i j] using hx
    calc
      ((d i).data j).cutoff (((d i).solver j).e x) = ψ i j (((d i).solver j).e x) :=
        hcut i j _
      _ = ψ i j (e i j x) := congrArg (ψ i j)
        (congrArg (fun e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base => e x) (he i j))
      _ = A.planeWeight i x / w i j := A.phaseWeightCutoff_apply i (e i j)
        (linearPhaseChart_smooth (ξ i j) (hξ i j) (U i j) (hU i j)).2.contDiffOn
        (hsupport i j) (w i j) hx'
  · intro i j x _
    rw [hform i j]
  · intro i j x hx
    have hx' : x ∈ (e i j).source :=
      A.planeWeight_support_chart i (e i j) (hsupport i j) hx
    simpa only [he i j] using hx'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformPolynomialSmallIncrement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformPolynomialSmallFiberSpace
local instance uniformPolynomialSmallDualAdd_rc5bd98_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformPolynomialSmallDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformPolynomialSmallFiberNormed
local instance uniformPolynomialSmallSectionNormed_rc5bd98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformPolynomialSmallSectionSpace_rc5bd98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_polynomial_atlas_small_increment
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (Ql : A.centers → Fin 3 → Fin nq → Expression)
    (hQl : ∀ i k l, (Ql i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Ql)
    (hlin : A.PolynomialLinearRepresentation Pol Ql)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (hsupport : ∀ i j, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i)
    (hSU₀ : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U₀ i)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (hmargin : ∀ i j x, x ∈ U i j →
      ρ + ‖(Q i).Q j‖*r₁ ≤ (Q i).Q j (A.tensorPlaneRead i reference x) ∧
      (Q i).Q j (A.tensorPlaneRead i reference x) ≤ R - ‖(Q i).Q j‖*r₁)
    (hImmQ : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgoodQ : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x))
    (Ωp : A.centers → Set JetPolynomial.Base) (hΩp : ∀ i, IsOpen (Ωp i))
    (KΩp : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩpK : ∀ i, Ωp i ⊆ KΩp i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ωp i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ωp i)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m)
    (hPF : ∀ m, A.ShiftedBound 2 m 1 (P m) F) (q : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (Ql i)))
        (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η₀ → 0 < δ → δ ≤ τ →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (Ql i)))
            (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))))^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  classical
  obtain ⟨ρd,hρd,halldata⟩ := A.uniform_polynomial_atlas_phase_mean_data_all_profiles Ql hQl F hF Q w hw Ω U K
    hΩ hU hK hUK hKΩ hImm hgood hsupport U₀ hU₀ K₀ hU₀K hSU₀
    (fun i => A.tensorPlaneRead i reference) hmargin
  obtain ⟨p,hdata⟩ := halldata P hP
  have hzero : A.WeightedBound 1 2 0 (F-F) := by
    simp only [sub_self]
    intro i
    have he : localize (i : M) (A.weight i) (0 : M → Space) =
        (fun _ : JetPolynomial.Base => (0 : Space)) := by
      funext x
      simp [localize]
    rw [he]
    exact weightedBound_zero (univ : Set JetPolynomial.Base) 1 2
  obtain ⟨d₀,_,_,hphase₀,_,hlinear₀,_,_,_⟩ := hdata F hF 0 le_rfl hρd hzero
    1 zero_lt_one le_rfl hPF 1 0 r₁ le_rfl zero_lt_one le_rfl le_rfl zero_le_one
  have hφ₀ : (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) =
      A.linearAtlasPhase Q w := by
    funext a
    unfold freeGlobalPhase linearAtlasPhase
    rw [hphase₀ a.1]
  have hgoodQ' : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)) x) := by
    simpa only [hφ₀] using hgoodQ
  obtain ⟨r,D₀,hr,hD₀,hDr,hsmall⟩ := A.profiled_polynomial_atlas_small_increment Pol hPol Ql hQl hquad hlin
    F hF hr₁ hρ reference href p d₀ Q w hw hlinear₀ hImmQ hgoodQ' Ωp hΩp KΩp hΩpK hweight houter P hP q
  refine ⟨r,hr,?_⟩
  intro C hC
  obtain ⟨ρs,η₀,B,T,hρs,hη₀,hη₁,hB,hT,hstep⟩ := hsmall C hC
  refine ⟨min ρd ρs,η₀,B,T,lt_min hρd hρs,hη₀,hη₁,hB,hT,?_⟩
  intro G hG b hb hbr hclose s hs hs1 hp H hH hsym hnear hHC τ δ ε hτ hτs hε hε1 hη hδ hδτ
  have hrealize := hstep G hG b hb (hbr.trans_le (min_le_right _ _)) hclose
    s hs hs1 hp H hH hsym hnear hHC
  obtain ⟨d,hfit,hmap,hphase,hsupport',_,hcut,hform,hsup⟩ :=
    hdata G hG b hb (hbr.trans_le (min_le_left _ _)) hclose s hs hs1 hp τ ε (D₀*r) hDr hτ hτs hε hε1
  have hph (i) : (d i).phase = (d₀ i).phase := (hphase i).trans (hphase₀ i).symm
  have hK' (i j) : (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    rw [hsupport' i]
  exact hrealize τ δ ε hτ hτs hε hε1 hη hδ hδτ d hfit hph hmap hcut hform hsup hK'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CompactGeometryPolynomialIncrement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.compactPolynomialSmallFiberSpace
local instance compactPolynomialSmallDualAdd_rc5bd98_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.compactPolynomialSmallDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.compactPolynomialSmallFiberNormed
local instance compactPolynomialSmallSectionNormed_rc5bd98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance compactPolynomialSmallSectionSpace_rc5bd98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Compact good phase geometry yields the actual small increment; no
mean data or linear solver is an input. -/
theorem compact_geometry_polynomial_increment
    {n : A.centers → ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hImm : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (hpos : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      0 < (Q i).Q j (A.tensorPlaneRead i reference x))
    (hgoodQ : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x))
    : ∃ loss : ℕ, ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) →
    (∀ m, A.ShiftedBound 2 m 1 (P m) F) → ∀ q : ℕ,
    ∃ r : ℝ, 0 < r ∧ ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → τ/s+ε/τ^loss ≤ η₀ → 0 < δ → δ ≤ τ →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s+ε/τ^loss)^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  obtain ⟨Ql,hQl,hquad,hlin⟩ := A.full_linearized_representatives Pol hPol
  obtain ⟨Ωp,KΩp,hΩp,hΩpK,hweight,houter⟩ := A.exists_outer_domains
  refine ⟨max (Finset.univ.sup (fun i : A.centers => tensorLoss (Ql i)))
    (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i))),?_⟩
  intro P hP hPF q
  obtain ⟨d⟩ := A.exists_phaseMeanDomains F hF Q hImm hgood
    (fun i => A.tensorPlaneRead i reference)
    (fun i => (A.tensorPlaneRead_smooth i href).continuous) hpos
  apply A.uniform_polynomial_atlas_small_increment Pol hPol Ql hQl hquad hlin F hF Q w hw d.Ω d.U d.K
    d.openΩ d.openU d.compactK d.UK d.KΩ d.immersion d.good d.support
    d.U₀ d.openU₀ d.K₀ d.U₀K₀ d.supportU₀ d.r_pos d.ρ_pos reference href d.margin
    ?_ hgoodQ Ωp hΩp KΩp hΩpK hweight houter P hP hPF q
  intro k l x hx
  apply hImm k x
  exact Set.image_mono (A.quadraticOverlapCompact_subset
    (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
    (fun a => isClosed_tsupport (A.weight a.1)) k l) hx

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MetricPolynomialIncrement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual metric-adapted immersion supplies all the small-increment geometry. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricPolynomialSmallFiberSpace
local instance metricPolynomialSmallDualAdd_rc5bd98_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricPolynomialSmallDualSmul
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricPolynomialSmallFiberNormed
local instance metricPolynomialSmallSectionNormed_rc5bd98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricPolynomialSmallSectionSpace_rc5bd98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- All geometric and mean-solver inputs are constructed from the metric and
immersion. Only the nearby map's explicit analytic bounds remain. -/
theorem polynomial_small_increment_oai (d : MetricGoodPhaseData g F)
    {n : d.A.centers → ℕ}
    (Pol : ∀ i : d.A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ loss : ℕ, ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) →
    (∀ m, d.A.ShiftedBound 2 m 1 (P m) F) → ∀ q : ℕ,
    ∃ r : ℝ, 0 < r ∧ ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → d.A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, d.A.ShiftedBound 2 m s (P m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖d.A.tensorEncode H x - d.A.tensorEncode g.inner x‖ ≤ r/2) →
      (∀ m, d.A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → τ/s+ε/τ^loss ≤ η₀ → 0 < δ → δ ≤ τ →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, d.A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, d.A.TensorWeightedBound τ m (T m*(δ*(τ/s+ε/τ^loss)^(q+1)+δ^3/τ))
          (d.A.atlasPolynomialMetric Pol ε (G+X)-d.A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  exact d.A.compact_geometry_polynomial_increment Pol hPol F hF d.Q d.w
    (fun i j => (d.weight_pos i j).ne') d.immersion d.pure_good g.inner
    g.contMDiff d.metric_positive d.quadratic_good

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_small_increment_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_small_increment_oai.{u_1}
