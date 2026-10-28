-- Prove2me | solution 1 for OAI.CoulombAtom.actual_uniform_upper_deficit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:44:36.191059+00:00
-- url     : https://prove2.me/submissions/127de9b3-ca28-4e60-bd04-feed8fe61951

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_sharp_joint_selected_patch

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoulombCoercivity

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

end CoulombCoercivity

lemma graphFormVector_admissible {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖ ^ 2 = 1) : FormAdmissible (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    exact ((mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property
      (i, a)) φ hφ hcφ
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s
  · have hmass := graphValue_norm_sq F
    rw [hn] at hmass
    simpa only [lp_norm_sq, graphComponent_apply, graphFormVector] using hmass.symm
  · intro s i
    exact nuclear_integrable i (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  · intro s i j hij
    exact pair_integrable i j hij (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))

lemma graphFormVector_admissibleGraph_value {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (s : Spins N) :
    (graphFormVector (admissibleGraph ψ hψ)).value s =ᵐ[volume] ψ.value s := by
  simpa only [graphFormVector, admissibleGraph, WithLp.ofLp_toLp,
    admissibleWeakGraph_value] using (hψ.1 s).coeFn_toLp

lemma graphFormVector_admissibleGraph_gradient {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphFormVector (admissibleGraph ψ hψ)).gradient s i a =ᵐ[volume] ψ.gradient s i a := by
  simpa only [graphFormVector, admissibleGraph, WithLp.ofLp_toLp,
    admissibleWeakGraph_gradient] using (hψ.2.1 s i a).coeFn_toLp

lemma admissibleGraph_norm {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ) :
    ‖fermionGraphValue N (admissibleGraph ψ hψ)‖ ^ 2 = 1 := by
  calc
    _ = ∑ s : Spins N, ∫ x, ‖(graphFormVector (admissibleGraph ψ hψ)).value s x‖ ^ 2 := by
      rw [graphValue_norm_sq]
      simp only [lp_norm_sq, graphComponent_apply, graphFormVector]
    _ = ∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      apply integral_congr_ae
      filter_upwards [graphFormVector_admissibleGraph_value ψ hψ s] with x hx
      rw [hx]
    _ = 1 := hψ.2.2.2.2.1

lemma formEnergy_congr_ae {N : ℕ} (Z : ℝ) (ψ φ : FormVector N)
    (hv : ∀ s, ψ.value s =ᵐ[volume] φ.value s)
    (hg : ∀ s i a, ψ.gradient s i a =ᵐ[volume] φ.gradient s i a) :
    formEnergy Z ψ = formEnergy Z φ := by
  have hk : (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖φ.gradient s i a x‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    apply integral_congr_ae
    filter_upwards [hg s i a] with x hx
    rw [hx]
  have hn : (∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖) =
      ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖φ.value s x‖ ^ 2 / ‖x i‖ := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hv s] with x hx
    rw [hx]
  have hp : (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖ else 0) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then ∫ x, ‖φ.value s x‖ ^ 2 / ‖x i - x j‖ else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · apply integral_congr_ae
      filter_upwards [hv s] with x hx
      rw [hx]
    · rfl
  unfold formEnergy
  rw [hk, hn, hp]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_QuantumSectorNearMinimizer
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

theorem quantum_sector_near_minimizer (Z : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖ ^ 2 = 1 ∧
      formEnergy Z (graphFormVector F) < energy Z N + ε := by
  have hex : ∃ ψ : FormVector N, FormAdmissible ψ ∧
      formEnergy Z ψ < energy Z N + ε := by
    by_cases hN : N = 0
    · subst N
      obtain ⟨ψ, hψ⟩ := formDomain_nonempty 0
      refine ⟨ψ, hψ, ?_⟩
      simpa only [formEnergy, Fin.sum_univ_zero, Finset.sum_const_zero,
        mul_zero, sub_zero, add_zero, energy, ↓reduceIte, zero_add] using hε
    · have hh : sInf {e | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} <
          energy Z N + ε := by
        simpa only [energy, ite_eq_right hN] using (lt_add_of_pos_right (energy Z N) hε)
      obtain ⟨e, ⟨ψ, hψ, he⟩, he'⟩ := exists_lt_of_csInf_lt (formValues_nonempty Z N) hh
      exact ⟨ψ, hψ, he ▸ he'⟩
  obtain ⟨ψ, hψ, he⟩ := hex
  refine ⟨admissibleGraph ψ hψ, admissibleGraph_norm ψ hψ, ?_⟩
  have heq := formEnergy_congr_ae Z (graphFormVector (admissibleGraph ψ hψ)) ψ
    (graphFormVector_admissibleGraph_value ψ hψ)
    (graphFormVector_admissibleGraph_gradient ψ hψ)
  exact heq ▸ he

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FineSmearingPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombNeumann.cubePartition_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_memLp {b : ℝ} (hb : 0 < b) : MemLp (varthetaScaled b) (5/3) := by
  apply bounded_compact_memLp (varthetaScaled_measurable b) (isCompact_closedBall (0:Space) (Real.sqrt 3*b))
  · intro x hx
    simpa only [mem_closedBall,dist_zero_right] using varthetaScaled_support_bound hb x hx
  · intro x
    rw [abs_of_nonneg (varthetaScaled_nonneg hb x)]
    exact varthetaScaled_le hb x

lemma varthetaScaled_potential_le {b : ℝ} (hb : 0 < b) {x : Space} (hx : x ≠ 0) :
    tfPotential (varthetaScaled b) x ≤ 1/‖x‖ := by
  have hh := radial_potential_le_point (varthetaScaled_integrable hb) (varthetaScaled_memLp hb)
    (varthetaScaled_nonneg hb) (fun _ _ h => varthetaScaled_radial b h)
    (by positivity : 0 ≤ Real.sqrt 3*b) (varthetaScaled_support_bound hb) hx
  simpa only [integral_varthetaScaled hb] using hh

lemma varthetaScaled_potential_eq_far {b : ℝ} (hb : 0 < b) {x : Space}
    (hx : Real.sqrt 3*b ≤ ‖x‖) : tfPotential (varthetaScaled b) x = 1/‖x‖ := by
  have hh := tfPotential_newton_exterior_closed (varthetaScaled_integrable hb)
    (varthetaScaled_memLp hb) (fun _ _ h => varthetaScaled_radial b h)
    (by positivity : 0 < Real.sqrt 3*b) (varthetaScaled_support_bound hb) hx
  simpa only [integral_varthetaScaled hb] using hh

lemma retainedSmear_potential {N : ℕ} {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) :
    tfPotential (retainedSmear b S x) y = ∑ i ∈ S, tfPotential (varthetaScaled b) (y-x i) := by
  simp only [tfPotential,retainedSmear,Finset.sum_div]
  rw [integral_finsetSum _ (fun i _ => translated_pole_integrable
    (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y (x i))]
  exact Finset.sum_congr rfl (fun i _ => integral_translated_pole (varthetaScaled b) y (x i))

theorem retainedSmear_potential_loss {N : ℕ} {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hxy : ∀ i ∈ S, x i ≠ y) :
    0 ≤ (∑ i ∈ S, 1/‖y-x i‖)-tfPotential (retainedSmear b S x) y ∧
      (∑ i ∈ S, 1/‖y-x i‖)-tfPotential (retainedSmear b S x) y ≤
        ∑ i ∈ S, (ball y (Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  rw [retainedSmear_potential hb,←Finset.sum_sub_distrib]
  have hh (i : Fin N) (hi : i ∈ S) :
      0 ≤ 1/‖y-x i‖-tfPotential (varthetaScaled b) (y-x i) ∧
      1/‖y-x i‖-tfPotential (varthetaScaled b) (y-x i) ≤
        (ball y (Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
    have hn := tfPotential_nonneg (ae_of_all _ (varthetaScaled_nonneg hb)) (y-x i)
    have hle := varthetaScaled_potential_le hb (sub_ne_zero.mpr (hxy i hi).symm)
    refine ⟨sub_nonneg.mpr hle,?_⟩
    by_cases hB : x i ∈ ball y (Real.sqrt 3*b)
    · rw [indicator_of_mem hB]
      exact sub_le_self _ hn
    · rw [indicator_of_notMem hB,varthetaScaled_potential_eq_far hb (by
        simpa only [mem_ball,dist_eq_norm,norm_sub_rev,not_lt] using hB)]
      simp only [sub_self,le_refl]
  exact ⟨Finset.sum_nonneg (fun i hi => (hh i hi).1),
    Finset.sum_le_sum (fun i hi => (hh i hi).2)⟩

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialRotation
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
namespace CoulombAtom

lemma averagedPacket_nonneg (p : Space) (r : ℝ) (x : Space) : 0 ≤ averagedPacket p r x :=
  integral_nonneg (fun g => packetDensity_nonneg (rotate g p) r x)

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialShellPotential
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAnalysis

lemma tfPotential_annular_bounds {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5/3)) (hr : IsRadial ρ) (hn : ∀ y, 0 ≤ ρ y)
    (hm : ∫ y, ρ y = 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖y‖ ∧ ‖y‖ ≤ b) (x : TFSpace) :
    1/max ‖x‖ b ≤ tfPotential ρ x ∧ tfPotential ρ x ≤ 1/max ‖x‖ a := by
  rw [tfPotential_radial_max h1 hp hr (ha.le.trans hab) (fun y hy => (hs y hy).2)]
  have ham : 0 < max ‖x‖ a := ha.trans_le (le_max_right _ _)
  have hbm : 0 < max ‖x‖ b := (ha.trans_le hab).trans_le (le_max_right _ _)
  have hind (y : TFSpace) : ‖ρ y/max ‖x‖ ‖y‖‖ ≤ ρ y/max ‖x‖ a := by
    by_cases hy : ρ y = 0
    · simp [hy]
    · rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hn _) (le_max_left _ _ |>.trans' (norm_nonneg _)))]
      exact div_le_div_of_nonneg_left (hn _) ham (max_le_max_left _ (hs y hy).1)
  have hi : Integrable (fun y => ρ y/max ‖x‖ ‖y‖) :=
    (h1.div_const _).mono' (h1.aemeasurable.div
      ((continuous_const.max continuous_norm).aemeasurable)).aestronglyMeasurable
      (Eventually.of_forall hind)
  constructor
  · rw [← hm, ← integral_div]
    apply integral_mono (h1.div_const _) hi
    intro y
    by_cases hy : ρ y = 0
    · simp [hy]
    · have hp0 : 0 < max ‖x‖ ‖y‖ := ham.trans_le (max_le_max_left _ (hs y hy).1)
      exact div_le_div_of_nonneg_left (hn _) hp0 (max_le_max_left _ (hs y hy).2)
  · rw [← hm, ← integral_div]
    exact integral_mono hi (h1.div_const _) (fun y => (le_abs_self _).trans (hind y))

end CoulombAnalysis
namespace CoulombAtom

lemma averagedPacket_annulus (p : Space) {r : ℝ} (hr : 0 < r) {x : Space}
    (hx : averagedPacket p r x ≠ 0) : ‖p‖-r ≤ ‖x‖ ∧ ‖x‖ ≤ ‖p‖+r := by
  refine ⟨?_,averagedPacket_support p hr hx⟩
  by_contra hn
  apply hx
  unfold averagedPacket
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro g
  by_contra hg
  have hd := packetDensity_support (rotate g p) hr hg
  have hh := norm_add_le (rotate g p-x) x
  rw [sub_add_cancel,(rotate g).norm_map,norm_sub_rev] at hh
  linarith

lemma averagedPacket_potential_bounds (p : Space) {r : ℝ} (hr : 0 < r)
    (hpr : r < ‖p‖) (x : Space) :
    1/max ‖x‖ (‖p‖+r) ≤ CoulombAnalysis.tfPotential (averagedPacket p r) x ∧
      CoulombAnalysis.tfPotential (averagedPacket p r) x ≤ 1/max ‖x‖ (‖p‖-r) :=
  CoulombAnalysis.tfPotential_annular_bounds (averagedPacket_integrable p hr)
    (averagedPacket_memLp p hr) (averagedPacket_radial p r) (averagedPacket_nonneg p r)
    (averagedPacket_mass p hr) (by linarith) (by linarith)
    (fun _ hh => averagedPacket_annulus p hr hh) x

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellCoulombDuality
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAnalysis

lemma tfCoulomb_density_bound (R : ℝ) {ρ : TFSpace → ℝ}
    (hp : MemLp ρ (5/3)) (hs : Function.support ρ ⊆ ball 0 R)
    (hn : ∀ x, 0 ≤ ρ x) (hmass : ∫ x, ρ x = 1) {C : ℝ}
    (hbound : ∀ x, tfPotential ρ x ≤ C) (f : TFLp (ballMeasure R)) :
    (∫ x, tfPotential ρ x*f x ∂ballMeasure R)^2 ≤ C*tfCoulombL R f f := by
  obtain ⟨q,hq,hpot⟩ := exists_patch_density R hp hs
  have hmassq : (∫ x, q x ∂ballMeasure R) = 1 := by
    rw [integral_congr_ae hq,ballMeasure,← integral_indicator measurableSet_ball]
    convert hmass using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    by_cases hx : x ∈ ball (0 : TFSpace) R
    · simp [hx]
    · have hz : ρ x = 0 := Function.notMem_support.mp (fun hh => hx (hs hh))
      simp [hx,hz]
  have hself : tfCoulombL R q q ≤ C := by
    rw [tfCoulombL_potential,← mul_one C,← hmassq,← integral_const_mul]
    apply integral_mono_ae (tfBallPotential_mul_integrable R q q)
      (((Lp.memLp q).integrable (Fact.out : (1:ENNReal) ≤ 5/3)).const_mul C)
    filter_upwards [hq] with x hx
    rw [hpot x,hx]
    exact mul_le_mul_of_nonneg_right (hbound x) (hn x)
  have hpair : tfCoulombL R q f = ∫ x, tfPotential ρ x*f x ∂ballMeasure R := by
    rw [tfCoulombL_potential]
    simp_rw [hpot]
  rw [← hpair]
  exact (tfCoulombL_pair_sq_le R q f).trans
    (mul_le_mul_of_nonneg_right hself (tfCoulombL_nonneg R f))

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

lemma shell_coulomb_test_bound {R : ℝ} (f : TFLp (ballMeasure R)) (p : Space)
    {r : ℝ} (hr : 0 < r) (hpr : r < ‖p‖) (hR : ‖p‖+r < R) :
    (∫ x, tfPotential (averagedPacket p r) x*f x ∂ballMeasure R)^2 ≤
      (1/(‖p‖-r))*tfCoulombL R f f := by
  apply tfCoulomb_density_bound R (averagedPacket_memLp p hr) _
    (averagedPacket_nonneg p r) (averagedPacket_mass p hr)
  · intro x
    exact (averagedPacket_potential_bounds p hr hpr x).2.trans
      (one_div_le_one_div_of_le (by linarith) (le_max_right _ _))
  · intro x hx
    exact mem_ball_zero_iff.mpr ((averagedPacket_support p hr hx).trans_lt hR)

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAtom
open CoulombAnalysis

lemma shell_potential_tendsto (p : Space) (hp : 0 < ‖p‖) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hpr : ∀ n, r n < ‖p‖)
    (hlim : Tendsto r atTop (𝓝 0)) (x : Space) :
    Tendsto (fun n => tfPotential (averagedPacket p (r n)) x) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
  have hmax : max ‖x‖ ‖p‖ ≠ 0 := (hp.trans_le (le_max_right _ _)).ne'
  have hplus : Tendsto (fun n => 1/max ‖x‖ (‖p‖+r n)) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
    convert! tendsto_const_nhds.div
      (tendsto_const_nhds.max (tendsto_const_nhds.add hlim)) (by simpa only [add_zero] using hmax) using 1; simp
  have hminus : Tendsto (fun n => 1/max ‖x‖ (‖p‖-r n)) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
    convert! tendsto_const_nhds.div
      (tendsto_const_nhds.max (tendsto_const_nhds.sub hlim)) (by simpa only [sub_zero] using hmax) using 1; simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hplus hminus
    (fun n => (averagedPacket_potential_bounds p (hr n) (hpr n) x).1)
    (fun n => (averagedPacket_potential_bounds p (hr n) (hpr n) x).2)

lemma shell_potential_pair_tendsto (μ : Measure Space) {f : Space → ℝ}
    (hf : Integrable f μ) (p : Space) (hp : 0 < ‖p‖) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hpr : ∀ n, r n ≤ ‖p‖/2)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, tfPotential (averagedPacket p (r n)) x*f x ∂μ) atTop
      (𝓝 (∫ x, (1/max ‖x‖ ‖p‖)*f x ∂μ)) := by
  have hpr' (n : ℕ) : r n < ‖p‖ := by linarith [hpr n]
  apply tendsto_integral_of_dominated_convergence (fun x => (2/‖p‖)*‖f x‖)
  · intro n
    exact ((tfPotential_continuous (averagedPacket_integrable p (hr n))
      (averagedPacket_memLp p (hr n))).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · exact hf.norm.const_mul _
  · intro n
    apply Eventually.of_forall
    intro x
    rw [norm_mul,Real.norm_eq_abs]
    have hh := averagedPacket_potential_bounds p (hr n) (hpr' n) x
    have hn : 0 ≤ tfPotential (averagedPacket p (r n)) x :=
      (by positivity : 0 ≤ 1/max ‖x‖ (‖p‖+r n)).trans hh.1
    rw [abs_of_nonneg hn]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hden : ‖p‖/2 ≤ max ‖x‖ (‖p‖-r n) :=
      (by linarith [hpr n] : ‖p‖/2 ≤ ‖p‖-r n).trans (le_max_right _ _)
    have hh' := one_div_le_one_div_of_le (by positivity : 0 < ‖p‖/2) hden
    exact hh.2.trans (by convert hh' using 1; ring)
  · exact Eventually.of_forall fun x =>
      (shell_potential_tendsto p hp hr hpr' hlim x).mul_const (f x)

end CoulombAtom
namespace CoulombAnalysis
open CoulombAtom

theorem tfCoulomb_truncated_duality {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (f : TFLp (ballMeasure R)) :
    (∫ x, (1/max ‖x‖ t)*f x ∂ballMeasure R)^2 ≤ (1/t)*tfCoulombL R f f := by
  let p : Space := t • radialAxis
  have hp : ‖p‖ = t := by simp [p,norm_smul,abs_of_pos ht]
  let δ : ℝ := min (t/2) ((R-t)/2)
  have hd : 0 < δ := by dsimp [δ]; positivity
  let r : ℕ → ℝ := fun n => δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrd (n : ℕ) : r n ≤ δ := by
    exact div_le_self hd.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hrt (n : ℕ) : r n ≤ t/2 := (hrd n).trans (min_le_left _ _)
  have hrR (n : ℕ) : ‖p‖+r n < R := by
    have hh := (hrd n).trans (min_le_right (t/2) ((R-t)/2))
    rw [hp]
    linarith
  have hpr (n : ℕ) : r n < ‖p‖ := by rw [hp]; linarith [hrt n]
  have hlim : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hpair := shell_potential_pair_tendsto (ballMeasure R)
    ((Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)) p (by rwa [hp]) hr
    (fun n => by simpa only [hp] using hrt n) hlim
  rw [hp] at hpair
  have hcoef : Tendsto (fun n => (1/(‖p‖-r n))*tfCoulombL R f f) atTop
      (𝓝 ((1/t)*tfCoulombL R f f)) := by
    convert! (tendsto_const_nhds.div
      (tendsto_const_nhds.sub hlim) (show ‖p‖-0 ≠ 0 by rw [sub_zero,hp]; exact ht.ne')).mul_const
      (tfCoulombL R f f) using 1; simp only [hp,sub_zero]
  exact le_of_tendsto_of_tendsto (hpair.pow 2) hcoef
    (Eventually.of_forall fun n => shell_coulomb_test_bound f p (hr n) (hpr n) (hrR n))

theorem tfPatchGap_truncated_control {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    (∫ x, (1/max ‖x‖ t)*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R)^2 ≤
      (2/t)*tfPatchGap R T hT Φ σ := by
  have hh := tfCoulomb_truncated_duality ht htR (σ-tfPatchMinimizer R T hT Φ)
  have he := mul_le_mul_of_nonneg_left (tfPatchGap_coulomb_le R T hT Φ hσ)
    (by positivity : 0 ≤ 1/t)
  exact hh.trans (by convert he using 1; ring)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegratedLipschitzControl
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

lemma weightedPatchTestSquare_nonneg {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (g : TFSpace → ℝ)
    (u : Configuration M) : 0 ≤ weightedPatchTestSquare ψ s Z lam y R hb S g u :=
  mul_nonneg (formMass_nonneg _) (sq_nonneg _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegratedTruncatedControl
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis
local instance instFactNeENNRealHDivOfNatTop_solutions_5 : Fact ((5/3:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_3_r86c5e4_1 (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_3_r86c5e4_1 (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_3
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_3 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma patch_test_continuous_of_memLp (R : ℝ) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    Continuous (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) := by
  have he : (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) =
      tfPatchPair R (hm.toLp g) := by
    funext f
    rw [tfPatchPair_apply]
    exact integral_congr_ae (hm.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])
  rw [he]
  exact (tfPatchPair R (hm.toLp g)).continuous

lemma truncated_kernel_memLp (R : ℝ) {t : ℝ} (ht : 0 < t) :
    MemLp (fun x : TFSpace => 1/max ‖x‖ t) (5/2) (ballMeasure R) := by
  have hc : Continuous (fun x : TFSpace => 1/max ‖x‖ t) :=
    continuous_const.div (continuous_norm.max continuous_const)
      (fun x => (ht.trans_le (le_max_right ‖x‖ t)).ne')
  apply MemLp.of_bound hc.aestronglyMeasurable (1/t)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le ht (le_max_right _ _)

local instance instFactNeENNRealHDivOfNatTop_solutions_6_r86c5e4_1 : Fact ((5/2:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
lemma weightedPatchTestSquare_memLp_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    AEMeasurable (weightedPatchTestSquare ψ s Z lam y R hb S g) := by
  have hmass := (hψ.coreSlice_mass_integrable s).aestronglyMeasurable.aemeasurable
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  have hr := conditionalPatchMinimizer_aemeasurable hψ s Z lam y R
  have hp := (patch_test_continuous_of_memLp R hm).measurable.comp_aemeasurable
    (hs.aemeasurable.sub hr)
  exact hmass.mul (hp.pow_const 2)

lemma weightedPatchTruncatedSquare_le {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M)) (u : Configuration M) :
    weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t) u ≤
      (2/t)*weightedPatchGap ψ s Z lam y R hb S u := by
  have hh := mul_le_mul_of_nonneg_left
    (tfPatchGap_truncated_control ht hR tfKinetic tfKinetic_pos
      (conditionalPatchField ψ s Z lam y R u) (retainedPatchLp_nonneg hb (S u) u y R))
    (formMass_nonneg (coreSlice ψ s u))
  simpa only [weightedPatchTestSquare,weightedPatchGap,mul_left_comm,mul_assoc] using hh

lemma weightedPatchTruncatedSquare_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t)) := by
  apply (hi.const_mul (2/t)).mono'
    (weightedPatchTestSquare_memLp_aemeasurable hψ s Z lam y R hb S hS
      (truncated_kernel_memLp R ht)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (weightedPatchTestSquare_nonneg ψ s Z lam y R hb S _ u)]
    exact weightedPatchTruncatedSquare_le ψ s Z lam y ht hR hb S u

lemma integral_weightedPatchTruncatedSquare_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    (∫ u, weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t) u) ≤
      (2/t)*(∫ u, weightedPatchGap ψ s Z lam y R hb S u) := by
  rw [←integral_const_mul]
  exact integral_mono (weightedPatchTruncatedSquare_integrable hψ s Z lam y ht hR hb S hS hi)
    (hi.const_mul _) (weightedPatchTruncatedSquare_le ψ s Z lam y ht hR hb S)

theorem radial_truncated_test_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {r : ℝ} (hr : 0 < r) (hR : r < t-4*b) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestSquare (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      (2/r)*
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
          (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention N y t b c s) u) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  exact integral_weightedPatchTruncatedSquare_le
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) hψ.sobolevVector c)
    s Z lam y hr hR hb _ (radialPatchRetention_measurable N y t b c s)
    (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PotentialRecovery
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PotentialRecovery_scope

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma truncated_potential_remainder {R t : ℝ} (ht : 0 < t) (htR : t < R)
    {f : TFSpace → ℝ} (hf : MemLp f (5/3) (ballMeasure R)) :
    |(∫ x, f x/‖x‖ ∂ballMeasure R)-
      (∫ x, (1/max ‖x‖ t)*f x ∂ballMeasure R)| ≤
      ∫ x in ball 0 t, ‖f x‖/‖x‖ := by
  have hi : Integrable (fun x => f x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul hf using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hj : Integrable (fun x => (1/max ‖x‖ t)*f x) (ballMeasure R) := by
    convert! (truncated_kernel_memLp R ht).integrable_mul hf using 1
    all_goals try with_reducible_and_instances rfl
  have hn : Integrable (fun x => ‖f x‖/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul hf.norm using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hb := hn.indicator (measurableSet_ball (x := (0:TFSpace)) (ε := t))
  have he : (∫ x, (ball (0:TFSpace) t).indicator (fun x => ‖f x‖/‖x‖) x ∂ballMeasure R) =
      ∫ x in ball 0 t, ‖f x‖/‖x‖ := by
    rw [integral_indicator measurableSet_ball]
    change (∫ x, ‖f x‖/‖x‖ ∂(volume.restrict (ball 0 R)).restrict (ball 0 t)) = _
    rw [Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball htR.le)]
  rw [←integral_sub hi hj]
  rw [←he,←Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hb
  filter_upwards [ae_restrict_of_ae (ae_ne_point (0:Space))] with x hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  by_cases hxt : ‖x‖ < t
  · rw [indicator_of_mem (by simpa only [mem_ball_zero_iff] using hxt)]
    have hle := one_div_le_one_div_of_le hx0 (le_max_left ‖x‖ t)
    have hpos : 0 ≤ 1/‖x‖-1/max ‖x‖ t := sub_nonneg.mpr hle
    have hid : f x/‖x‖-(1/max ‖x‖ t)*f x = (1/‖x‖-1/max ‖x‖ t)*f x := by ring
    rw [hid,norm_mul,Real.norm_eq_abs,abs_of_nonneg hpos,div_eq_inv_mul]
    have hh := mul_le_mul_of_nonneg_right
      (sub_le_self (1/‖x‖) (by positivity : 0 ≤ 1/max ‖x‖ t)) (norm_nonneg (f x))
    simpa only [one_div,div_eq_inv_mul,mul_one] using hh
  · rw [indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hxt),
      max_eq_left (le_of_not_gt hxt)]
    simp [div_eq_mul_inv,mul_comm]

lemma tfBallPotential_at_zero (R : ℝ) (f : TFLp (ballMeasure R)) :
    tfBallPotential R f 0 = ∫ x, f x/‖x‖ ∂ballMeasure R := by
  simp only [tfBallPotential,zero_sub,norm_neg]

end CoulombAnalysis

end Work_PotentialRecovery_scope

open MeasureTheory Filter
open scoped ENNReal

namespace CoulombAtom

lemma weighted_abs_integrable_and_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w f : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hi : Integrable w μ)
    (hf : AEStronglyMeasurable f μ)
    (hs : Integrable (fun x => w x*(f x)^2) μ) :
    Integrable (fun x => w x*|f x|) μ ∧
      (∫ x, w x*|f x| ∂μ) ≤ Real.sqrt (∫ x, w x ∂μ)*
        Real.sqrt (∫ x, w x*(f x)^2 ∂μ) := by
  let a := fun x => Real.sqrt (w x)
  let b := fun x => Real.sqrt (w x)*|f x|
  have ha : AEStronglyMeasurable a μ := Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable
  have hb : AEStronglyMeasurable b μ := ha.mul hf.norm
  have ha2 (x : α) : a x^2 = w x := Real.sq_sqrt (hw x)
  have hb2 (x : α) : b x^2 = w x*(f x)^2 := by
    dsimp only [b]
    rw [mul_pow,Real.sq_sqrt (hw x),sq_abs]
  have hab (x : α) : a x*b x = w x*|f x| := by
    dsimp only [a,b]
    rw [←mul_assoc,←pow_two,Real.sq_sqrt (hw x)]
  have hma : MemLp a 2 μ := (memLp_two_iff_integrable_sq ha).2 (by simpa only [ha2] using hi)
  have hmb : MemLp b 2 μ := (memLp_two_iff_integrable_sq hb).2 (by simpa only [hb2] using hs)
  have hip : Integrable (fun x => a x*b x) μ := by
    convert! hma.integrable_mul hmb using 1
    all_goals try with_reducible_and_instances rfl
  refine ⟨by simpa only [hab] using hip,?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => Real.sqrt_nonneg (w x))
    (Eventually.of_forall fun x => mul_nonneg (Real.sqrt_nonneg (w x)) (abs_nonneg (f x)))
    (show MemLp a (ENNReal.ofReal 2) μ by simpa using hma)
    (show MemLp b (ENNReal.ofReal 2) μ by simpa using hmb)
  simpa only [hab,Real.rpow_two,ha2,hb2,←Real.sqrt_eq_rpow] using h

lemma finite_weighted_abs_bound {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ : ∀ i, Measure (α i)} {w f : ∀ i, α i → ℝ}
    (hw : ∀ i x, 0 ≤ w i x) (hi : ∀ i, Integrable (w i) (μ i))
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hs : ∀ i, Integrable (fun x => w i x*(f i x)^2) (μ i)) :
    (∑ i, ∫ x, w i x*|f i x| ∂μ i) ≤
      Real.sqrt (∑ i, ∫ x, w i x ∂μ i)*
        Real.sqrt (∑ i, ∫ x, w i x*(f i x)^2 ∂μ i) := by
  calc
    _ ≤ ∑ i, Real.sqrt (∫ x, w i x ∂μ i)*
        Real.sqrt (∫ x, w i x*(f i x)^2 ∂μ i) :=
      Finset.sum_le_sum fun i _ => (weighted_abs_integrable_and_bound (hw i) (hi i) (hf i) (hs i)).2
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le Finset.univ
      (fun i => integral_nonneg (hw i))
      (fun i => integral_nonneg (fun x => mul_nonneg (hw i x) (sq_nonneg _)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ExpectedTruncatedControl
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ExpectedTruncatedControl_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

open CoulombNeumann CoulombAnalysis
local instance instFactNeENNRealHDivOfNatTop_solutions_7 : Fact ((5/3:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_4_r86c5e4_1 (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_4_r86c5e4_1 (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_4
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_4 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

local instance instFactNeENNRealHDivOfNatTop_solutions_8_r86c5e4_1 : Fact ((5/2:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
lemma patchTestError_aestronglyMeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    AEStronglyMeasurable (fun u =>
      ∫ x, g x*(retainedPatchLp hb (S u) u y R-
        tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ s Z lam y R u)) x
          ∂ballMeasure R) := by
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  have hr := conditionalPatchMinimizer_aemeasurable hψ s Z lam y R
  exact ((patch_test_continuous_of_memLp R hm).measurable.comp_aemeasurable
    (hs.aemeasurable.sub hr)).aestronglyMeasurable

lemma weightedPatchTruncatedAbs_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R r : ℝ} (hr : 0 < r) (hR : r < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ r)) :=
  (weighted_abs_integrable_and_bound (fun _ => formMass_nonneg _)
    (hψ.coreSlice_mass_integrable s)
    (patchTestError_aestronglyMeasurable hψ s Z lam y R hb S hS (truncated_kernel_memLp R hr))
    (weightedPatchTruncatedSquare_integrable hψ s Z lam y hr hR hb S hS hi)).1

theorem radial_truncated_absolute_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {r : ℝ} (hr : 0 < r) (hR : r < t-4*b) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestAbs (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/r)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
            (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
            (radialPatchRetention N y t b c s) u)) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let I := (c : Fin N → Fin 2) × Spins (cutOutNumber c)
  let w := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    formMass (coreSlice (orderedCutForm p hp ψ i.1) i.2 u)
  let f := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    ∫ x, (1/max ‖x‖ r)*(retainedPatchLp hb (radialPatchRetention N y t b i.1 i.2 u) u y (t-4*b)-
      tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField (orderedCutForm p hp ψ i.1) i.2 Z lam y (t-4*b) u)) x
      ∂ballMeasure (t-4*b)
  have hχ (c : Fin N → Fin 2) : SobolevVector (orderedCutForm p hp ψ c) :=
    orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hgap (i : I) := radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam
    hg hcg hgn hrad hgs i.1 i.2
  have hcs := finite_weighted_abs_bound (μ := fun i : I => (volume : Measure (Configuration (cutOutNumber i.1))))
    (w := w) (f := f) (fun _ _ => formMass_nonneg _)
    (fun i => (hχ i.1).coreSlice_mass_integrable i.2)
    (fun i => patchTestError_aestronglyMeasurable (hχ i.1) i.2 Z lam y (t-4*b) hb _
      (radialPatchRetention_measurable N y t b i.1 i.2) (truncated_kernel_memLp _ hr))
    (fun i => weightedPatchTruncatedSquare_integrable (hχ i.1) i.2 Z lam y hr hR hb _
      (radialPatchRetention_measurable N y t b i.1 i.2) (hgap i))
  have hmass : (∑ i : I, ∫ u, w i u) = formMass ψ := by
    rw [Fintype.sum_sigma]
    change (∑ c, ∑ s, ∫ u, formMass (coreSlice (orderedCutForm p hp ψ c) s u)) = _
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ.sobolevVector
  rw [hmass,Fintype.sum_sigma,Fintype.sum_sigma] at hcs
  change (∑ c, ∑ s, ∫ u, weightedPatchTestAbs (orderedCutForm p hp ψ c) s Z lam y _ hb
    (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c, ∑ s, ∫ u, weightedPatchTestSquare (orderedCutForm p hp ψ c) s Z lam y _ hb
          (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (radial_truncated_test_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hr hR))
    (Real.sqrt_nonneg _))

end Work_ExpectedTruncatedControl_scope

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

open CoulombAnalysis

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TranslatedShortRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ContDiff

namespace CoulombAnalysis

lemma ball_translation_preserving (y : TFSpace) (R : ℝ) :
    MeasurePreserving (fun x : TFSpace => y+x) (ballMeasure R) (volume.restrict (ball y R)) := by
  have h := (measurePreserving_add_left (volume : Measure TFSpace) y).restrict_preimage
    (measurableSet_ball (x := y) (ε := R))
  have he : (fun x : TFSpace => y+x) ⁻¹' ball y R = ball 0 R := by
    ext x
    simp only [mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero]
  simpa only [he,ballMeasure] using h

lemma setIntegral_translate_ball (y : TFSpace) (R : ℝ) (f : TFSpace → ℝ) :
    (∫ x in ball 0 R, f (y+x)) = ∫ x in ball y R, f x :=
  (ball_translation_preserving y R).integral_comp (MeasurableEquiv.addLeft y).measurableEmbedding f

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FineLocalPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_local_potential_le {b q : ℝ} (hb : 0 < b)
    (y a : Space) (ha : a ≠ y) :
    (∫ z in ball y q, varthetaScaled b (z-a)/‖y-z‖) ≤
      (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) a := by
  by_cases hnear : a ∈ ball y (q+Real.sqrt 3*b)
  · rw [indicator_of_mem hnear]
    calc
      _ ≤ ∫ z : Space, varthetaScaled b (z-a)/‖y-z‖ :=
        setIntegral_le_integral
          (translated_pole_integrable (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y a)
          (Eventually.of_forall fun z => div_nonneg (varthetaScaled_nonneg hb _) (norm_nonneg _))
      _ = tfPotential (varthetaScaled b) (y-a) := integral_translated_pole _ _ _
      _ ≤ _ := varthetaScaled_potential_le hb (sub_ne_zero.mpr ha.symm)
  · rw [indicator_of_notMem hnear]
    apply le_of_eq
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzero : varthetaScaled b (z-a) = 0 := by
      by_contra hne
      have hs := varthetaScaled_support_bound hb (z-a) hne
      have hd := dist_triangle a z y
      have hfar : q+Real.sqrt 3*b ≤ dist a y := le_of_not_gt hnear
      have hclose : dist z y < q := hz
      rw [←dist_eq_norm,dist_comm z a] at hs
      linarith
    simp only [hzero,zero_div,Pi.zero_apply]

lemma retainedSmear_local_potential_le {N : ℕ} {b q : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hxy : ∀ i ∈ S, x i ≠ y) :
    (∫ z in ball y q, retainedSmear b S x z/‖y-z‖) ≤
      ∑ i ∈ S, (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  simp only [retainedSmear,Finset.sum_div]
  rw [integral_finsetSum _ (fun i _ =>
    (translated_pole_integrable (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y (x i)).restrict)]
  exact Finset.sum_le_sum (fun i hi => varthetaScaled_local_potential_le hb y (x i) (hxy i hi))

theorem retainedPatchLp_local_potential_le {N : ℕ} {b q R : ℝ} (hb : 0 < b) (hqR : q ≤ R)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hxy : ∀ i ∈ S, x i ≠ y) :
    (∫ z in ball 0 q, ‖retainedPatchLp hb S x y R z‖/‖z‖) ≤
      ∑ i ∈ S, (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  have he := ae_mono (Measure.restrict_mono (ball_subset_ball hqR) le_rfl)
    (retainedPatchLp_ae hb S x y R)
  have hid : (∫ z in ball 0 q, ‖retainedPatchLp hb S x y R z‖/‖z‖) =
      ∫ z in ball 0 q, retainedSmear b S x (y+z)/‖z‖ := by
    apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz,Real.norm_of_nonneg (retainedSmear_nonneg hb S x _)]
  rw [hid]
  have ht := setIntegral_translate_ball y q (fun z => retainedSmear b S x z/‖y-z‖)
  simp only [sub_add_cancel_left,norm_neg] at ht
  rw [ht]
  exact retainedSmear_local_potential_le hb S x y hxy

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegrableCutTower
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_IntegrableCutTower_scope

open MeasureTheory Set Filter
open scoped BigOperators

lemma cutOuter_expectation_eq_full_integrable {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (c : Fin L → Fin 2) (g : Configuration (cutOutNumber c) → ℝ)
    (hi : ∀ s : Spins (cutCoreNumber c+cutOutNumber c), Integrable (fun x =>
      g (outProjection x)*‖(orderedCutForm p hp ψ c).value s x‖^2)) :
    (∑ s : Spins (cutOutNumber c), ∫ u,
      g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      ∑ s : Spins L, ∫ x, g (cutOutPositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 := by
  rw [weighted_coreSlice_eq_full_integrable _ _ hi]
  have he (s : Spins (cutCoreNumber c+cutOutNumber c)) :
      (∫ x, g (outProjection x)*‖(orderedCutForm p hp ψ c).value s x‖^2) =
      ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value
        (s ∘ (cutOrder c).symm) x‖^2 := by
    simpa only [orderedCutForm,reindexForm,cutOutPositions_reindex] using
      integral_reindex (cutOrder c) (fun x => g (cutOutPositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value (s ∘ (cutOrder c).symm) x‖^2)
  simp_rw [he]
  exact sum_spin_reindex (cutOrder c) (fun s : Spins L =>
    ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2)

end Work_IntegrableCutTower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma rawLocalPotential_nonneg {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    0 ≤ rawLocalPotential y q x := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · positivity
  · exact le_rfl

lemma rawLocalPotential_measurable (N : ℕ) (y : Space) (q : ℝ) :
    Measurable (rawLocalPotential (N := N) y q) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (configuration_distance_measurable y i) measurable_const)
    (measurable_const.div (configuration_distance_measurable y i)) measurable_const

lemma rawLocalPotential_weighted_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q x*‖ψ.value s x‖^2) := by
  simp only [rawLocalPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  have hi := (hψ.shifted_nuclear_integrable s i y).indicator
    (measurableSet_lt (configuration_distance_measurable y i) (measurable_const (a := q)))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_core_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) (q : ℝ) :
    Integrable (fun u => rawLocalPotential y q u*formMass (coreSlice ψ s u)) := by
  simp only [rawLocalPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  have hi := (coreSlice_mass_shifted_integrable hψ s i y).indicator
    (measurableSet_lt (configuration_distance_measurable y i) (measurable_const (a := q)))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_out_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins (N+M)) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q (outProjection x)*‖ψ.value s x‖^2) := by
  simp only [rawLocalPotential,Finset.sum_mul,outProjection]
  apply integrable_finsetSum
  intro i _
  have hi := (hψ.shifted_nuclear_integrable s (finSumFinEquiv (Sum.inr i)) y).indicator
    (measurableSet_lt (configuration_distance_measurable y (finSumFinEquiv (Sum.inr i))) (measurable_const (a := q)))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_cutOutPositions_le {N : ℕ} (y : Space) (q : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) :
    rawLocalPotential y q (cutOutPositions c x) ≤ rawLocalPotential y q x := by
  classical
  let e : Fin (cutOutNumber c) → Fin N := fun i => cutOrder c (finSumFinEquiv (Sum.inr i))
  have hinj : Function.Injective e :=
    (cutOrder c).injective.comp (finSumFinEquiv.injective.comp Sum.inr_injective)
  let k : Fin N → ℝ := fun i => if ‖x i-y‖ < q then 1/‖x i-y‖ else 0
  have hn (i : Fin N) : 0 ≤ k i := by dsimp only [k]; split_ifs <;> positivity
  change (∑ i, k (e i)) ≤ ∑ i, k i
  calc
    _ = ∑ i ∈ Finset.univ.image e, k i := (Finset.sum_image (fun i _ j _ h => hinj h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hn i)

lemma rawLocalPotential_cut_weighted_integrable {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (c : Fin N → Fin 2)
    (s : Spins N) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q (cutOutPositions c x)*
      ‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) := by
  have hmp := (hψ.multiply (spatialProduct p hp c)).1 s
  have hmeas : Measurable (cutOutPositions c) := by
    apply Measurable.of_eval
    exact fun _ => measurable_pi_apply _
  apply (rawLocalPotential_weighted_integrable (hψ.multiply (spatialProduct p hp c)) s y q).mono'
    (((rawLocalPotential_measurable _ y q).comp hmeas).aestronglyMeasurable.mul
      (hmp.aestronglyMeasurable.norm.pow 2))
  filter_upwards [] with x
  simp only [Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (rawLocalPotential_nonneg _ _ _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (rawLocalPotential_cutOutPositions_le y q c x) (sq_nonneg _)

theorem fresh_cut_raw_local_control {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (y : Space) (q : ℝ) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      rawLocalPotential y q u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤
      ∫ x, rawLocalPotential y q x ∂formRawLaw ψ := by
  have htw (c : Fin N → Fin 2) := cutOuter_expectation_eq_full_integrable p hp ψ c
    (rawLocalPotential y q)
    (fun s => rawLocalPotential_out_weighted_integrable (orderedCutForm_sobolev p hp hψ c) s y q)
  simp_rw [htw]
  have hb : (∑ c : Fin N → Fin 2, ∑ s : Spins N, ∫ x,
      rawLocalPotential y q (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) ≤
      ∑ c : Fin N → Fin 2, ∑ s : Spins N, ∫ x,
        rawLocalPotential y q x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 := by
    apply Finset.sum_le_sum; intro c _
    apply Finset.sum_le_sum; intro s _
    exact integral_mono (rawLocalPotential_cut_weighted_integrable p hp hψ c s y q)
      (rawLocalPotential_weighted_integrable (hψ.multiply _) s y q)
      (fun x => mul_le_mul_of_nonneg_right (rawLocalPotential_cutOutPositions_le y q c x) (sq_nonneg _))
  apply hb.trans_eq
  rw [Finset.sum_comm,formRawLaw_integral hψ]
  have he (s : Spins N) : (∑ c : Fin N → Fin 2, ∫ x,
      rawLocalPotential y q x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) =
      ∫ x, rawLocalPotential y q x*‖ψ.value s x‖^2 := by
    rw [←integral_finsetSum _ (fun c _ => rawLocalPotential_weighted_integrable (hψ.multiply _) s y q)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [←Finset.mul_sum,finite_partition_value (spatialProduct p hp) (spatial_square_partition p hp)]
  simp_rw [he]
  rw [←integral_finsetSum _ (fun s _ => rawLocalPotential_weighted_integrable hψ s y q)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [←Finset.mul_sum,formRawDensity,mul_comm]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialPatchCap
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAtom
open CoulombAnalysis

theorem radialPatchMinimizer_nonradial_cap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := orderedCutForm p hp ψ c
    ∀ᵐ u, ∀ x : Space, ‖x‖ ≤ 3*(t-4*b)/4 →
      let f := tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField χ s Z lam y (t-4*b) u)
      normalizedCoreField Z lam (coreSlice χ s u) (y+x)-tfBallPotential (t-4*b) f x ≤
        tfPatchCapConstant/(t-4*b)^4 := by
  dsimp only
  filter_upwards [(orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c).ae_coreSlice s] with u hu
  intro x hx
  apply conditionalPatchMinimizer_nonradial_cap _ s u hu (radialPatchCore y t) _ y
    (by linarith) hb hb (radialPatch_nuclear_distance hb hy)
    (radialPatch_core_distance y hb) Z lam x hx
  intro x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

end CoulombAtom

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchCenterObservable
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
attribute [local instance] OAI.CoulombAtom.patchCenterMeasurableSpace
local instance patchCenterBorelSpace (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma tfBallPotential_zero_continuous (R : ℝ) :
    Continuous (fun f : TFLp (ballMeasure R) => tfBallPotential R f 0) := by
  convert patch_test_continuous_of_memLp R (nuclear_memLp R) using 1
  all_goals try with_reducible_and_instances rfl
  funext f
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [zero_sub,norm_neg]
    ring

lemma conditionalPatchCenter_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (conditionalPatchCenter ψ t Z lam y R) :=
  (normalizedCoreField_eval_aemeasurable hψ t Z lam y).sub
    ((tfBallPotential_zero_continuous R).measurable.comp_aemeasurable
      (conditionalPatchMinimizer_aemeasurable hψ t Z lam y R))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_DeletedPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

lemma outerDeletedPotential_nonneg {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    0 ≤ outerDeletedPotential y t b u := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> positivity

lemma outerDeletedPotential_measurable {M : ℕ} (y : Space) (t b : ℝ) :
    Measurable (outerDeletedPotential (M := M) y t b) := by
  apply Finset.measurable_sum; intro i _
  exact (measurable_const.div (configuration_distance_measurable y i)).ite
    (measurableSet_le measurable_const (configuration_distance_measurable y i)) measurable_const

lemma outerDeletedPotential_le_count {M : ℕ} (y : Space) {t b : ℝ} (h : 7*b < t)
    (u : Configuration M) :
    outerDeletedPotential y t b u ≤ outerDeletedCount y t b u/(t-7*b) := by
  rw [outerDeletedCount,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact one_div_le_one_div_of_le (by linarith) hi
  · simp

lemma outerDeletedPotential_le {M : ℕ} (y : Space) {t b : ℝ} (h : 7*b < t) (u : Configuration M) :
    outerDeletedPotential y t b u ≤ M/(t-7*b) :=
  (outerDeletedPotential_le_count y h u).trans
    (div_le_div_of_nonneg_right (outerDeletedCount_le y t b u) (by linarith))

lemma weighted_outerDeletedPotential_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {t b : ℝ} (h : 7*b < t) :
    Integrable (fun u => outerDeletedPotential y t b u*formMass (coreSlice ψ s u)) :=
  (hψ.coreSlice_mass_integrable s).bdd_mul
    (outerDeletedPotential_measurable y t b).aestronglyMeasurable
    (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (outerDeletedPotential_nonneg y t b u)]
      exact outerDeletedPotential_le y h u))

theorem fresh_cut_deleted_potential_bound {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (h : 7*b < t) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      outerDeletedPotential y t b u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u))/(t-7*b) := by
  let I := (c : Fin N → Fin 2) × Spins (cutOutNumber c)
  let w := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    formMass (coreSlice (orderedCutForm p hp ψ i.1) i.2 u)
  let f := fun i : I => fun u : Configuration (cutOutNumber i.1) => outerDeletedCount y t b u
  have hχ (c : Fin N → Fin 2) := orderedCutForm_sobolev p hp hψ c
  have hi (i : I) : Integrable (fun u => f i u*w i u) :=
    ((hχ i.1).coreSlice_mass_integrable i.2).bdd_mul
      (outerDeletedCount_measurable y t b).aestronglyMeasurable
      (ae_of_all _ (fun u => by
        rw [Real.norm_of_nonneg (outerDeletedCount_nonneg y t b u)]
        exact outerDeletedCount_le y t b u))
  have hi2 (i : I) : Integrable (fun u => w i u*(f i u)^2) := by
    have H := ((hχ i.1).coreSlice_mass_integrable i.2).bdd_mul
      ((outerDeletedCount_measurable y t b).pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun u => norm_sq_le_of_nonneg (outerDeletedCount_nonneg y t b u)
        (outerDeletedCount_le y t b u)))
    simpa only [mul_comm] using H
  have hcs := finite_weighted_abs_bound
    (μ := fun i : I => (volume : Measure (Configuration (cutOutNumber i.1))))
    (w := w) (f := f) (fun _ _ => formMass_nonneg _)
    (fun i => (hχ i.1).coreSlice_mass_integrable i.2)
    (fun _ => (outerDeletedCount_measurable y t b).aestronglyMeasurable) hi2
  have hmass : (∑ i : I, ∫ u, w i u) = formMass ψ := by
    rw [Fintype.sum_sigma]
    change (∑ c, ∑ s, ∫ u, formMass (coreSlice (orderedCutForm p hp ψ c) s u)) = _
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ
  have hc (i : I) : (∫ u, outerDeletedPotential y t b u*w i u) ≤
      (∫ u, f i u*w i u)/(t-7*b) := by
    rw [←integral_div]
    apply integral_mono (weighted_outerDeletedPotential_integrable (hχ i.1) i.2 y h)
      ((hi i).div_const _)
    intro u
    have hh := mul_le_mul_of_nonneg_right (outerDeletedPotential_le_count y h u)
      (formMass_nonneg (coreSlice (orderedCutForm p hp ψ i.1) i.2 u))
    simpa only [div_mul_eq_mul_div] using hh
  rw [hmass] at hcs
  have hcauchy : (∑ i : I, ∫ u, f i u*w i u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt (∑ i : I, ∫ u, (f i u)^2*w i u) := by
    simpa only [f,abs_of_nonneg (outerDeletedCount_nonneg y t b _),mul_comm] using hcs
  have hd : (∑ i : I, ∫ u, outerDeletedPotential y t b u*w i u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt (∑ i : I, ∫ u, (f i u)^2*w i u)/(t-7*b) := calc
    _ ≤ (∑ i : I, ∫ u, f i u*w i u)/(t-7*b) := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun i _ => hc i)
    _ ≤ _ := div_le_div_of_nonneg_right hcauchy (by linarith)
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at hd
  simpa only [w,f] using hd

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FreshFieldTower
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma retainedPatchLp_potential {N : ℕ} {b R : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    tfBallPotential R (retainedPatchLp hb S x y R) 0 = tfPotential (retainedSmear b S x) y := by
  rw [←tfPotential_extension]
  have he : tfPotential (tfExtension R (retainedPatchLp hb S x y R)) 0 =
      ∫ z, retainedSmear b S x (y+z)/‖z‖ := by
    apply integral_congr_ae
    filter_upwards [retainedPatchLp_extension hb S x y hmargin] with z hz
    simp only [hz,zero_sub,norm_neg]
  rw [he]
  have ht := integral_add_left_eq_self (μ := volume)
    (fun z => retainedSmear b S x z/‖y-z‖) y
  simpa only [sub_add_cancel_left,norm_neg,tfPotential] using ht

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

lemma rawLocalPotential_indicator {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    rawLocalPotential y q x = ∑ i, (ball y q).indicator (fun z => 1/‖y-z‖) (x i) := by
  classical
  simp only [rawLocalPotential, indicator_apply, mem_ball, dist_eq_norm, norm_sub_rev]

lemma rawPotential_retained_deleted {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    rawPotential y u = rawLocalPotential y (t-7*b) u+outerDeletedPotential y t b u := by
  rw [rawPotential,rawLocalPotential,outerDeletedPotential,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ‖u i-y‖ < t-7*b
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

lemma radial_fine_potential_loss_ae {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
    ∀ᵐ u : Configuration (cutOutNumber c),
      0 ≤ rawLocalPotential y (t-7*b) u-
        tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0 ∧
      rawLocalPotential y (t-7*b) u-
        tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0 ≤
      rawLocalPotential y (Real.sqrt 3*b) u := by
  have he : ∀ᵐ u : Configuration (cutOutNumber c), ∀ i, u i ≠ y :=
    ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ : Fin (cutOutNumber c) => (volume : Measure Space)) i y)
  filter_upwards [he] with u hu
  rw [retainedPatchLp_potential hb _ u y (radialPatch_retained_margin y hb c s u)]
  have hh := retainedSmear_potential_loss hb (radialPatchRetention N y t b c s u) u y (fun i _ => hu i)
  have hret : (∑ i ∈ radialPatchRetention N y t b c s u, 1/‖y-u i‖) = rawLocalPotential y (t-7*b) u := by
    simp only [radialPatchRetention,Finset.sum_filter,rawLocalPotential,norm_sub_rev]
  rw [hret] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [rawLocalPotential_indicator]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => indicator_nonneg (fun z _ => by positivity) _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchTruncationLoss
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchDensityCap_scale {R : ℝ} (hR : 0 < R) :
    (tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) = tfPatchDensityCapConstant/R^6 := by
  have he : tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic) =
      (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))/R^4 := by ring
  rw [he,cap_reaction_scale (div_nonneg tfPatchCapConstant_pos.le (mul_nonneg (by norm_num) tfKinetic_pos.le)) hR]
  rfl

lemma local_coulomb_le_of_density_cap {f : TFSpace → ℝ} {q C : ℝ}
    (hq : 0 < q) (hf : MemLp f (5/3) (ballMeasure q))
    (hcap : ∀ᵐ x ∂ballMeasure q, ‖f x‖ ≤ C) :
    (∫ x in ball 0 q, ‖f x‖/‖x‖) ≤ 2*Real.pi*C*q^2 := by
  have hi : Integrable (fun x => ‖f x‖/‖x‖) (ballMeasure q) := by
    convert! (nuclear_memLp q).integrable_mul hf.norm using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hk : Integrable (fun x : TFSpace => ‖x‖⁻¹) (ballMeasure q) := by
    simpa only [one_div] using (nuclear_memLp q).integrable (Fact.out : (1 : ENNReal) ≤ 5/2)
  have hh : (∫ x, ‖f x‖/‖x‖ ∂ballMeasure q) ≤ ∫ x, C*‖x‖⁻¹ ∂ballMeasure q := by
    apply integral_mono_ae hi (hk.const_mul C)
    filter_upwards [hcap] with x hx
    exact (div_le_div_of_nonneg_right hx (norm_nonneg x)).trans_eq (by ring)
  apply hh.trans_eq
  rw [integral_const_mul]
  change C*(∫ x : TFSpace in ball 0 q, ‖x‖⁻¹) = _
  rw [integral_coulomb_ball hq]
  ring

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

theorem conditionalPatchMinimizer_truncation_loss {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r q : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (Z lam : ℝ) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    |tfBallPotential R f 0-(∫ x, (1/max ‖x‖ q)*f x ∂ballMeasure R)| ≤
      2*Real.pi*tfPatchDensityCapConstant*q^2/R^6 := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  have hqR' : q < R := by linarith
  have hmeasure : ballMeasure q ≤ ballMeasure R :=
    Measure.restrict_mono (ball_subset_ball hqR'.le) le_rfl
  have hcap := conditionalPatchMinimizer_density_cap ψ t u hu A hcore y hR hd hr hnuc hsep Z lam
  have hn := tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  have hn' := ae_mono hmeasure hn
  have hc' := ae_mono hmeasure hcap
  have hb : ∀ᵐ x ∂ballMeasure q, ‖f x‖ ≤ tfPatchDensityCapConstant/R^6 := by
    filter_upwards [hn',hc',ae_restrict_mem measurableSet_ball] with x hx hxcap hxb
    rw [Real.norm_of_nonneg hx]
    have hnorm : ‖x‖ ≤ 3*R/4 := (mem_ball_zero_iff.mp hxb).le.trans hqR
    simpa only [tfPatchDensityCap_scale hR] using hxcap hnorm
  have he := truncated_potential_remainder hq hqR' (Lp.memLp f)
  rw [←tfBallPotential_at_zero] at he
  apply he.trans
  have hh := local_coulomb_le_of_density_cap hq ((Lp.memLp f).mono_measure hmeasure) hb
  exact hh.trans_eq (by ring)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchLocalObservable
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma local_coulomb_pair_eq {R q : ℝ} (hqR : q ≤ R)
    (f : TFLp (ballMeasure R)) (hf : NonnegDensity f) :
    (∫ x, ((ball (0 : Space) q).indicator (fun z => 1/‖z‖) x)*f x ∂ballMeasure R) =
      ∫ x in ball 0 q, ‖f x‖/‖x‖ := by
  have hh : (fun x => ((ball (0 : Space) q).indicator (fun z => 1/‖z‖) x)*f x) =
      (ball (0 : Space) q).indicator (fun x => f x/‖x‖) := by
    funext x
    by_cases hx : x ∈ ball (0 : Space) q
    · simp only [indicator_of_mem hx]; ring
    · simp only [indicator_of_notMem hx,zero_mul]
  rw [hh,integral_indicator measurableSet_ball]
  change (∫ x, f x/‖x‖ ∂(volume.restrict (ball 0 R)).restrict (ball 0 q)) = _
  rw [Measure.restrict_restrict measurableSet_ball,inter_eq_left.mpr (ball_subset_ball hqR)]
  apply integral_congr_ae
  filter_upwards [ae_mono (Measure.restrict_mono (ball_subset_ball hqR) le_rfl) hf] with x hx
  rw [Real.norm_of_nonneg hx]

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
attribute [local instance] OAI.CoulombAtom.instMeasurableSpacePatchLocalObservableTFLp
local instance instBorelSpacePatchLocalObservableTFLp (R : ℝ) :
    BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma retainedPatchLocalPotential_nonneg {M : ℕ} (y : Space) (R q : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Finset (Fin M)) (u : Configuration M) :
    0 ≤ ∫ x in ball 0 q, ‖retainedPatchLp hb S u y R x‖/‖x‖ :=
  integral_nonneg (fun _ => div_nonneg (norm_nonneg _) (norm_nonneg _))

lemma retainedPatchLocalPotential_le {M : ℕ} (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Finset (Fin M)) (u : Configuration M) :
    (∫ x in ball 0 q, ‖retainedPatchLp hb S u y R x‖/‖x‖) ≤
      2*Real.pi*(M*b⁻¹^3)*q^2 := by
  have hmeasure : ballMeasure q ≤ ballMeasure R :=
    Measure.restrict_mono (ball_subset_ball hqR) le_rfl
  apply local_coulomb_le_of_density_cap hq
    ((Lp.memLp (retainedPatchLp hb S u y R)).mono_measure hmeasure)
  filter_upwards [ae_mono hmeasure (retainedPatchLp_nonneg hb S u y R),
    ae_mono hmeasure (retainedPatchLp_bound hb S u y R)] with x hx hxcap
  rw [Real.norm_of_nonneg hx]
  apply hxcap.trans
  have hcNat : S.card ≤ M := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hc : (S.card : ℝ) ≤ M := by exact_mod_cast hcNat
  exact mul_le_mul_of_nonneg_right hc (by positivity)

lemma retainedPatchLocalPotential_measurable {M : ℕ} (y : Space) {R q : ℝ}
    (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    Measurable (fun u => ∫ x in ball 0 q, ‖retainedPatchLp hb (S u) u y R x‖/‖x‖) := by
  have hg := (nuclear_memLp R).indicator measurableSet_ball (s := ball (0 : Space) q)
  have hs := retainedPatchLp_measurable hb S id hS measurable_id y R
  have hm := (patch_test_continuous_of_memLp R hg).measurable.comp hs
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  simpa only [one_div,Function.comp_apply,id_eq] using
    (local_coulomb_pair_eq hqR _ (retainedPatchLp_nonneg hb (S u) u y R)).symm

lemma weightedPatchLocalPotential_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    Integrable (weightedPatchLocalPotential ψ s y R q hb S) := by
  have hm := (retainedPatchLocalPotential_measurable y hqR hb S hS).aestronglyMeasurable (μ := volume)
  have hd : ∀ᵐ u, ‖∫ x in ball 0 q, ‖retainedPatchLp hb (S u) u y R x‖/‖x‖‖ ≤
      2*Real.pi*(M*b⁻¹^3)*q^2 := by
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (retainedPatchLocalPotential_nonneg y R q hb _ u)]
    exact retainedPatchLocalPotential_le y hq hqR hb _ u
  exact ((hψ.coreSlice_mass_integrable s).bdd_mul hm hd).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchFullPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma tfBallPotential_sub_at_zero (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfBallPotential R f 0-tfBallPotential R g 0 =
      ∫ x, (1/‖x‖)*(f-g) x ∂ballMeasure R := by
  rw [tfBallPotential_at_zero,tfBallPotential_at_zero]
  have hf : Integrable (fun x => f x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul (Lp.memLp f) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hg : Integrable (fun x => g x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul (Lp.memLp g) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  rw [←integral_sub hf hg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  simp only [hx,Pi.sub_apply]
  ring

lemma tfBallPotential_truncated_triangle {R q : ℝ} (hq : 0 < q) (hqR : q < R)
    (f g : TFLp (ballMeasure R)) {C : ℝ}
    (hg : |tfBallPotential R g 0-(∫ x, (1/max ‖x‖ q)*g x ∂ballMeasure R)| ≤ C) :
    |tfBallPotential R f 0-tfBallPotential R g 0| ≤
      |∫ x, (1/max ‖x‖ q)*(f-g) x ∂ballMeasure R|+
      (∫ x in ball 0 q, ‖f x‖/‖x‖)+C := by
  let A := ∫ x, (1/max ‖x‖ q)*f x ∂ballMeasure R
  let B := ∫ x, (1/max ‖x‖ q)*g x ∂ballMeasure R
  have hp : (∫ x, (1/max ‖x‖ q)*(f-g) x ∂ballMeasure R) = A-B := by
    dsimp only [A,B]
    have hf : Integrable (fun x => (1/max ‖x‖ q)*f x) (ballMeasure R) :=
      (truncated_kernel_memLp R hq).integrable_mul (Lp.memLp f)
    have hg : Integrable (fun x => (1/max ‖x‖ q)*g x) (ballMeasure R) :=
      (truncated_kernel_memLp R hq).integrable_mul (Lp.memLp g)
    rw [←integral_sub hf hg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with x hx
    simp only [hx,Pi.sub_apply,mul_sub]
  have hf := truncated_potential_remainder hq hqR (Lp.memLp f)
  rw [←tfBallPotential_at_zero] at hf
  rw [hp]
  have he : tfBallPotential R f 0-tfBallPotential R g 0 =
      (A-B)+(tfBallPotential R f 0-A)-(tfBallPotential R g 0-B) := by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans
    (add_le_add (add_le_add le_rfl hf) hg))

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ExpectedFullPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma weightedPatchFull_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ s u) x)
    (y : Space) {R d r q b : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (Z lam : ℝ) :
    ∀ᵐ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u ≤
      weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ q) u+
      weightedPatchLocalPotential ψ s y R q hb S u+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)*formMass (coreSlice ψ s u) := by
  have hqR' : q < R := by linarith
  filter_upwards [hψ.ae_coreSlice s] with u hu
  have he := tfBallPotential_truncated_triangle hq hqR' (retainedPatchLp hb (S u) u y R) _
    (conditionalPatchMinimizer_truncation_loss ψ s u hu A (hcore u) y hR hd hr hnuc hsep hq hqR Z lam)
  rw [tfBallPotential_sub_at_zero] at he
  have hw := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ s u))
  simpa only [weightedPatchTestAbs,weightedPatchLocalPotential,mul_add,mul_comm
    (formMass (coreSlice ψ s u)) (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)] using hw

lemma weightedPatchFull_integrable_and_bound {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ s u) x)
    (y : Space) {R d r q b : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (Z lam : ℝ) (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) ∧
    (∫ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u) ≤
      (∫ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ q) u)+
      (∫ u, weightedPatchLocalPotential ψ s y R q hb S u)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)*(∫ u, formMass (coreSlice ψ s u)) := by
  have hqR' : q < R := by linarith
  have ht := weightedPatchTruncatedAbs_integrable hψ s Z lam y hq hqR' hb S hS hi
  have hl := weightedPatchLocalPotential_integrable hψ s y hq hqR'.le hb S hS
  have hc := (hψ.coreSlice_mass_integrable s).const_mul (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)
  have hbnd := weightedPatchFull_le hψ s A hcore y hR hd hr hnuc hsep hq hqR hb S Z lam
  have hker : MemLp (fun x : TFSpace => 1/‖x‖) (5/2) (ballMeasure R) := by
    simpa only [one_div] using nuclear_memLp R
  have hm : AEStronglyMeasurable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) := by
    have he := (hψ.coreSlice_mass_integrable s).aestronglyMeasurable.mul
      (patchTestError_aestronglyMeasurable hψ s Z lam y R hb S hS hker).norm
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hfull : Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) := by
    apply ((ht.add hl).add hc).mono' hm
    filter_upwards [hbnd] with u hu
    have hn : 0 ≤ weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u :=
      mul_nonneg (formMass_nonneg _) (abs_nonneg _)
    rw [Real.norm_of_nonneg hn]
    exact hu
  refine ⟨hfull,?_⟩
  have hh := integral_mono_ae hfull ((ht.add hl).add hc) hbnd
  have he := integral_add (ht.add hl) hc
  have he' := integral_add ht hl
  simp only [Pi.add_apply] at he he' hh
  rw [he, he', integral_const_mul] at hh
  exact hh

theorem radial_full_absolute_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestAbs (χ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention N y t b c s) u))+
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchLocalPotential (χ c) s y (t-4*b) q hb (radialPatchRetention N y t b c s) u)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ := by
  dsimp only
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hqR' : q < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hc (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c)) (i : Fin (cutCoreNumber c))
      (hi : v i ∉ radialPatchCore y t) : FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hbranch (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    (weightedPatchFull_integrable_and_bound (hχ c) s (radialPatchCore y t) (hc c s) y hR hb hb
      (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) hq hqR hb _
      (radialPatchRetention_measurable N y t b c s) Z lam
      (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)).2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbranch c s))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  have hmass : (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      formMass (coreSlice (χ c) s u)) = formMass ψ := by
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ.sobolevVector
  rw [hmass] at hsum
  exact hsum.trans (add_le_add (add_le_add
    (radial_truncated_absolute_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR') le_rfl) le_rfl)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_FullPotentialComparison
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma retainedPatchLocalPotential_raw_le_ae {M : ℕ} (y : Space) {R q : ℝ}
    (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) :
    ∀ᵐ u, (∫ z in ball 0 q, ‖retainedPatchLp hb (S u) u y R z‖/‖z‖) ≤
      rawLocalPotential y (q+Real.sqrt 3*b) u := by
  classical
  have he : ∀ᵐ u : Configuration M, ∀ i, u i ≠ y := by
    exact (ae_all_iff.mpr fun i => Measure.ae_eval_ne (fun _ : Fin M => (volume : Measure Space)) i y)
  filter_upwards [he] with u hu
  apply (retainedPatchLp_local_potential_le hb hqR (S u) u y (fun i _ => hu i)).trans
  have heq (i : Fin M) : (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (u i) =
      if ‖u i-y‖ < q+Real.sqrt 3*b then 1/‖u i-y‖ else 0 := by
    simp only [indicator_apply,mem_ball,dist_eq_norm,norm_sub_rev]
  simp_rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by
    split_ifs <;> positivity)

lemma weightedPatchLocalPotential_raw_integral_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    (∫ u, weightedPatchLocalPotential ψ s y R q hb S u) ≤
      ∫ u, rawLocalPotential y (q+Real.sqrt 3*b) u*formMass (coreSlice ψ s u) := by
  apply integral_mono_ae (weightedPatchLocalPotential_integrable hψ s y hq hqR hb S hS)
    (rawLocalPotential_core_integrable hψ s y _)
  filter_upwards [retainedPatchLocalPotential_raw_le_ae y hqR hb S] with u hu
  simpa only [weightedPatchLocalPotential,mul_comm (formMass (coreSlice ψ s u))] using
    mul_le_mul_of_nonneg_left hu (formMass_nonneg (coreSlice ψ s u))

theorem radial_full_potential_comparison {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestAbs (χ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention N y t b c s) u))+
      (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ := by
  dsimp only
  have hqR' : q ≤ t-4*b := by linarith
  apply (radial_full_absolute_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR).trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  apply le_trans (Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
      weightedPatchLocalPotential_raw_integral_le
        (orderedCutForm_sobolev _ _ hψ.sobolevVector c) s y hq hqR' hb _
        (radialPatchRetention_measurable N y t b c s))))
  exact fresh_cut_raw_local_control _ _ hψ.sobolevVector y _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchCenterIntegrable
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchMinimizer_potential_zero_le {R T F : ℝ} (hR : 0 < R)
    (hT : 0 < T) (Φ : TFField R) (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    tfBallPotential R (tfPatchMinimizer R T hT Φ) 0 ≤
      2*Real.pi*((max F 0/((5/3:ℝ)*T))^(3/2:ℝ))*R^2 := by
  have hn := tfPatchMinimizer_nonneg R T hT Φ
  have hb := tfPatchMinimizer_ae_bound hT Φ hΦ
  have he := local_coulomb_le_of_density_cap hR (Lp.memLp (tfPatchMinimizer R T hT Φ))
    (hb.and hn |>.mono fun x hx => by simpa only [Real.norm_of_nonneg hx.2] using hx.1)
  apply le_trans _ he
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp only [zero_sub,norm_neg,Real.norm_of_nonneg hx]

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

lemma conditionalPatchCenter_abs_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R b : ℝ} (hR : 0 < R)
    (Z lam : ℝ) (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    ∀ᵐ u, |conditionalPatchCenter ψ t Z lam y R u| ≤
      finiteCorePatchBound N Z lam b +
        2*Real.pi*((finiteCorePatchBound N Z lam b/((5/3:ℝ)*tfKinetic))^(3/2:ℝ))*R^2 := by
  have hy : y ∈ closedBall y R := mem_closedBall_self hR.le
  filter_upwards [hψ.ae_coreSlice t,
    conditionalPatchField_upper hψ t y R Z lam hb A hcore hnuc hsep] with u hu hf
  have h1 := normalizedCoreField_abs_le hu A (hcore u) hb y
    (fun a ha => hsep a ha y hy) hb (hnuc y hy) Z lam
  have h2 := tfPatchMinimizer_potential_zero_le hR tfKinetic_pos _ hf
  rw [max_eq_left (finiteCorePatchBound_nonneg N Z lam hb)] at h2
  have hn := tfBallPotential_nonneg (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u)) 0
  exact (abs_sub _ _).trans (add_le_add h1 (by simpa only [abs_of_nonneg hn] using h2))

lemma weightedPatchCenter_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R b : ℝ} (hR : 0 < R)
    (Z lam : ℝ) (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    Integrable (weightedPatchCenter ψ t Z lam y R) := by
  have hbnd := conditionalPatchCenter_abs_le hψ t y hR Z lam hb A hcore hnuc hsep
  have hm := (conditionalPatchCenter_aemeasurable hψ t Z lam y R).aestronglyMeasurable
  exact ((hψ.coreSlice_mass_integrable t).bdd_mul hm
    (hbnd.mono fun u hu => by simpa only [Real.norm_eq_abs] using hu)).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialCenterRawComparison
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAnalysis

lemma center_raw_error_of_loss {m a p f r d l : ℝ}
    (hm : 0 ≤ m) (hd : 0 ≤ d) (hl : 0 ≤ r-f) (hb : r-f ≤ l) :
    |(a-(r+d))*m-m*(a-p)| ≤ m*|f-p|+l*m+d*m := by
  have he : (a-(r+d))*m-m*(a-p) = -(m*(f-p))-(r-f)*m-d*m := by ring
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) le_rfl).trans
  rw [abs_neg,abs_mul,abs_of_nonneg hm,abs_of_nonneg (mul_nonneg hl hm),
    abs_of_nonneg (mul_nonneg hd hm)]
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hm)) le_rfl

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma radial_branch_center_raw_bound {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (htb : 7*b < t) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    {ψ : FormVector (cutCoreNumber c+cutOutNumber c)} (hψ : SobolevVector ψ) (Z lam : ℝ)
    (hc : Integrable (weightedPatchCenter ψ s Z lam y (t-4*b)))
    (hi : Integrable (weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
      (radialPatchRetention N y t b c s) (fun x => 1/‖x‖))) :
    |(∫ u, (normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
        formMass (coreSlice ψ s u))-(∫ u, weightedPatchCenter ψ s Z lam y (t-4*b) u)| ≤
      (∫ u, weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u)+
      (∫ u, rawLocalPotential y (Real.sqrt 3*b) u*formMass (coreSlice ψ s u))+
      (∫ u, outerDeletedPotential y t b u*formMass (coreSlice ψ s u)) := by
  have hf : Integrable (fun u => (normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
      formMass (coreSlice ψ s u)) := by
    convert (normalizedCoreField_weighted_integrable hψ s Z lam y).sub
      (rawPotential_coreSlice_integrable hψ s y) using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    exact sub_mul _ _ _
  have hl := rawLocalPotential_core_integrable hψ s y (Real.sqrt 3*b)
  have hd := weighted_outerDeletedPotential_integrable hψ s y htb
  have he : ∀ᵐ u, |(normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
      formMass (coreSlice ψ s u)-weightedPatchCenter ψ s Z lam y (t-4*b) u| ≤
      weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u+
      rawLocalPotential y (Real.sqrt 3*b) u*formMass (coreSlice ψ s u)+
      outerDeletedPotential y t b u*formMass (coreSlice ψ s u) := by
    filter_upwards [radial_fine_potential_loss_ae y (t := t) hb c s] with u hu
    simp only [weightedPatchCenter,conditionalPatchCenter,weightedPatchTestAbs,
      ←tfBallPotential_sub_at_zero,rawPotential_retained_deleted y t b u]
    exact center_raw_error_of_loss (formMass_nonneg _) (outerDeletedPotential_nonneg y t b u) hu.1 hu.2
  rw [←integral_sub hf hc]
  apply (abs_integral_le_integral_abs).trans
  have hh := integral_mono_ae (hf.sub hc).abs ((hi.add hl).add hd) he
  simp only [Pi.sub_apply,Pi.add_apply] at hh
  have hi1 := integral_add (hi.add hl) hd
  have hi2 := integral_add hi hl
  simp only [Pi.add_apply] at hi1 hi2
  rw [hi1,hi2] at hh
  exact hh

theorem radial_center_raw_comparison {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchCenter (χ c) s Z lam y (t-4*b) u)| ≤
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchTestAbs (χ c) s Z lam y (t-4*b) hb
          (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u)+
      (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          (outerDeletedCount y t b u)^2*formMass (coreSlice (χ c) s u))/(t-7*b) := by
  dsimp only
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hc (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c)) (i : Fin (cutCoreNumber c))
      (hi : v i ∉ radialPatchCore y t) : FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hbranch (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    radial_branch_center_raw_bound y hb htb c s (hχ c) Z lam
      (weightedPatchCenter_integrable (hχ c) s y hR Z lam hb (radialPatchCore y t) (hc c s)
        (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb))
      (weightedPatchFull_integrable_and_bound (hχ c) s (radialPatchCore y t) (hc c s) y
        hR hb hb (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) hq hqR hb _
        (radialPatchRetention_measurable N y t b c s) Z lam
        (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)).1
  rw [←fresh_cut_field_tower p hp hψ.sobolevVector Z lam y,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    (Finset.abs_sum_le_sum_abs (fun s : Spins (cutOutNumber c) =>
      (∫ u, (normalizedCoreField Z lam (coreSlice (χ c) s u) y-rawPotential y u)*formMass (coreSlice (χ c) s u))-
      (∫ u, weightedPatchCenter (χ c) s Z lam y (t-4*b) u)) Finset.univ).trans
      (Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbranch c s)))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  apply hh.trans
  exact add_le_add
    (add_le_add le_rfl (fresh_cut_raw_local_control p hp hψ.sobolevVector y (Real.sqrt 3*b)))
    (fresh_cut_deleted_potential_bound p hp hψ.sobolevVector y htb)

theorem radial_center_field_quantitative {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchCenter (χ c) s Z lam y (t-4*b) u)| ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention N y t b c s) u))+
      (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ+
      (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          (outerDeletedCount y t b u)^2*formMass (coreSlice (χ c) s u))/(t-7*b) := by
  apply (radial_center_raw_comparison hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR).trans
  exact add_le_add (add_le_add
    (radial_full_potential_comparison hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR)
    le_rfl) le_rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ActualMasterCenterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma graphFormVector_sobolev {N : ℕ} (F : fermionGraph N) :
    SobolevFermion (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_⟩
  · intro s i a
    exact (mem_weakGraph _ _).mp (F.val s).property (i,a)
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s

lemma formMass_graph {N : ℕ} (F : fermionGraph N) :
    formMass (graphFormVector F) = ‖fermionGraphValue N F‖^2 := by
  rw [←formRawDensity_integral (graphFormVector_sobolev F).sobolevVector]
  exact graphRawDensity_integral F

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma sharpFreshFieldConstant_one_le : 1 ≤ sharpFreshFieldConstant := by
  have hC := actualCellMomentConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold sharpFreshFieldConstant
  have h : 0 ≤ thinFieldUniversalConstant*(6+actualCellMomentConstant+
      localizationIMSConstant*actualCellMomentConstant) := by positivity
  linarith only [h]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RotationShellBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology

namespace CoulombAtom

lemma rotation_integral_inverse {f : SpatialRotation → ℝ} (hf : Continuous f) :
    (∫ g, f g⁻¹ ∂rotationMeasure) = ∫ g, f g ∂rotationMeasure := by
  have hi : Integrable (fun q : SpatialRotation × SpatialRotation => f (q.1⁻¹*q.2))
      (rotationMeasure.prod rotationMeasure) :=
    (hf.comp (continuous_fst.inv.mul continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))
  have hx (x : SpatialRotation) : (∫ y, f (x⁻¹*y) ∂rotationMeasure) = ∫ y, f y ∂rotationMeasure :=
    rotation_integral_left f x⁻¹
  have hy (y : SpatialRotation) : (∫ x, f (x⁻¹*y) ∂rotationMeasure) = ∫ x, f x⁻¹ ∂rotationMeasure := by
    rw [←rotation_integral_left (fun x => f (x⁻¹*y)) y]
    simp only [mul_inv_rev,inv_mul_cancel_right]
  calc
    _ = ∫ y, ∫ x, f (x⁻¹*y) ∂rotationMeasure ∂rotationMeasure := by
      simp only [hy,integral_const,probReal_univ,smul_eq_mul,one_mul]
    _ = ∫ x, ∫ y, f (x⁻¹*y) ∂rotationMeasure ∂rotationMeasure := integral_integral_swap hi.swap
    _ = _ := by simp only [hx,integral_const,probReal_univ,smul_eq_mul,one_mul]

lemma rotate_inv_rotate (g : SpatialRotation) (p : Space) :
    rotate g⁻¹ (rotate g p) = p := by
  rw [←rotate_mul,inv_mul_cancel,rotate_one]

lemma rotate_kernel_inverse (g : SpatialRotation) (p z : Space) :
    ‖rotate g p-z‖ = ‖p-rotate g⁻¹ z‖ := by
  rw [←(rotate g⁻¹).norm_map (rotate g p-z),(rotate g⁻¹).map_sub,rotate_inv_rotate]

lemma rotation_kernel_inner (p z : Space) (hz : ‖z‖ < ‖p‖) :
    (∫ g : SpatialRotation, 1/‖rotate g p-z‖ ∂rotationMeasure) = 1/‖p‖ := by
  simp_rw [rotate_kernel_inverse]
  have hc : Continuous (fun g : SpatialRotation => rotate g z) :=
    continuous_subtype_val.clm_apply continuous_const
  have hn (g : SpatialRotation) : ‖p-rotate g z‖ ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp (norm_eq_zero.mp he)
    have hh : ‖p‖ = ‖z‖ := by rw [he',(rotate g).norm_map]
    linarith
  have hfi : Continuous (fun g : SpatialRotation => (1:ℝ)/‖p-rotate g z‖) :=
    continuous_const.div (continuous_const.sub hc).norm hn
  rw [rotation_integral_inverse hfi]
  exact rotation_kernel_newton z p hz

theorem rotation_kernel_shell (p z : Space) (h : ‖z‖ ≠ ‖p‖) :
    (∫ g : SpatialRotation, 1/‖rotate g p-z‖ ∂rotationMeasure) =
      1/max ‖p‖ ‖z‖ := by
  rcases lt_or_gt_of_ne h with hz | hz
  · rw [max_eq_left hz.le]
    exact rotation_kernel_inner p z hz
  · rw [max_eq_right hz.le]
    simp_rw [norm_sub_rev (rotate _ p) z]
    exact rotation_kernel_newton p z hz

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_SphericalMeanFieldBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma rotation_density_kernel_measurable {ρ : Space → ℝ}
    (hm : Measurable ρ) (p : Space) :
    Measurable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖) := by
  have hg : Continuous (fun q : SpatialRotation × Space => rotate q.1 p) :=
    continuous_subtype_val.fst'.clm_apply continuous_const
  exact (hm.comp measurable_snd).div (hg.sub continuous_snd).norm.measurable

lemma density_shell_integrable {ρ : Space → ℝ} (hm : Measurable ρ) (hi : Integrable ρ)
    (hn : ∀ z, 0 ≤ ρ z) {p : Space} (hp : p ≠ 0) :
    Integrable (fun z => ρ z/max ‖p‖ ‖z‖) := by
  apply (hi.div_const ‖p‖).mono' (hm.div (measurable_const.max measurable_norm)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/max ‖p‖ ‖z‖‖ ≤ ρ z/‖p‖
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (le_max_of_le_left (norm_nonneg p)))]
    exact div_le_div_of_nonneg_left (hn z) (norm_pos_iff.mpr hp) (le_max_left _ _)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedSelectedMaster
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma priced_graph_tilt_excess {Z lam e : ℝ} {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) (G : fermionGraph N)
    (hn : ‖fermionGraphValue N G‖^2 = 1)
    (hE : formEnergy Z (graphFormVector G) ≤ energy Z N+e) :
    corePriceExcess Z lam (graphFormVector G) ≤ e := by
  rw [corePriceExcess,formMass_graph,hn,mul_one,mul_one,priceEnergy_eq_of_minimizes hN]
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OrdinaryDensity
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

lemma rawOneParticleLaw_ac {N : ℕ} (ψ : FormVector N) :
    rawOneParticleLaw (formRawLaw ψ) ≪ volume := by
  apply Measure.absolutelyContinuous_sum_left
  intro i
  exact ((withDensity_absolutelyContinuous volume _).map (measurable_pi_apply i)).trans
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => (volume : Measure Space)) i).absolutelyContinuous

lemma ordinaryDensity_nonneg {N : ℕ} (ψ : FormVector N) (z : Space) :
    0 ≤ ordinaryDensity ψ z := ENNReal.toReal_nonneg

lemma ordinaryDensity_measurable {N : ℕ} (ψ : FormVector N) :
    Measurable (ordinaryDensity ψ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma ordinaryDensity_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    Integrable (ordinaryDensity ψ) := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  let : IsFiniteMeasure (rawOneParticleLaw (formRawLaw ψ)) := rawOneParticleLaw_finite _
  exact Measure.integrable_toReal_rnDeriv

lemma ordinaryDensity_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {f : Space → ℝ} (hf : Measurable f)
    (hi : ∀ i : Fin N, Integrable (fun x => f (x i)) (formRawLaw ψ)) :
    (∫ z, ordinaryDensity ψ z*f z) = ∫ x, ∑ i, f (x i) ∂formRawLaw ψ := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  let : IsFiniteMeasure (rawOneParticleLaw (formRawLaw ψ)) := rawOneParticleLaw_finite _
  change (∫ z, ((rawOneParticleLaw (formRawLaw ψ)).rnDeriv volume z).toReal*f z) = _
  rw [integral_toReal_rnDeriv_mul (rawOneParticleLaw_ac ψ)]
  exact rawOneParticleLaw_pairing _ hf hi

lemma ordinaryDensity_mass {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    (∫ z, ordinaryDensity ψ z) = (N:ℝ)*formMass ψ := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  have he := ordinaryDensity_pairing hψ (measurable_const (a := (1:ℝ)))
    (fun _ => integrable_const 1)
  simp only [mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  rw [he,integral_const,smul_eq_mul,measureReal_def,formRawLaw_univ hψ,
    ENNReal.toReal_ofReal (formMass_nonneg ψ)]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalOrdinaryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

lemma sharpFreshKineticConstant_one_le : 1 ≤ sharpFreshKineticConstant := by
  have := localizationIMSConstant_nonneg
  have := actualCellMomentConstant_one_le
  have := sharpFreshFieldConstant_one_le
  have hh : 0 ≤ localizationIMSConstant*actualCellMomentConstant+
      sharpFreshFieldConstant*actualCellMomentConstant := by positivity
  unfold sharpFreshKineticConstant
  linarith only [hh]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpLocalPotentialBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpLocalPotential_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

lemma sharpOrdinaryDensityConstant_nonneg : 0 ≤ sharpOrdinaryDensityConstant := by
  have hc := le_trans zero_le_one actualCellMomentConstant_one_le
  have hk := le_trans zero_le_one sharpFreshKineticConstant_one_le
  unfold sharpOrdinaryDensityConstant
  positivity

end Work_SharpLocalPotential_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpBudgetMonotoneBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma sharpPatchRemainder_mono {a b m n : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hmn : m ≤ n) : sharpPatchRemainder a b m ≤ sharpPatchRemainder a b n := by
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hF : 0 ≤ sharpFreshFieldConstant := le_trans zero_le_one sharpFreshFieldConstant_one_le
  have hn : 0 ≤ n := hm.trans hmn
  unfold sharpPatchRemainder
  gcongr

lemma sharpLocalPotentialBudget_mono {a m n u v : ℝ} (ha : 0 < a)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hu : 0 ≤ u) (huv : u ≤ v) :
    sharpLocalPotentialBudget a m u ≤ sharpLocalPotentialBudget a n v := by
  have hC : 0 ≤ sharpOrdinaryDensityConstant := sharpOrdinaryDensityConstant_nonneg
  unfold sharpLocalPotentialBudget
  gcongr

lemma sharpPotentialRemainder_mono {a b m n D E q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hDE : D ≤ E) (hq : 0 < q) :
    sharpPotentialRemainder a b m D q ≤ sharpPotentialRemainder a b n E q := by
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  unfold sharpPotentialRemainder
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · apply add_le_add
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (add_le_add hDE (sharpPatchRemainder_mono ha hb hm hmn)) (by positivity))
        · exact sharpLocalPotentialBudget_mono ha hm hmn (by positivity) le_rfl
      · exact le_rfl
    · exact sharpLocalPotentialBudget_mono ha hm hmn (by positivity) le_rfl
  · gcongr

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpectedRadialCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ExpectedRadialCap_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis

theorem expectedRadialPatchCenter_le {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) :
    expectedRadialPatchCenter ψ y ht hb Z lam ≤
      (tfPatchCapConstant/(t-4*b)^4)*formMass ψ := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ c
  have hcore (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c))
      (i : Fin (cutCoreNumber c)) (hi : v i ∉ radialPatchCore y t) :
      FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hi (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    weightedPatchCenter_integrable (hχ c) s y hR Z lam hb (radialPatchCore y t)
      (hcore c s) (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb)
  have hbnd (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
      (∫ u, weightedPatchCenter (χ c) s Z lam y (t-4*b) u) ≤
        (tfPatchCapConstant/(t-4*b)^4)*(∫ u, formMass (coreSlice (χ c) s u)) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (hi c s) ((hχ c).coreSlice_mass_integrable s |>.const_mul _)
    filter_upwards [radialPatchMinimizer_nonradial_cap hψ y ht hb hbt hy Z lam c s] with u hu
    have h := hu 0 (by simpa only [norm_zero] using (by positivity : 0 ≤ 3*(t-4*b)/4))
    simp only [add_zero] at h
    have hh := mul_le_mul_of_nonneg_left h (formMass_nonneg (coreSlice (χ c) s u))
    simpa only [weightedPatchCenter,conditionalPatchCenter,mul_comm,χ,p,hp] using hh
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbnd c s))
  simp_rw [←Finset.mul_sum,(hχ _).integral_coreSlice_mass] at hh
  rw [orderedCutForm_mass_sum p hp hψ] at hh
  exact hh

end Work_ExpectedRadialCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

lemma scaled_mass_four_thirds {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    (M/a^3)^(4/3:ℝ) = M^(4/3:ℝ)/a^4 := by
  rw [Real.div_rpow hM (by positivity),←Real.rpow_natCast,←Real.rpow_mul ha.le]
  norm_num

lemma sharpPatchRemainder_rescale {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M) :
    a^7*sharpPatchRemainder a (a*β) (M/a^3) = dimensionlessPatchRemainder a β M := by
  have hs : 8*(a*β)/a = 8*β := by field_simp
  unfold sharpPatchRemainder dimensionlessPatchRemainder
  rw [hs,scaled_mass_four_thirds ha hM]
  field_simp
  ring

lemma sharpLocalPotentialBudget_rescale {a M u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    a^4*sharpLocalPotentialBudget a (M/a^3) (a*u) = dimensionlessLocalPotential M u := by
  have hC := sharpOrdinaryDensityConstant_nonneg
  have he : sharpOrdinaryDensityConstant*(M/a^3)^2/a =
      sharpOrdinaryDensityConstant*M^2/a^7 := by field_simp
  have hp : (a^7)^(3/5:ℝ) = a^(21/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ha.le]; norm_num
  have hprod : a^4*a^(1/5:ℝ) = a^(21/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  unfold sharpLocalPotentialBudget dimensionlessLocalPotential
  rw [he,Real.div_rpow (mul_nonneg hC (sq_nonneg M)) (by positivity),hp,
    Real.mul_rpow ha.le hu]
  have hne : a^(21/5:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  calc _ = (a^4*a^(1/5:ℝ)/a^(21/5:ℝ))*
        ((sharpOrdinaryDensityConstant*M^2)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*u^(1/5:ℝ)) := by ring
       _ = _ := by rw [hprod,div_self hne,one_mul]

lemma sharpPotentialRemainder_rescale {a β M E τ : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M) (hτ : 0 < τ) :
    a^4*sharpPotentialRemainder a (a*β) (M/a^3) (E/a^7) (a*τ) =
      dimensionlessPotentialRemainder a β M E τ := by
  have hR := sharpPatchRemainder_rescale ha hβ hM
  have hroot : a^4*Real.sqrt ((2/(a*τ))*(E/a^7+sharpPatchRemainder a (a*β) (M/a^3))) =
      Real.sqrt ((2/τ)*(E+dimensionlessPatchRemainder a β M)) := by
    rw [←Real.sqrt_sq (by positivity : 0 ≤ a^4),←Real.sqrt_mul (sq_nonneg (a^4))]
    congr 1
    rw [←hR]
    field_simp
  have hpot1 := sharpLocalPotentialBudget_rescale (M := M) ha
    (by positivity : 0 ≤ τ+Real.sqrt 3*β)
  have hpot2 := sharpLocalPotentialBudget_rescale (M := M) ha
    (by positivity : 0 ≤ Real.sqrt 3*β)
  have he1 : a*τ+Real.sqrt 3*(a*β) = a*(τ+Real.sqrt 3*β) := by ring
  have he2 : Real.sqrt 3*(a*β) = a*(Real.sqrt 3*β) := by ring
  have he3 : 8*(a*β)/a = 8*β := by field_simp
  unfold sharpPotentialRemainder dimensionlessPotentialRemainder
  rw [mul_add,mul_add,mul_add,mul_add]
  rw [hroot,he1,he2,hpot1,hpot2,he3]
  field_simp

lemma localOffsetMass_rescale {D : ℝ} {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) :
    (localCellRadius y)^3*localOffsetMass D y = 1+Real.sqrt (D*(localCellRadius y)^7) := by
  have ha := localCellRadius_pos hy
  have hh : (localCellRadius y)^3 ≤ 1 := pow_le_one₀ ha.le ha1
  have hmax : max (1/(localCellRadius y)^3) 1 = 1/(localCellRadius y)^3 :=
    max_eq_left ((le_div_iff₀ (by positivity : 0 < (localCellRadius y)^3)).mpr (by simpa using hh))
  unfold localOffsetMass
  rw [hmax,mul_add,mul_one_div_cancel (pow_ne_zero _ ha.ne'),←Real.sqrt_sq (by positivity : 0 ≤ (localCellRadius y)^3),
    ←Real.sqrt_mul (sq_nonneg ((localCellRadius y)^3))]
  congr 2
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpErrorLimitBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

lemma patch_power_ratio {a : ℝ} (ha : 0 < a) (p w : ℝ) :
    (a^p/(a^(1/5:ℝ))^2)/a^w = a^(p-2/5-w) := by
  rw [←Real.rpow_mul_natCast ha.le,←Real.rpow_sub ha,←Real.rpow_sub ha]
  norm_num

lemma patch_sqrt_ratio {a : ℝ} (ha : 0 < a) (w : ℝ) :
    Real.sqrt (8*a^(1/5:ℝ))/a^w = Real.sqrt 8*a^(1/10-w) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8),Real.sqrt_eq_rpow (a^(1/5:ℝ)),
    ←Real.rpow_mul ha.le]
  norm_num
  rw [mul_div_assoc,←Real.rpow_sub ha]

lemma dimensionlessPatchRemainder_weight {a : ℝ} (ha : 0 < a) (M w : ℝ) :
    dimensionlessPatchRemainder a (a^(1/5:ℝ)) M/a^w = weightedDimensionlessPatch a M w := by
  have h2 : (a^2/(a^(1/5:ℝ))^2)/a^w = a^(8/5-w) := by
    convert patch_power_ratio ha 2 w using 1 <;> norm_num
  have h1 : (a/(a^(1/5:ℝ))^2)/a^w = a^(3/5-w) := by
    convert patch_power_ratio ha 1 w using 1 <;> norm_num
  have h3 : (a^3/a^(1/5:ℝ))/a^w = a^(14/5-w) := by
    rw [←Real.rpow_natCast,←Real.rpow_sub ha,←Real.rpow_sub ha]
    norm_num
  have hr := patch_sqrt_ratio ha w
  unfold dimensionlessPatchRemainder weightedDimensionlessPatch
  rw [←h2,←h1,←h3,←hr]
  ring

theorem dimensionlessPatchRemainder_div_tendsto {ι : Type*} {l : Filter ι}
    {a M : ι → ℝ} {M₀ w : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hM : Tendsto M l (𝓝 M₀)) (hw : w < 1/10) :
    Tendsto (fun i => dimensionlessPatchRemainder (a i) ((a i)^(1/5:ℝ)) (M i)/(a i)^w)
      l (𝓝 0) := by
  have hpow (p : ℝ) (hp : 0 < p) := ha0.rpow_const_nhds_zero hp
  have hs : Tendsto (fun i => Real.sqrt (8*(a i)^(1/5:ℝ))) l (𝓝 0) := by
    simpa using ((hpow (1/5) (by norm_num)).const_mul 8).sqrt
  have h1 := ((hpow (8/5-w) (by linarith)).mul_const localizationIMSConstant).mul
    ((hs.mul_const actualCellMomentConstant).mul hM)
  have h2 := (((hpow (3/5-w) (by linarith)).mul_const neumannRemainderConstant).mul_const
    ((actualCellMomentConstant)^(2/3:ℝ))).mul (hM.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 4/3)))
  have h3 := (((hpow (8/5-w) (by linarith)).mul_const neumannRemainderConstant).mul_const
    actualCellMomentConstant).mul hM
  have h4 := (((hpow (14/5-w) (by linarith)).mul_const ((2*Real.pi+1)/2)).mul_const
    actualCellMomentConstant).mul hM
  have h5 := ((((hpow (1/10-w) (by linarith)).const_mul (Real.sqrt 8)).const_mul
    sharpFreshFieldConstant).mul_const actualCellMomentConstant).mul (hM.pow 2)
  have h6 := ((((hpow (8/5-w) (by linarith)).mul_const (packetDirichlet canonicalRealPacket/2)).mul_const
    768).mul_const sharpFreshFieldConstant).mul hM
  have hh : Tendsto (fun i => weightedDimensionlessPatch (a i) (M i) w) l (𝓝 0) := by
    simpa only [weightedDimensionlessPatch,zero_mul,mul_zero,add_zero] using
      ((((h1.add h2).add h3).add h4).add h5).add h6
  apply hh.congr'
  filter_upwards [ha] with i hi
  exact (dimensionlessPatchRemainder_weight hi (M i) w).symm

lemma dimensionlessLocalPotential_tendsto {ι : Type*} {l : Filter ι}
    {M u : ι → ℝ} {M₀ : ℝ} (hM : Tendsto M l (𝓝 M₀)) (hu : Tendsto u l (𝓝 0)) :
    Tendsto (fun i => dimensionlessLocalPotential (M i) (u i)) l (𝓝 0) := by
  have h1 := ((hM.pow 2).const_mul sharpOrdinaryDensityConstant).rpow_const
    (Or.inr (by norm_num : (0:ℝ) ≤ 3/5))
  have h2 := hu.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  simpa only [dimensionlessLocalPotential,mul_zero] using
    (h1.mul_const ((8*Real.pi)^(2/5:ℝ))).mul h2

theorem dimensionlessPotentialRemainder_tendsto {ι : Type*} {l : Filter ι}
    {a M E : ι → ℝ} {M₀ w : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hM : Tendsto M l (𝓝 M₀)) (hw : 0 < w) (hw' : w < 1/10)
    (hE : Tendsto (fun i => E i/(a i)^w) l (𝓝 0)) :
    Tendsto (fun i => dimensionlessPotentialRemainder (a i) ((a i)^(1/5:ℝ)) (M i) (E i) ((a i)^w))
      l (𝓝 0) := by
  have hR := dimensionlessPatchRemainder_div_tendsto ha ha0 hM hw'
  have hτ := ha0.rpow_const_nhds_zero hw
  have hβ := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  have hroot : Tendsto (fun i => Real.sqrt ((2/(a i)^w)*
      (E i+dimensionlessPatchRemainder (a i) ((a i)^(1/5:ℝ)) (M i)))) l (𝓝 0) := by
    have ht := ((hE.add hR).const_mul 2).sqrt
    convert ht using 1
    · funext i
      congr 1
      ring
    · simp
  have hu1 : Tendsto (fun i => (a i)^w+Real.sqrt 3*(a i)^(1/5:ℝ)) l (𝓝 0) := by
    simpa using hτ.add (hβ.const_mul (Real.sqrt 3))
  have hu2 : Tendsto (fun i => Real.sqrt 3*(a i)^(1/5:ℝ)) l (𝓝 0) := by
    simpa using hβ.const_mul (Real.sqrt 3)
  have hcap := (hτ.pow 2).const_mul (2*Real.pi*tfPatchDensityCapConstant)
  have hdel := (((hβ.const_mul 8).sqrt).mul_const actualCellMomentConstant).mul hM
  simpa only [dimensionlessPotentialRemainder,zero_mul,mul_zero,zero_pow (by decide : 2 ≠ 0),
    Real.sqrt_zero,add_zero] using
    (((hroot.add (dimensionlessLocalPotential_tendsto hM hu1)).add hcap).add
      (dimensionlessLocalPotential_tendsto hM hu2)).add hdel

end Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma microscopicWidth_eq {a : ℝ} (ha : 0 < a) :
    a*a^(1/5:ℝ) = a^(6/5:ℝ) := by
  calc _ = a^(1:ℝ)*a^(1/5:ℝ) := by rw [Real.rpow_one]
       _ = _ := by rw [←Real.rpow_add ha]; norm_num

lemma microscopic_collar {a m : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hm : 1/a^3 ≤ m) : a ≤ (a*a^(1/5:ℝ))^2*m := by
  have hβ : a ≤ a^(1/5:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (1/5:ℝ) ≤ 1)
  have hb : a^2 ≤ a*a^(1/5:ℝ) := by nlinarith
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  have hsq : a^4 ≤ (a*a^(1/5:ℝ))^2 := by nlinarith [sq_nonneg (a*a^(1/5:ℝ)-a^2)]
  calc a = a^4*(1/a^3) := by field_simp
       _ ≤ a^4*m := mul_le_mul_of_nonneg_left hm (by positivity)
       _ ≤ (a*a^(1/5:ℝ))^2*m := mul_le_mul_of_nonneg_right hsq hm0

lemma normalized_excess_ratio {a D w : ℝ} (ha : 0 < a) :
    (D*a^7)/a^w = D*a^(7-w) := by
  rw [mul_div_assoc,←Real.rpow_natCast,←Real.rpow_sub ha]
  norm_num

theorem physical_local_mass_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^3*localOffsetMass (D i) (y i)) l (𝓝 1) := by
  let a := fun i => localCellRadius (y i)
  have hp : Tendsto (fun i => (a i)^w) l (𝓝 0) := hy0.rpow_const_nhds_zero hw
  have hE : Tendsto (fun i => D i*(a i)^7) l (𝓝 0) := by
    have ht := hD.mul hp
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hy] with i hi
    have ha := localCellRadius_pos hi
    change D i*(a i)^(7-w)*(a i)^w = D i*(a i)^7
    rw [mul_assoc,←Real.rpow_add ha]
    norm_num [a]
  have ht : Tendsto (fun i => 1+Real.sqrt (D i*(a i)^7)) l (𝓝 1) := by
    simpa using hE.sqrt.const_add 1
  apply ht.congr'
  filter_upwards [hy,hy0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi ha1
  exact (localOffsetMass_rescale hi ha1.le).symm

theorem physical_potential_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w) (hw' : w < 1/10)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*
      sharpPotentialRemainder (localCellRadius (y i))
        ((localCellRadius (y i))^(6/5:ℝ)) (localOffsetMass (D i) (y i)) (D i)
        ((localCellRadius (y i))*(localCellRadius (y i))^w)) l (𝓝 0) := by
  let a := fun i => localCellRadius (y i)
  let M := fun i => (a i)^3*localOffsetMass (D i) (y i)
  let E := fun i => D i*(a i)^7
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono (fun i hi => localCellRadius_pos hi)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have hE : Tendsto (fun i => E i/(a i)^w) l (𝓝 0) := by
    apply hD.congr'
    filter_upwards [ha] with i hi
    exact (normalized_excess_ratio hi).symm
  have ht := dimensionlessPotentialRemainder_tendsto ha hy0 hM hw hw' hE
  apply ht.congr'
  filter_upwards [ha] with i hi
  have hMi : 0 ≤ M i := mul_nonneg (pow_nonneg hi.le _) (le_trans zero_le_one (localOffsetMass_one_le _ _))
  have he := sharpPotentialRemainder_rescale (E := E i) hi (Real.rpow_pos_of_pos hi (1/5:ℝ)) hMi (Real.rpow_pos_of_pos hi w)
  have hmass : M i/(a i)^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  have henergy : E i/(a i)^7 = D i := by dsimp [E]; field_simp
  rw [hmass,henergy,microscopicWidth_eq hi] at he
  exact he.symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpOrdinaryCapBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpOrdinaryCap_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis
attribute [local irreducible] corePriceExcess

lemma ordinaryDensity_raw_potential {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) :
    tfPotential (ordinaryDensity ψ) y = ∫ x, rawPotential y x ∂formRawLaw ψ := by
  have hkernel : Measurable (fun z : Space => (1:ℝ)/‖y-z‖) := by fun_prop
  have hi (i : Fin N) : Integrable (fun x : Configuration N => (1:ℝ)/‖y-x i‖)
      (formRawLaw ψ) := by
    apply (rawPotential_form_integrable hψ y).mono'
      (hkernel.comp (measurable_pi_apply i)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖(1:ℝ)/‖y-x i‖‖ ≤ rawPotential y x
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [rawPotential,norm_sub_rev (x _) y]
    change (1:ℝ)/‖y-x i‖ ≤ ∑ j, (1:ℝ)/‖y-x j‖
    exact Finset.single_le_sum (f := fun j : Fin N => (1:ℝ)/‖y-x j‖)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hh := ordinaryDensity_pairing hψ hkernel hi
  simpa only [tfPotential,mul_one_div,rawPotential,norm_sub_rev y] using hh

theorem sharp_unconditional_field_cap {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*
      localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    Z/‖y‖-lam-tfPotential (ordinaryDensity ψ) y ≤
      tfPatchCapConstant/(localCellRadius y)^4+
      sharpPotentialRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)
        (max (corePriceExcess Z lam ψ) 0) q := by
  obtain ⟨t,ht,ht0,_,hpot⟩ := sharp_joint_selected_patch hψ hy ha1 hb hba hZ hlam hq hqr hcollar
  have ha := localCellRadius_pos hy
  have hnorm : t ≤ ‖y‖ := by
    have := ht.2
    unfold localCellRadius at this
    nlinarith [norm_nonneg y]
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  have hraw := radial_center_field_quantitative hψ.sobolevFermion y ht0 hb
    (by linarith [ht.1]) hnorm hZ hlam canonicalRealPacket_smooth canonicalRealPacket_compact
    canonicalRealPacket_normalized canonicalRealPacket_radial canonicalRealPacket_support hq
    (by linarith [ht.1] : q ≤ 3*(t-4*b)/4)
  change |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
    expectedRadialPatchCenter ψ y ht0 hb Z lam| ≤ radialPotentialError ψ y ht0 hb Z lam q at hraw
  rw [hm,mul_one,←ordinaryDensity_raw_potential hψ.sobolevFermion.sobolevVector y] at hraw
  have hcap := expectedRadialPatchCenter_le hψ.sobolevFermion.sobolevVector y ht0 hb
    (by linarith [ht.1]) hnorm Z lam
  rw [hm,mul_one] at hcap
  have hpow : (localCellRadius y)^4 ≤ (t-4*b)^4 :=
    pow_le_pow_left₀ ha.le (by linarith [ht.1]) 4
  have hd := div_le_div_of_nonneg_left tfPatchCapConstant_pos.le
    (by positivity : 0 < (localCellRadius y)^4) hpow
  linarith [(le_abs_self _).trans (hraw.trans hpot),hcap.trans hd]

end CoulombAtom

end Work_SharpOrdinaryCap_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma ae_off_norm_sphere (p : Space) : ∀ᵐ z : Space, ‖z‖ ≠ ‖p‖ := by
  apply ae_iff.mpr
  have he : {a : Space | ¬ ‖a‖ ≠ ‖p‖} = sphere (0:Space) ‖p‖ := by
    ext a
    simp only [mem_ofPred_eq,not_not,mem_sphere,dist_zero_right]
  rw [he]
  exact Measure.addHaar_sphere volume (0:Space) ‖p‖

lemma rotation_kernel_integrable_off_sphere (p z : Space) (hp : p ≠ 0)
    (hz : ‖z‖ ≠ ‖p‖) :
    Integrable (fun g : SpatialRotation => (1:ℝ)/‖rotate g p-z‖) rotationMeasure := by
  by_contra hn
  have he := rotation_kernel_shell p z hz
  rw [integral_undef hn] at he
  have hm : 0 < max ‖p‖ ‖z‖ := (norm_pos_iff.mpr hp).trans_le (le_max_left _ _)
  exact (ne_of_gt (one_div_pos.mpr hm)) he.symm

lemma L1_rotation_density_kernel_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    Integrable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖)
      (rotationMeasure.prod volume) := by
  have hme : AEStronglyMeasurable
      (fun q : Space × SpatialRotation => ρ q.1/‖rotate q.2 p-q.1‖)
      (volume.prod rotationMeasure) :=
    ((rotation_density_kernel_measurable hm p).comp measurable_swap).aestronglyMeasurable
  have hh : Integrable (fun q : Space × SpatialRotation => ρ q.1/‖rotate q.2 p-q.1‖)
      (volume.prod rotationMeasure) := by
    apply (integrable_prod_iff hme).mpr
    constructor
    · filter_upwards [ae_off_norm_sphere p] with z hz
      simpa only [mul_one_div] using (rotation_kernel_integrable_off_sphere p z hp hz).const_mul (ρ z)
    · apply (density_shell_integrable hm hi hn hp).congr
      filter_upwards [ae_off_norm_sphere p] with z hz
      change ρ z/max ‖p‖ ‖z‖ = ∫ g : SpatialRotation, ‖ρ z/‖rotate g p-z‖‖ ∂rotationMeasure
      simp_rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
      simp_rw [show ∀ g : SpatialRotation, ρ z/‖rotate g p-z‖ =
        ρ z*((1:ℝ)/‖rotate g p-z‖) by intro g; ring]
      rw [integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]
  exact hh.swap

lemma L1_potential_rotation_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    Integrable (fun g : SpatialRotation => tfPotential ρ (rotate g p)) rotationMeasure :=
  (L1_rotation_density_kernel_integrable hm hi hn hp).integral_prod_left

theorem L1_sphereMean_potential {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    sphereMean (tfPotential ρ) p = ∫ z, ρ z/max ‖p‖ ‖z‖ := by
  calc
    _ = ∫ g : SpatialRotation, ∫ z : Space, ρ z/‖rotate g p-z‖ ∂volume ∂rotationMeasure := rfl
    _ = ∫ z : Space, ∫ g : SpatialRotation, ρ z/‖rotate g p-z‖ ∂rotationMeasure :=
      integral_integral_swap (L1_rotation_density_kernel_integrable hm hi hn hp)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_off_norm_sphere p] with z hz
      rw [show (fun g : SpatialRotation => ρ z/‖rotate g p-z‖) =
        fun g => ρ z*(1/‖rotate g p-z‖) by funext g; ring,
        integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]

lemma L1_residualCharge_le_sphereMean {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    (Z : ℝ) {p : Space} (hp : p ≠ 0) :
    (Z-∫ z, ρ z)/‖p‖ ≤ sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p := by
  have hsh := density_shell_integrable hm hi hn hp
  have hf : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p =
      Z/‖p‖-sphereMean (tfPotential ρ) p := by
    unfold sphereMean
    simp only [(rotate _).norm_map]
    rw [integral_sub (integrable_const _) (L1_potential_rotation_integrable hm hi hn hp)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rw [hf,L1_sphereMean_potential hm hi hn hp,sub_div]
  apply sub_le_sub_left
  rw [←integral_div]
  apply integral_mono hsh (hi.div_const ‖p‖)
  intro z
  exact div_le_div_of_nonneg_left (hn z) (norm_pos_iff.mpr hp) (le_max_left _ _)

theorem L1_residualCharge_of_field_cap {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    (Z : ℝ) {p : Space} (hp : p ≠ 0) {B : ℝ}
    (hcap : ∀ g : SpatialRotation, Z/‖rotate g p‖-tfPotential ρ (rotate g p) ≤ B) :
    Z-∫ z, ρ z ≤ ‖p‖*B := by
  have hh := L1_residualCharge_le_sphereMean hm hi hn Z hp
  have hb : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p ≤ B := by
    have hin : Integrable (fun g : SpatialRotation => Z/‖rotate g p‖-tfPotential ρ (rotate g p)) rotationMeasure := by
      simp only [(rotate _).norm_map]
      exact (integrable_const _).sub (L1_potential_rotation_integrable hm hi hn hp)
    have hv := integral_mono hin (integrable_const B) hcap
    simpa only [sphereMean,integral_const,probReal_univ,smul_eq_mul,one_mul] using hv
  have h := (div_le_iff₀ (norm_pos_iff.mpr hp)).mp (hh.trans hb)
  simpa only [mul_comm] using h

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ActualUpperDeficitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ActualUpperDeficit_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma localCellRadius_rotate (g : SpatialRotation) (y : Space) :
    localCellRadius (rotate g y) = localCellRadius y := by
  simp only [localCellRadius,(rotate _).norm_map]

lemma localOffsetMass_rotate (g : SpatialRotation) (D : ℝ) (y : Space) :
    localOffsetMass D (rotate g y) = localOffsetMass D y := by
  simp only [localOffsetMass,localCellRadius_rotate]

theorem actual_upper_deficit {Z lam D : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) (hD : 0 < D)
    {p : Space} (hp : p ≠ 0) (ha1 : localCellRadius p ≤ 1)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius p)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius p)
    (hqR : q ≤ 3*(5*localCellRadius p-4*b)/4)
    (hcollar : localCellRadius p ≤ b^2*(1/(localCellRadius p)^3)) :
    Z-(N:ℝ) ≤ ‖p‖*(lam+tfPatchCapConstant/(localCellRadius p)^4+
      sharpPotentialRemainder (localCellRadius p) b (localOffsetMass D p) D q) := by
  obtain ⟨F,hFn,hFE⟩ := quantum_sector_near_minimizer Z N hD
  have hψ := graphFormVector_admissible F hFn
  have hsf := hψ.sobolevFermion.sobolevVector
  have hDE : max (corePriceExcess Z lam (graphFormVector F)) 0 ≤ D :=
    max_le (priced_graph_tilt_excess hN F hFn hFE.le) hD.le
  have hcap (g : SpatialRotation) : Z/‖rotate g p‖-
      tfPotential (ordinaryDensity (graphFormVector F)) (rotate g p) ≤
      lam+tfPatchCapConstant/(localCellRadius p)^4+
        sharpPotentialRemainder (localCellRadius p) b (localOffsetMass D p) D q := by
    have hgp : rotate g p ≠ 0 := by
      intro he
      have hnorm := (rotate g).norm_map p
      rw [he,norm_zero] at hnorm
      exact hp (norm_eq_zero.mp hnorm.symm)
    have hcollar' : localCellRadius (rotate g p) ≤ b^2*
        localOffsetMass (max (corePriceExcess Z lam (graphFormVector F)) 0) (rotate g p) := by
      rw [localOffsetMass,localCellRadius_rotate]
      apply hcollar.trans
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
      linarith [le_max_left (1/(localCellRadius p)^3) 1,
        Real.sqrt_nonneg (max (corePriceExcess Z lam (graphFormVector F)) 0*localCellRadius p)]
    have hbound := sharp_unconditional_field_cap hψ hZ hlam hgp
      (by simpa only [localCellRadius_rotate] using ha1) hb
      (by simpa only [localCellRadius_rotate] using hba) hq
      (by simpa only [localCellRadius_rotate] using hqr)
      (by simpa only [localCellRadius_rotate] using hqR) hcollar'
    simp only [localCellRadius_rotate,localOffsetMass_rotate] at hbound
    have he := sharpPotentialRemainder_mono (localCellRadius_pos hp) hb
      (le_trans zero_le_one (localOffsetMass_one_le _ p))
      (localOffsetMass_mono hDE p) hDE hq
    linarith [hbound.trans (add_le_add le_rfl he)]
  have hbound := L1_residualCharge_of_field_cap
    (ordinaryDensity_measurable (graphFormVector F)) (ordinaryDensity_integrable hsf)
    (ordinaryDensity_nonneg (graphFormVector F)) Z hp hcap
  have hm : formMass (graphFormVector F) = 1 := hψ.2.2.2.2.1
  rwa [ordinaryDensity_mass hsf,hm,mul_one] at hbound

end Work_ActualUpperDeficit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma pointOnFirstAxis_norm {s : ℝ} (hs : 0 ≤ s) :
    ‖s • spaceDirections 0‖ = s := by
  simp [norm_smul,spaceDirections,Real.norm_of_nonneg hs]

lemma upperDeficit_rescale {s C R : ℝ} (hs : 0 < s) :
    s^3*(s*((s^4)⁻¹+C/(s/100000)^4+R)) =
      1+(100000:ℝ)^4*(C+(s/100000)^4*R) := by
  field_simp [hs.ne']
  ring

theorem actual_uniform_upper_deficit_oai {ι : Type*} {l : Filter ι} {s : ι → ℝ}
    (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0)) :
    ∀ᶠ i in l, ∀ Z : ℝ, 0 ≤ Z → ∀ N : ℕ,
      PriceMinimizes (energy Z) ((s i)^4)⁻¹ N →
      (s i)^3*(Z-(N:ℝ)) ≤ quantumUpperDeficitConstant := by
  let p : ι → Space := fun i => s i • spaceDirections 0
  let a : ι → ℝ := fun i => localCellRadius (p i)
  have hpn : ∀ᶠ i in l, ‖p i‖ = s i := hs.mono (fun i hi => pointOnFirstAxis_norm hi.le)
  have hp : ∀ᶠ i in l, p i ≠ 0 := by
    filter_upwards [hs,hpn] with i hi hn
    apply norm_ne_zero_iff.mp
    rw [hn]
    exact hi.ne'
  have haeq : ∀ᶠ i in l, a i = s i/100000 := by
    filter_upwards [hpn] with i hi
    simp only [a,localCellRadius,hi]
  have ha : ∀ᶠ i in l, 0 < a i := hp.mono (fun i hi => localCellRadius_pos hi)
  have ha0 : Tendsto a l (𝓝 0) := by
    have hh := hs0.div_const 100000
    simp only [zero_div] at hh
    exact hh.congr' (haeq.mono (fun _ h => h.symm))
  have hbeta := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  have htau := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/100000)
  have hD : Tendsto (fun i => (1:ℝ)*(a i)^(7-(1/100000:ℝ))) l (𝓝 0) := by
    simpa only [one_mul] using ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 7-(1/100000:ℝ))
  have herr := physical_potential_error_tendsto (D := fun _ => 1) hp ha0
    (by norm_num : (0:ℝ) < 1/100000) (by norm_num : (1/100000:ℝ) < 1/10) hD
  filter_upwards [hs,hpn,hp,ha,haeq,
    ha0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hbeta.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8)),
    htau.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8)),
    herr.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hsi hpni hpi hai haei ha1 hb1 hq1 he Z hZ N hN
  let b : ℝ := a i*(a i)^(1/5:ℝ)
  let q : ℝ := a i*(a i)^(1/100000:ℝ)
  have hb : 0 < b := mul_pos hai (Real.rpow_pos_of_pos hai _)
  have hq : 0 < q := mul_pos hai (Real.rpow_pos_of_pos hai _)
  have hba : 2*b ≤ a i := by dsimp [b]; nlinarith
  have hbb : b ≤ a i/8 := by dsimp [b]; nlinarith
  have hqq : q ≤ a i/8 := by dsimp [q]; nlinarith
  have hroot : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg 3]
  have hqr : q+Real.sqrt 3*b ≤ 4*a i := by nlinarith
  have hqR : q ≤ 3*(5*a i-4*b)/4 := by nlinarith
  have hc : a i ≤ b^2*(1/(a i)^3) := microscopic_collar hai ha1.le le_rfl
  have hu := actual_upper_deficit hZ (by positivity : 0 < ((s i)^4)⁻¹)
    hN (by norm_num : (0:ℝ) < 1) hpi ha1.le hb hba hq hqr hqR hc
  rw [hpni] at hu
  have hscale := mul_le_mul_of_nonneg_left hu (pow_nonneg hsi.le 3)
  have heb : (a i)^4*sharpPotentialRemainder (a i) b
      (localOffsetMass 1 (p i)) 1 q ≤ 1 := by
    simpa only [b,q,microscopicWidth_eq hai] using he.le
  rw [show localCellRadius (p i) = a i from rfl,haei,
    upperDeficit_rescale hsi] at hscale
  apply hscale.trans
  unfold quantumUpperDeficitConstant
  rw [haei] at heb
  nlinarith

end CoulombAtom

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CoulombAtom.actual_uniform_upper_deficit_oai.{u_1} := @OAI.CoulombAtom.actual_uniform_upper_deficit_oai.{u_1}
