-- Prove2me | solution 1 for OAI.CoulombAtom.TailTiltState.initial_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:42:23.45831+00:00
-- url     : https://prove2.me/submissions/20b7a692-a5a1-4ae4-966f-bd091092b720

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_actual_priced_particle_bound_three
import Theorems.Thm_OAI_CoulombAtom_normalized_inner_event_global_bound
import Theorems.Thm_OAI_CoulombAtom_quantum_energy_step_at_coarse_fence

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
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_SobolevVector
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
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma SobolevFermion.multiply {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (p : FermionMultiplier N) : SobolevFermion (multiplyForm p.toSmoothMultiplier ψ) := by
  have hw := hψ.sobolevVector.multiply p.toSmoothMultiplier
  refine ⟨hw.1, hw.2.1, hw.2.2, ?_⟩
  intro π s
  filter_upwards [hψ.2.2.2 π s] with x hx
  change (p.value (x ∘ π) : ℂ) * ψ.value (s ∘ π) (x ∘ π) =
    _ * ((p.value x : ℂ) * ψ.value s x)
  rw [p.symmetric, hx]
  ring

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

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
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Form
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

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

lemma insertionTerms_disjoint {N : ℕ} {T : FormVector (N+1)} (R : ℝ)
    (hc : ∀ x (j : Fin N), R ≤ ‖x j.castSucc‖ → FormZeroAt T x)
    (he : ∀ x, ‖x (Fin.last N)‖ < R → FormZeroAt T x) :
    FormsDisjoint (insertionTerm T) := by
  have hh (k l : Fin (N+1)) (hkl : k ≠ l) (x : Configuration (N+1)) :
      FormZeroAt (insertionTerm T k) x ∨ FormZeroAt (insertionTerm T l) x := by
    by_cases hk : ‖x k‖ < R
    · left
      exact insertionTerm_zero k (he _ (by simpa only [Function.comp_apply,insertionSwap_last] using hk))
    · right
      have hne : insertionSwap l k ≠ Fin.last N := by
        intro h
        have hh := congrArg (insertionSwap l) h
        exact hkl (by simpa only [insertionSwap,Equiv.swap_apply_self,Equiv.swap_apply_right] using hh)
      obtain ⟨j,hj⟩ := Fin.exists_castSucc_eq.mpr hne
      apply insertionTerm_zero l
      apply hc _ j
      simpa only [Function.comp_apply,hj,insertionSwap,Equiv.swap_apply_self] using le_of_not_gt hk
  constructor
  · intro k l hkl s x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl (hk s).1
    · exact Or.inr (hl s).1
  · intro k l hkl s i a x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl ((hk s).2 i a)
    · exact Or.inr ((hl s).2 i a)

lemma tensor_insertion_disjoint {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) (R : ℝ)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x)
    (he : ∀ x, ‖x 0‖ < R → FormZeroAt φ x) :
    FormsDisjoint (insertionTerm (tensorForm ψ φ)) := by
  apply insertionTerms_disjoint R
  · intro x i hx
    apply tensor_zero_left
    exact hc _ i hx
  · intro x hx
    apply tensor_zero_right
    exact he _ hx

theorem normalized_wedge_trial {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : FormAdmissible ψ) (hφ : FormAdmissible φ) (R : ℝ)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x)
    (he : ∀ x, ‖x 0‖ < R → FormZeroAt φ x) (Z : ℝ) :
    ∃ F : FormVector (N+1), FormAdmissible F ∧ formEnergy Z F = formEnergy Z (tensorForm ψ φ) := by
  let T := tensorForm ψ φ
  have hT := hψ.sobolevFermion.sobolevVector.tensor hφ.sobolevFermion.sobolevVector
  have hTa := tensor_coreAntisymmetric hψ.sobolevFermion φ
  have hd := tensor_insertion_disjoint ψ φ R hc he
  have hm : formMass T = 1 := by
    rw [formMass_tensor,formMass,formMass,hψ.2.2.2.2.1,hφ.2.2.2.2.1,one_mul]
  have hw := formMass_wedge hT hd
  rw [hm,mul_one] at hw
  have hp : 0 < formMass (wedgeForm T) := by rw [hw]; positivity
  refine ⟨scaleForm (Real.sqrt (formMass (wedgeForm T)))⁻¹ (wedgeForm T),
    (wedgeForm_fermion hT hTa).normalize hp,?_⟩
  rw [formEnergy_scale,formEnergy_wedge hT hd,hw,inv_pow,
    Real.sq_sqrt (le_of_lt (show (0:ℝ) < N+1 by positivity))]
  field_simp


open MeasureTheory Filter
open scoped BigOperators


lemma formNuclear_nonneg {N : ℕ} (ψ : FormVector N) : 0 ≤ formNuclear ψ := by
  apply Finset.sum_nonneg; intro s _
  apply Finset.sum_nonneg; intro i _
  exact integral_nonneg fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialInside
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
namespace CoulombAtom

lemma radialCut_inner {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : ‖x-y‖ ≤ t) :
    (radialCut y ht hb 0).value x = 1 ∧ (radialCut y ht hb 1).value x = 0 := by
  simp [radialCut, radialInside, radialOutside, radialPhase_zero ht hb hx]

end CoulombAtom

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TruncationRadius
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
namespace CoulombAtom

lemma truncationRadius_one_le (k : ℕ) : 1 ≤ truncationRadius k := by
  unfold truncationRadius; linarith [Nat.cast_nonneg (α := ℝ) k]

lemma SobolevFermion.truncate {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ) (k : ℕ) :
    SobolevFermion (truncateForm k ψ) := hψ.multiply (truncationMultiplier N k)

lemma truncation_value_le_one {N : ℕ} (k : ℕ) (x : Configuration N) :
    |(truncationMultiplier N k).value x| ≤ 1 :=
  spatial_product_sub_bound
    (radialCut 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (radialCut_partition 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (fun _ : Fin N => 0) x Finset.univ

lemma truncation_value_one {N : ℕ} (k : ℕ) (x : Configuration N)
    (hx : ∀ i, ‖x i‖ ≤ truncationRadius k) :
    (truncationMultiplier N k).value x = 1 := by
  change (∏ i, (radialCut 0 (truncationRadius_pos k).le
    (truncationRadius_pos k) 0).value (x i)) = 1
  apply Finset.prod_eq_one
  intro i _
  exact (radialCut_inner (truncationRadius_pos k).le (truncationRadius_pos k)
    (by simpa only [sub_zero] using hx i)).1

lemma truncation_derivative_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N) (a : Fin 3)
    (hx : ‖x i‖ ≤ truncationRadius k) :
    lineDeriv ℝ (truncationMultiplier N k).value x (direction i a) = 0 := by
  change lineDeriv ℝ (spatialProductValue _ _) x (direction i a) = 0
  rw [spatialProduct_derivative]
  change _ * lineDeriv ℝ (fun z => Real.cos (radialPhase 0 (truncationRadius k)
    (truncationRadius k) z)) (x i) (spaceDirections a) = 0
  rw [radial_cos_derivative, radialPhase_zero (truncationRadius_pos k).le
    (truncationRadius_pos k) (by simpa only [sub_zero] using hx)]
  simp only [Real.sin_zero, neg_zero, zero_mul, mul_zero]

lemma truncation_derivative_bound {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N) (a : Fin 3) :
    |lineDeriv ℝ (truncationMultiplier N k).value x (direction i a)| ≤
      Real.pi * smoothTransitionBound := by
  change |lineDeriv ℝ (spatialProductValue _ _) x (direction i a)| ≤ _
  rw [spatialProduct_derivative, abs_mul]
  have hprod := spatial_product_sub_bound
    (radialCut 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (radialCut_partition 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (fun _ : Fin N => 0) x (Finset.univ.erase i)
  apply (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans
  rw [one_mul]
  change |lineDeriv ℝ (fun z => Real.cos (radialPhase 0 (truncationRadius k)
    (truncationRadius k) z)) (x i) (spaceDirections a)| ≤ _
  rw [radial_cos_derivative, abs_mul, abs_neg]
  apply (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
  rw [one_mul]
  apply (radialPhase_derivative_le 0 (truncationRadius_pos k).le (truncationRadius_pos k) (x i) a).trans
  exact div_le_self (mul_pos Real.pi_pos smoothTransitionBound_pos).le (truncationRadius_one_le k)

lemma truncation_eventually_identity {N : ℕ} (x : Configuration N) :
    ∀ᶠ k : ℕ in atTop, (truncationMultiplier N k).value x = 1 ∧
      ∀ i a, lineDeriv ℝ (truncationMultiplier N k).value x (direction i a) = 0 := by
  obtain ⟨K,hK⟩ := exists_nat_gt ‖x‖
  refine eventually_atTop.mpr ⟨K,fun k hk => ?_⟩
  have hx (i : Fin N) : ‖x i‖ ≤ truncationRadius k := by
    have hki : (K:ℝ) ≤ k := by exact_mod_cast hk
    have hi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    unfold truncationRadius
    linarith
  exact ⟨truncation_value_one k x hx, fun i a => truncation_derivative_zero k x i a (hx i)⟩

lemma truncateForm_eventually_identity {N : ℕ} (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) :
    ∀ᶠ k : ℕ in atTop, (truncateForm k ψ).value s x = ψ.value s x ∧
      ∀ i a, (truncateForm k ψ).gradient s i a x = ψ.gradient s i a x := by
  filter_upwards [truncation_eventually_identity x] with k hk
  constructor
  · change ((truncationMultiplier N k).value x : ℂ) * _ = _
    rw [hk.1]; simp only [Complex.ofReal_one, one_mul]
  · intro i a
    change ((truncationMultiplier N k).value x : ℂ) * _ +
      Complex.ofReal (lineDeriv ℝ (truncationMultiplier N k).value x (direction i a)) * _ = _
    rw [hk.1,hk.2 i a]
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero]

lemma truncateForm_value_sq_le {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) : ‖(truncateForm k ψ).value s x‖^2 ≤ ‖ψ.value s x‖^2 := by
  change ‖((truncationMultiplier N k).value x : ℂ) * ψ.value s x‖^2 ≤ _
  rw [scaled_norm_sq]
  have hh := truncation_value_le_one k x
  have hs : (truncationMultiplier N k).value x ^ 2 ≤ 1 := by
    nlinarith [sq_abs ((truncationMultiplier N k).value x), abs_nonneg ((truncationMultiplier N k).value x)]
  exact mul_le_of_le_one_left (sq_nonneg _) hs

lemma truncateForm_gradient_sq_le {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i : Fin N) (a : Fin 3) :
    ‖(truncateForm k ψ).gradient s i a x‖^2 ≤
      2*‖ψ.gradient s i a x‖^2 + 2*(Real.pi*smoothTransitionBound)^2*‖ψ.value s x‖^2 := by
  have hC : 0 < Real.pi*smoothTransitionBound := mul_pos Real.pi_pos smoothTransitionBound_pos
  have hnorm : ‖(truncateForm k ψ).gradient s i a x‖ ≤
      ‖ψ.gradient s i a x‖ + (Real.pi*smoothTransitionBound)*‖ψ.value s x‖ := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (truncation_value_le_one k x))
      (mul_le_mul_of_nonneg_right (truncation_derivative_bound k x i a) (norm_nonneg _))
  nlinarith [sq_nonneg (‖ψ.gradient s i a x‖-(Real.pi*smoothTransitionBound)*‖ψ.value s x‖),
    norm_nonneg ((truncateForm k ψ).gradient s i a x), norm_nonneg (ψ.gradient s i a x),
    norm_nonneg (ψ.value s x)]

lemma truncateForm_mass_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    Tendsto (fun k => formMass (truncateForm k ψ)) atTop (𝓝 (formMass ψ)) := by
  unfold formMass
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => ‖ψ.value s x‖^2)
  · intro k; exact ((hψ.truncate k).1 s).norm.integrable_sq.aestronglyMeasurable
  · exact (hψ.1 s).norm.integrable_sq
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact truncateForm_value_sq_le k ψ s x
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.1])

lemma truncateForm_kinetic_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    Tendsto (fun k => ∫ x, ‖(truncateForm k ψ).gradient s i a x‖^2) atTop
      (𝓝 (∫ x, ‖ψ.gradient s i a x‖^2)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*‖ψ.gradient s i a x‖^2 + 2*(Real.pi*smoothTransitionBound)^2*‖ψ.value s x‖^2)
  · intro k; exact ((hψ.truncate k).2.1 s i a).norm.integrable_sq.aestronglyMeasurable
  · exact ((hψ.2.1 s i a).norm.integrable_sq.const_mul 2).add
      ((hψ.1 s).norm.integrable_sq.const_mul _)
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact truncateForm_gradient_sq_le k ψ s x i a
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.2 i a])

lemma truncateForm_coulomb_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (s : Spins N) (d : Configuration N → ℝ) (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hi : Integrable (fun x => ‖ψ.value s x‖^2 / d x)) :
    Tendsto (fun k => ∫ x, ‖(truncateForm k ψ).value s x‖^2 / d x) atTop
      (𝓝 (∫ x, ‖ψ.value s x‖^2 / d x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖ψ.value s x‖^2 / d x)
  · intro k
    exact (((hψ.truncate k).1 s).norm.integrable_sq.aemeasurable.div
      hd.aemeasurable).aestronglyMeasurable
  · exact hi
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hd0 x))]
      exact div_le_div_of_nonneg_right (truncateForm_value_sq_le k ψ s x) (hd0 x)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.1])

lemma truncateForm_energy_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (Z : ℝ) : Tendsto (fun k => formEnergy Z (truncateForm k ψ)) atTop
      (𝓝 (formEnergy Z ψ)) := by
  unfold formEnergy
  apply Tendsto.add
  · apply Tendsto.sub
    · apply Tendsto.const_mul
      apply tendsto_finsetSum; intro s _
      apply tendsto_finsetSum; intro i _
      apply tendsto_finsetSum; intro a _
      exact truncateForm_kinetic_tendsto hψ s i a
    · apply Tendsto.const_mul
      apply tendsto_finsetSum; intro s _
      apply tendsto_finsetSum; intro i _
      exact truncateForm_coulomb_tendsto hψ s (fun x => ‖x i‖)
        (measurable_pi_apply i).norm (fun _ => norm_nonneg _)
        (hψ.sobolevVector.nuclear_integrable s i)
  · apply tendsto_finsetSum; intro s _
    apply tendsto_finsetSum; intro i _
    apply tendsto_finsetSum; intro j _
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      exact truncateForm_coulomb_tendsto hψ s (fun x => ‖x i-x j‖)
        ((measurable_pi_apply i).sub (measurable_pi_apply j)).norm (fun _ => norm_nonneg _)
        (hψ.sobolevVector.pair_integrable s i j (ne_of_lt hij))
    · simp only [ite_eq_right hij]
      exact tendsto_const_nhds

lemma truncation_value_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N)
    (hx : 2*truncationRadius k ≤ ‖x i‖) : (truncationMultiplier N k).value x = 0 := by
  classical
  change (∏ j, (radialCut 0 (truncationRadius_pos k).le
    (truncationRadius_pos k) 0).value (x j)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply (radialCut_outer (truncationRadius_pos k).le (truncationRadius_pos k) ?_).1
  simpa only [sub_zero, two_mul] using hx

lemma truncateForm_support {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i : Fin N) (hx : 2*truncationRadius k ≤ ‖x i‖) :
    (truncateForm k ψ).value s x = 0 := by
  change ((truncationMultiplier N k).value x : ℂ) * _ = _
  rw [truncation_value_zero k x i hx]
  simp

lemma truncation_gradient_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i j : Fin N)
    (a : Fin 3) (hx : 2*truncationRadius k < ‖x i‖) :
    lineDeriv ℝ (truncationMultiplier N k).value x (direction j a) = 0 := by
  have he : (truncationMultiplier N k).value =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    have hh : ∀ᶠ z : Configuration N in 𝓝 x, 2*truncationRadius k < ‖z i‖ :=
      ((continuous_apply i).norm.tendsto x).eventually (eventually_gt_nhds hx)
    exact hh.mono fun z hz => truncation_value_zero k z i hz.le
  rw [he.lineDeriv_eq (𝕜 := ℝ)]
  simp only [lineDeriv, deriv_const]

lemma truncateForm_gradient_support {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i j : Fin N) (a : Fin 3) (hx : 2*truncationRadius k < ‖x i‖) :
    (truncateForm k ψ).gradient s j a x = 0 := by
  change ((truncationMultiplier N k).value x : ℂ) * _ +
    Complex.ofReal (lineDeriv ℝ (truncationMultiplier N k).value x (direction j a)) * _ = 0
  rw [truncation_value_zero k x i hx.le, truncation_gradient_zero k x i j a hx]
  simp

theorem admissible_compact_approximation {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) (Z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ φ : FormVector N, FormAdmissible φ ∧
      formEnergy Z φ < formEnergy Z ψ + ε ∧
      ∀ s x i, R ≤ ‖x i‖ → φ.value s x = 0 ∧ ∀ j a, φ.gradient s j a x = 0 := by
  let φ : ℕ → FormVector N := fun k =>
    scaleForm (Real.sqrt (formMass (truncateForm k ψ)))⁻¹ (truncateForm k ψ)
  have hm := truncateForm_mass_tendsto hψ.sobolevFermion
  have hmass : formMass ψ = 1 := hψ.2.2.2.2.1
  rw [hmass] at hm
  have he : Tendsto (fun k => formEnergy Z (φ k)) atTop (𝓝 (formEnergy Z ψ)) := by
    have hh := (((Real.continuous_sqrt.tendsto 1).comp hm).inv₀ (by norm_num)).pow 2
    have hh' := hh.mul (truncateForm_energy_tendsto hψ.sobolevFermion Z)
    simpa only [φ, formEnergy_scale, Real.sqrt_one, inv_one, one_pow, one_mul, Function.comp_apply] using hh'
  have hp : ∀ᶠ k : ℕ in atTop, 0 < formMass (truncateForm k ψ) :=
    hm.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 1))
  have hene : ∀ᶠ k : ℕ in atTop, formEnergy Z (φ k) < formEnergy Z ψ + ε :=
    he.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨k,hk,hke⟩ := (hp.and hene).exists
  refine ⟨3*truncationRadius k, mul_pos (by norm_num) (truncationRadius_pos k), φ k,
    (hψ.sobolevFermion.truncate k).normalize hk,hke,?_⟩
  intro s x i hx
  have hx' : 2*truncationRadius k < ‖x i‖ := by linarith [truncationRadius_pos k]
  constructor
  · change _ * (truncateForm k ψ).value s x = 0
    rw [truncateForm_support k ψ s x i hx'.le, mul_zero]
  · intro j a
    change _ * (truncateForm k ψ).gradient s j a x = 0
    rw [truncateForm_gradient_support k ψ s x i j a hx', mul_zero]

theorem quantum_sector_compact_near_minimizer (Z : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ φ : FormVector N, FormAdmissible φ ∧
      formEnergy Z φ < energy Z N + ε ∧
      ∀ s x i, R ≤ ‖x i‖ → φ.value s x = 0 ∧ ∀ j a, φ.gradient s j a x = 0 := by
  obtain ⟨F,hF,he⟩ := quantum_sector_near_minimizer Z N (half_pos hε)
  obtain ⟨R,hR,φ,hφ,hq,hs⟩ := admissible_compact_approximation
    (graphFormVector_admissible F hF) Z (half_pos hε)
  exact ⟨R,hR,φ,hφ,by linarith,hs⟩

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_DiffuseSeed
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

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

lemma diffuseSeed_smooth (R : ℝ) : ContDiff ℝ ∞ (diffuseSeed R) :=
  (trialSeed_smooth 1).comp (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).contDiff

lemma diffuseSeed_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (diffuseSeed R) :=
  (trialSeed_compact 1).comp_smul (inv_ne_zero hR.ne')

lemma diffuseRaw_sobolev (R : ℝ) (hR : 0 < R) : SobolevFermion (diffuseRaw R) := by
  refine ⟨fun _ => (diffuseSeed_smooth R).continuous.memLp_of_hasCompactSupport
    (diffuseSeed_compact hR),fun s i a => ?_,fun s i a φ hφ hcφ => ?_,?_⟩
  · exact (smooth_derivative_continuous (diffuseSeed_smooth R) _).memLp_of_hasCompactSupport
      (compact_derivative (diffuseSeed_compact hR) _)
  · exact smooth_weak_gradient (diffuseSeed_smooth R) (diffuseSeed_compact hR) hφ hcφ _
  · intro π s
    have hp : π = 1 := Subsingleton.elim _ _
    subst π
    exact Eventually.of_forall fun x => by simp [diffuseRaw,smoothForm]

lemma diffuseRaw_mass_pos {R : ℝ} (hR : 0 < R) : 0 < formMass (diffuseRaw R) := by
  have hn : diffuseSeed R (R • trialCenter 1) = 1 := by
    simp only [diffuseSeed,smul_smul,inv_mul_cancel₀ hR.ne',one_smul,trialSeed_center]
  have hi : 0 < ∫ x, ‖diffuseSeed R x‖^2 :=
    ((diffuseSeed_smooth R).continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq (diffuseSeed_compact hR)) (fun x => sq_nonneg _)
      (x := R • trialCenter 1) (by rw [hn]; norm_num)
  change 0 < ∑ _s : Spins 1, ∫ x, ‖diffuseSeed R x‖^2
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hi

lemma diffuseRaw_gradient (R : ℝ) (s : Spins 1) (i : Fin 1) (a : Fin 3) (x : Configuration 1) :
    (diffuseRaw R).gradient s i a x = R⁻¹ •
      (smoothForm (trialSeed 1)).gradient s i a (R⁻¹ • x) := by
  change fderiv ℝ ((trialSeed 1) ∘ ⇑(R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1))) x (direction i a) = _
  rw [fderiv_comp x ((trialSeed_smooth 1).differentiable (by simp)).differentiableAt
    (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,smoothForm]

lemma diffuseRaw_mass (R : ℝ) (hR : 0 < R) :
    formMass (diffuseRaw R) = R ^ Module.finrank ℝ (Configuration 1) *
      formMass (smoothForm (trialSeed 1)) := by
  unfold formMass
  simp only [diffuseRaw,smoothForm,diffuseSeed]
  have hi := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
    (fun x => ‖trialSeed 1 x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,Finset.mul_sum]

lemma diffuseRaw_kinetic (R : ℝ) (hR : 0 < R) :
    formKinetic (diffuseRaw R) = R⁻¹^2 * R ^ Module.finrank ℝ (Configuration 1) *
      formKinetic (smoothForm (trialSeed 1)) := by
  unfold formKinetic
  simp_rw [diffuseRaw_gradient,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  have hi (s : Spins 1) (i : Fin 1) (a : Fin 3) :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
      (fun x => ‖(smoothForm (trialSeed 1)).gradient s i a x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,← Finset.mul_sum]
  ring

lemma diffuseOrbital_admissible {R : ℝ} (hR : 0 < R) : FormAdmissible (diffuseOrbital R) :=
  (diffuseRaw_sobolev R hR).normalize (diffuseRaw_mass_pos hR)

lemma diffuseOrbital_kinetic {R : ℝ} (hR : 0 < R) :
    formKinetic (diffuseOrbital R) = diffuseKinetic / R^2 := by
  have hmpos : 0 < formMass (smoothForm (trialSeed 1)) := by
    have hh := diffuseRaw_mass_pos (by norm_num : (0:ℝ)<1)
    rw [diffuseRaw_mass 1 (by norm_num), one_pow, one_mul] at hh
    exact hh
  rw [diffuseOrbital,formKinetic_scale,inv_pow,Real.sq_sqrt (diffuseRaw_mass_pos hR).le,
    diffuseRaw_mass R hR,diffuseRaw_kinetic R hR,diffuseKinetic]
  field_simp

lemma diffuseSeed_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    diffuseSeed R x = 0 := by
  by_contra hn
  have hh := trialSeed_nucleus hn (0 : Fin 1)
  change 1 ≤ ‖R⁻¹ • x 0‖ at hh
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)] at hh
  have hl : R⁻¹ * ‖x 0‖ < 1 := by
    rw [← div_eq_inv_mul,div_lt_one hR]
    exact hx
  exact not_lt_of_ge hh hl

lemma diffuseRaw_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    FormZeroAt (diffuseRaw R) x := by
  have he : diffuseSeed R =ᶠ[𝓝 x] fun _ => (0:ℂ) :=
    (((continuous_apply (0 : Fin 1)).norm.tendsto x).eventually (eventually_lt_nhds hx)).mono
      fun _ hy => diffuseSeed_zero hR hy
  intro s
  refine ⟨diffuseSeed_zero hR hx,fun i a => ?_⟩
  change fderiv ℝ (diffuseSeed R) x (direction i a) = 0
  rw [he.fderiv_eq]
  simp

lemma diffuseOrbital_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    FormZeroAt (diffuseOrbital R) x := by
  intro s
  have hh := diffuseRaw_zero hR hx s
  constructor
  · change _ * (diffuseRaw R).value s x = 0
    rw [hh.1,mul_zero]
  · intro i a
    change _ * (diffuseRaw R).gradient s i a x = 0
    rw [hh.2,mul_zero]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


lemma tensorCross_le {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) {R d : ℝ} (hd : 0 < d)
    (hc : ∀ s x i, R ≤ ‖x i‖ → ψ.value s x = 0)
    (he : ∀ s x, ‖x 0‖ < R+d → φ.value s x = 0) :
    tensorCross ψ φ ≤ (N : ℝ)/d * formMass ψ * formMass φ := by
  have hT := hψ.tensor hφ
  have hi (s : Spins N) (t : Spins 1) (i : Fin N) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z (Fin.last N)‖) ≤
      d⁻¹ * (∫ x, ‖ψ.value s x‖^2) * (∫ y, ‖φ.value t y‖^2) := by
    have hn : i.castSucc ≠ Fin.last N := Fin.castSucc_ne_last i
    calc
      _ ≤ ∫ z, d⁻¹ * ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 := by
        apply integral_mono
          (pair_integrable _ _ hn (hT.1 _) (hT.2.1 _ _) (hT.2.2 _ _))
          (((hT.1 _).integrable_norm_pow (by norm_num)).const_mul d⁻¹)
        intro z
        dsimp only
        by_cases hz : (tensorForm ψ φ).value (joinLists s t) z = 0
        · simp only [hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_div,mul_zero,le_refl]
        · have hz' : ψ.value s (leftList z) ≠ 0 ∧ φ.value t (rightList z) ≠ 0 := by
            simpa only [tensorForm,leftList_join,rightList_join,mul_ne_zero_iff] using hz
          have hin : ‖z i.castSucc‖ < R := lt_of_not_ge fun h => hz'.1 (hc _ _ i h)
          have hout : R+d ≤ ‖z (Fin.last N)‖ := le_of_not_gt fun h => hz'.2 (he _ _ h)
          have hg : d ≤ ‖z i.castSucc-z (Fin.last N)‖ := by
            have ht := norm_sub_norm_le (z (Fin.last N)) (z i.castSucc)
            rw [norm_sub_rev] at ht
            linarith
          rw [← div_eq_inv_mul]
          exact div_le_div_of_nonneg_left (sq_nonneg _) hd hg
      _ = _ := by
        rw [integral_const_mul]
        have hh : (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2) =
            (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2) := by
          simp only [tensorForm,leftList_join,rightList_join,norm_mul,mul_pow]
          exact integral_product_join (N := N) (M := 1)
            (fun x => ‖ψ.value s x‖^2) (fun y => ‖φ.value t y‖^2)
        rw [hh,mul_assoc]
  calc
    tensorCross ψ φ ≤ ∑ s : Spins N, ∑ t : Spins 1, ∑ _i : Fin N,
        d⁻¹ * (∫ x, ‖ψ.value s x‖^2) * (∫ y, ‖φ.value t y‖^2) := by
      exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ => hi s t i
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      unfold formMass
      simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
      ring

lemma exterior_insertion_trial {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {Z R r : ℝ} (hZ : 0 ≤ Z) (hR : 0 < R) (hr : 2*R ≤ r)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x) :
    ∃ F : FormVector (N+1), FormAdmissible F ∧
      formEnergy Z F ≤ formEnergy Z ψ + diffuseKinetic/r^2 + 2*(N : ℝ)/r := by
  have hrp : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) hR) hr
  have hφ := diffuseOrbital_admissible hrp
  obtain ⟨F,hF,hFE⟩ := normalized_wedge_trial hψ hφ R hc
    (fun x hx => diffuseOrbital_zero hrp (lt_of_lt_of_le hx (by linarith))) Z
  refine ⟨F,hF,?_⟩
  have hcross := tensorCross_le hψ.sobolevFermion.sobolevVector
    hφ.sobolevFermion.sobolevVector (R := R) (d := r/2) (half_pos hrp)
    (fun s x i hx => (hc x i hx s).1)
    (fun s x hx => (diffuseOrbital_zero hrp (lt_of_lt_of_le hx (by linarith)) s).1)
  have hmψ : formMass ψ = 1 := hψ.2.2.2.2.1
  have hmφ : formMass (diffuseOrbital r) = 1 := hφ.2.2.2.2.1
  rw [hmψ,hmφ,mul_one,mul_one] at hcross
  rw [hFE,formEnergy_tensor_one,hmψ,hmφ,mul_one,one_mul,diffuseOrbital_kinetic hrp]
  have hn := mul_nonneg hZ (formNuclear_nonneg (diffuseOrbital r))
  have hc' : (N : ℝ)/(r/2) = 2*(N : ℝ)/r := by ring
  rw [hc'] at hcross
  linarith

theorem quantum_energy_succ_le {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) :
    energy Z (N+1) ≤ energy Z N := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R,hR,ψ,hψ,hene,hc⟩ := quantum_sector_compact_near_minimizer Z N (half_pos hε)
  have ht : Tendsto (fun r : ℝ => diffuseKinetic/r^2 + 2*(N : ℝ)/r) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := diffuseKinetic)).div_atTop
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    have hk := (tendsto_const_nhds (x := 2*(N : ℝ))).div_atTop tendsto_id
    simpa only [zero_add, id_eq] using hh.add hk
  have he : ∀ᶠ r : ℝ in atTop, diffuseKinetic/r^2 + 2*(N : ℝ)/r < ε/2 :=
    ht.eventually (eventually_lt_nhds (half_pos hε))
  obtain ⟨r,hlarge,herror⟩ := ((eventually_ge_atTop (2*R)).and he).exists
  obtain ⟨F,hF,hbound⟩ := exterior_insertion_trial hψ hZ hR hlarge
    (fun x i hx s => hc s x i hx)
  have hl := energy_le_form hZ hF
  linarith

theorem quantum_energy_antitone {Z : ℝ} (hZ : 0 ≤ Z) : Antitone (energy Z) :=
  antitone_nat_of_succ_le (quantum_energy_succ_le hZ)


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

lemma physicalObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (physicalObservedConfiguration (N := N) ell k) := by
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact (((EuclideanSpace.proj a : Space →L[ℝ] ℝ).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    (((measurable_pi_apply (k,i,a)).comp measurable_snd).const_mul _))

lemma unorderedObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (unorderedObservedConfiguration (N := N) ell k) :=
  unorderedConfiguration_measurable.comp (physicalObservedConfiguration_measurable ell k)

lemma observationInformation_le {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j ≤
      (inferInstance : MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (unorderedObservedConfiguration_measurable ell k).comap_le
  · exact bot_le

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

lemma masterKernel_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ masterKernel c₁ r₀ s g x y := sq_nonneg _

lemma masterKernel_joint_continuous {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Continuous (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2) := by
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := (masterWidth_lipschitz hc.le hr hs).continuous.comp (continuous_fst : Continuous (Prod.fst : Space × Space → Space))
  have hi := ht.inv₀ (fun p => (masterWidth_pos hc hr hs p.1).ne')
  exact (hi.pow 3).mul ((hg.pow 2).comp (hi.smul (continuous_snd.sub continuous_fst)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open CoulombObservation ProbabilityTheory

lemma originalDatum_measurable {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    Measurable (originalDatum (N := N) ell j) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap id (observationInformation ell j) ≤ _
  simpa only [MeasurableSpace.comap_id] using (observationInformation_le (N := N) ell j)

lemma originalDatum_comap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace.comap (originalDatum (N := N) ell j) inferInstance =
      observationInformation ell j := MeasurableSpace.comap_id

lemma kernelPosteriorTest_eq {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    posteriorTestValue μ ell j g =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z) := by
  have h := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable
    ((Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))).stronglyMeasurable) hi
  simpa only [originalDatum_comap,posteriorTestValue,kernelPosteriorTest,originalRawKernel,Function.comp_def] using h

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterJointPosterior
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma jointMasterPosterior_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  have h : StronglyMeasurable (fun p : (OriginalDatum N K ell j × Space) × Configuration N =>
      ∑ i, masterKernel c₁ r₀ s g (p.2 i) p.1.2) :=
    (Finset.measurable_sum _ (fun i _ => hm.comp
      (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst.snd))).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := (originalRawKernel μ ell j).comap Prod.fst measurable_fst)).measurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormRawPotential
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

lemma rawPotential_measurable {N : ℕ} (y : Space) : Measurable (rawPotential (N := N) y) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.div (configuration_distance_measurable y i))

lemma formRawLaw_ae_no_poles {N : ℕ} (ψ : FormVector N) (y : Space) :
    ∀ᵐ x ∂formRawLaw ψ, ∀ i, x i ≠ y := by
  apply (withDensity_absolutelyContinuous volume _).ae_le
  exact ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure Space)) i y)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_MasterPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma scaled_packet_density_radial (b : ℝ) {g : Space → ℝ} (hr : IsRadial g) :
    IsRadial (fun x => (scaledRealPacket b g x)^2) := by
  intro x y hxy
  dsimp only
  rw [scaledRealPacket_radial b hr x y hxy]

lemma scaled_packet_density_support {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) (x : Space) (hx : (scaledRealPacket b g x)^2 ≠ 0) :
    ‖x‖ ≤ b := (scaledRealPacket_support hb hs (by intro hz; exact hx (by rw [hz]; norm_num))).le

lemma scaled_packet_potential_le {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x, (g x)^2 = 1) (hr : IsRadial g) (hs : tsupport g ⊆ ball 0 1)
    {x : Space} (hx : x ≠ 0) :
    tfPotential (fun z => (scaledRealPacket b g z)^2) x ≤ 1/‖x‖ := by
  have hc : Continuous (fun z => (scaledRealPacket b g z)^2) := by
    exact (scaledRealPacket_smooth b hg).continuous.pow 2
  have hcomp : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
    convert! (scaledRealPacket_compact hb hcg).mul_right (f' := scaledRealPacket b g) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact pow_two _
  have hh := radial_potential_le_point (hc.integrable_of_hasCompactSupport hcomp)
    (hc.memLp_of_hasCompactSupport hcomp) (fun z => sq_nonneg _)
    (scaled_packet_density_radial b hr) hb.le (scaled_packet_density_support hb hs) hx
  simpa only [scaledRealPacket_mass hb,hgn] using hh

lemma masterKernel_potential_centered (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    tfPotential (masterKernel c₁ r₀ s g x) y =
      tfPotential (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) (y-x) :=
  integral_translated_pole (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) y x

lemma masterKernel_potential_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ tfPotential (masterKernel c₁ r₀ s g x) y :=
  tfPotential_nonneg (ae_of_all _ (masterKernel_nonneg c₁ r₀ s g x)) y

lemma masterKernel_potential_le {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : x ≠ y) :
    tfPotential (masterKernel c₁ r₀ s g x) y ≤ 1/‖y-x‖ := by
  rw [masterKernel_potential_centered]
  exact scaled_packet_potential_le (masterWidth_pos hc hr hs x) hg hcg hgn hrad hgs
    (sub_ne_zero.mpr hxy.symm)

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

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

open CoulombAnalysis

lemma scaled_packet_density_compact {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
  convert! (scaledRealPacket_compact hb hg).mul_right (f' := scaledRealPacket b g) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact pow_two _

lemma masterKernel_pole_measurable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) (y : Space) :
    Measurable (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) := by
  have hm : Measurable (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterKernelFubini
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAnalysis

lemma masterKernel_pole_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x y : Space) :
    Integrable (fun z => masterKernel c₁ r₀ s g x z/‖y-z‖) := by
  have hη := scaled_packet_density_compact (masterWidth_pos hc hr hs x) hcg
  have hηc := (scaledRealPacket_smooth (masterWidth c₁ r₀ s x) hg).continuous.pow 2
  exact translated_pole_integrable (hηc.integrable_of_hasCompactSupport hη)
    (hηc.memLp_of_hasCompactSupport hη) y x

lemma master_configuration_potential_integrable {N : ℕ} (ν : Measure (Configuration N))
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun x : Configuration N => ∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y) ν := by
  apply hi.mono' ((Finset.measurable_sum _ (fun i _ =>
    (masterKernel_pole_measurable hc hr hs hg.continuous y).comp (measurable_pi_apply i))).aestronglyMeasurable)
  filter_upwards [he] with x hx
  change ‖∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y‖ ≤ rawPotential y x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_potential_nonneg c₁ r₀ s g (x i) y))]
  apply Finset.sum_le_sum
  intro i _
  simpa only [norm_sub_rev] using masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs (hx i)

lemma master_configuration_pole_integrable {N : ℕ} (ν : Measure (Configuration N))
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun p : Configuration N × Space => (∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)/‖y-p.2‖)
      (ν.prod volume) := by
  have hm : Measurable (fun p : Configuration N × Space => (∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)/‖y-p.2‖) :=
    (Finset.measurable_sum _ (fun i _ => (masterKernel_joint_continuous hc hr hs hg.continuous).measurable.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))).div (by fun_prop)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => ?_),?_⟩
  · simp only [Finset.sum_div]
    exact integrable_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y)
  · have hp := master_configuration_potential_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Finset.sum_div]
    simp_rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ =>
      div_nonneg (masterKernel_nonneg c₁ r₀ s g (x i) _) (norm_nonneg _)))]
    exact integral_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y)

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombObservation ProbabilityTheory

lemma originalRawKernel_comp {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) :
    originalRawKernel μ ell j ∘ₘ ((physicalObservationLaw μ K).map (originalDatum ell j)) = μ := by
  rw [originalRawKernel,condDistrib_comp_map (originalDatum_measurable ell j).aemeasurable
    measurable_fst.aemeasurable]
  simp [physicalObservationLaw,Measure.map_fst_prod]

lemma originalRawKernel_ae {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {P : Configuration N → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ᵐ x ∂originalRawKernel μ ell j (originalDatum ell j z), P x := by
  rw [←originalRawKernel_comp μ ell j] at hP
  exact ae_of_ae_map (originalDatum_measurable ell j).aemeasurable (Measure.ae_ae_of_ae_comp hP)

lemma originalRawKernel_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {f : Configuration N → ℝ} (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      Integrable f (originalRawKernel μ ell j (originalDatum ell j z)) := by
  have hx := originalDatum_measurable (N := N) ell j
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hi0 : Integrable (fun a : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => f a.1)
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  have hi1 : Integrable (fun p : OriginalDatum N K ell j × Configuration N => f p.2)
      ((physicalObservationLaw μ K).map (fun a => (originalDatum ell j a,a.1))) := by
    apply (integrable_map_measure (hf.comp measurable_snd).aestronglyMeasurable
      (hx.prodMk measurable_fst).aemeasurable).mpr
    exact hi0
  exact hi1.condDistrib_ae hx.aemeasurable measurable_fst.aemeasurable

lemma kernelPosteriorTest_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ) :
    Integrable (fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z))
      (physicalObservationLaw μ K) := by
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hf : Measurable (fun x : Configuration N => ∑ i, g (x i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hg.comp (measurable_pi_apply i))
  have hi0 : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => ∑ i, g (z.1 i))
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  exact integrable_condExp.congr (kernelPosteriorTest_eq μ ell j hg hi0)

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

lemma formRawLaw_graph {N : ℕ} (F : fermionGraph N) :
    formRawLaw (graphFormVector F) = graphRawLaw F := rfl

lemma formMass_graph {N : ℕ} (F : fermionGraph N) :
    formMass (graphFormVector F) = ‖fermionGraphValue N F‖^2 := by
  rw [←formRawDensity_integral (graphFormVector_sobolev F).sobolevVector]
  exact graphRawDensity_integral F

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ActualSectorPlateau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
attribute [local irreducible] fermionGraph fermionGraphValue graphFormVector
  formEnergy energy

theorem quantum_energy_plateau (Z n : ℕ) (hn : 2*Z+1 ≤ n) :
    energy Z n = energy Z (2*Z+1) := by
  have h (k : ℕ) : energy Z (2*Z+1+k) = energy Z (2*Z+1) := by
    induction k with
    | zero => simp only [Nat.add_zero]
    | succ k hk =>
      rw [show 2*Z+1+(k+1)=(2*Z+1+k)+1 by omega,
        quantum_energy_step_at_coarse_fence Z _ (by omega),hk]
  simpa only [Nat.add_sub_of_le hn] using h (n-(2*Z+1))

lemma quantum_energy_coarse_fence_minimum (Z n : ℕ) :
    energy Z (2*Z+1) ≤ energy Z n := by
  by_cases hn : n ≤ 2*Z+1
  · exact quantum_energy_antitone (Nat.cast_nonneg Z) hn
  · exact (quantum_energy_plateau Z n (by omega)).symm.le

theorem quantum_unpriced_infimum_finite (Z : ℕ) :
    sInf (Set.range (energy (Z:ℝ))) = energy Z (2*Z+1) := by
  have hb : BddBelow (Set.range (energy (Z:ℝ))) := by
    refine ⟨energy Z (2*Z+1),?_⟩
    rintro x ⟨n,rfl⟩
    exact quantum_energy_coarse_fence_minimum Z n
  apply le_antisymm
  · exact csInf_le hb ⟨2*Z+1,rfl⟩
  · apply le_csInf (s := Set.range (energy (Z:ℝ))) ⟨_,2*Z+1,rfl⟩
    rintro x ⟨n,rfl⟩
    exact quantum_energy_coarse_fence_minimum Z n

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ActualUnshiftedBudget
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector
  fermionGraph weakGraph fermionGraphValue formEnergy energy corePriceExcess

lemma actual_priced_excess_unshifted_bound (Z : ℕ) {lam : ℝ} (hlam : 0 < lam)
    {N : ℕ} (G : fermionGraph N) (hn : ‖fermionGraphValue N G‖^2 = 1)
    {e : ℝ} (he : corePriceExcess Z lam (graphFormVector G) ≤ e) :
    formEnergy Z (graphFormVector G) ≤ sInf (Set.range (energy (Z:ℝ)))+
      lam*(2*(Z:ℝ)+1-(N:ℝ))+e := by
  have hp := quantum_price_le_sector (Nat.cast_nonneg Z) hlam (2*Z+1)
  rw [quantum_unpriced_infimum_finite]
  rw [corePriceExcess,formMass_graph,hn,mul_one,mul_one] at he
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hp
  nlinarith only [he,hp]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTruncationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierTruncation_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma innerPotential_nonneg {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z) (r : ℝ) (y : Space) :
    0 ≤ innerPotential r ρ y := integral_nonneg (fun z => div_nonneg (hn z) (norm_nonneg _))

lemma inner_master_potential_measurable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) (r : ℝ) (y : Space) :
    Measurable (fun x => innerPotential r (masterKernel c₁ r₀ s g x) y) := by
  have hm : Measurable (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma inner_master_potential_le {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (r : ℝ) (x y : Space) :
    innerPotential r (masterKernel c₁ r₀ s g x) y ≤ tfPotential (masterKernel c₁ r₀ s g x) y := by
  exact setIntegral_le_integral (masterKernel_pole_integrable hc hr hs hg hcg x y)
    (ae_of_all _ (fun z => div_nonneg (masterKernel_nonneg c₁ r₀ s g x z) (norm_nonneg _)))

lemma inner_master_configuration_integrable {N : ℕ} (ν : Measure (Configuration N))
    (r : ℝ) (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun x : Configuration N => ∑ i, innerPotential r (masterKernel c₁ r₀ s g (x i)) y) ν := by
  apply hi.mono' ((Finset.measurable_sum _ (fun i _ =>
    (inner_master_potential_measurable hc hr hs hg.continuous r y).comp (measurable_pi_apply i))).aestronglyMeasurable)
  filter_upwards [he] with x hx
  change ‖∑ i, innerPotential r (masterKernel c₁ r₀ s g (x i)) y‖ ≤ rawPotential y x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ =>
    innerPotential_nonneg (masterKernel_nonneg c₁ r₀ s g (x i)) r y))]
  apply Finset.sum_le_sum
  intro i _
  exact (inner_master_potential_le hc hr hs hg hcg r (x i) y).trans
    (by simpa only [norm_sub_rev] using masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs (hx i))

theorem inner_master_configuration_fubini {N : ℕ} (ν : Measure (Configuration N)) [SFinite ν]
    (r : ℝ) (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    innerPotential r (fun z => ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν) y =
      ∫ x, ∑ i, innerPotential r (masterKernel c₁ r₀ s g (x i)) y ∂ν := by
  have hp := (master_configuration_pole_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs).mono_measure
    (Measure.prod_mono (le_refl ν) (Measure.restrict_le_self (s := ball (0 : Space) r)))
  unfold innerPotential
  calc
    _ = ∫ z in ball (0 : Space) r, ∫ x, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖ ∂ν := by
      simp only [integral_div]
    _ = ∫ x, (∫ z in ball (0 : Space) r, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖) ∂ν :=
      integral_integral_swap hp.swap
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [Finset.sum_div]
        exact integral_finsetSum _ (fun i _ => (masterKernel_pole_integrable hc hr hs hg hcg (x i) y).integrableOn))

end CoulombAtom

end Work_BarrierTruncation_barrier_scope

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_BarrierInitialEventBarrier
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

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis

lemma jointMasterPosterior_inner_eq_kernel {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (r : ℝ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    (fun z => innerPotential r (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y) =ᵐ[
      physicalObservationLaw μ K] fun z => kernelPosteriorTest μ ell j
        (fun x => innerPotential r (masterKernel c₁ r₀ s g x) y) (originalDatum ell j z) := by
  filter_upwards [originalRawKernel_integrable μ ell j (rawPotential_measurable y) hi,
    originalRawKernel_ae μ ell j he] with z hz hze
  exact inner_master_configuration_fubini _ r y hz hze hc hr hs hg hcg hgn hrad hgs

lemma jointMasterPosterior_inner_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (r : ℝ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun z => innerPotential r (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y)
      (physicalObservationLaw μ K) :=
  (kernelPosteriorTest_integrable μ ell j (inner_master_potential_measurable hc hr hs hg.continuous r y)
    (inner_master_configuration_integrable μ r y hi he hc hr hs hg hcg hgn hrad hgs)).congr
      (jointMasterPosterior_inner_eq_kernel μ ell j r y hi he hc hr hs hg hcg hgn hrad hgs).symm

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_inner_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (r : ℝ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      innerPotential r (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma threshold_event_mean_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hi : Integrable f μ) {t : ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hAB : ∀ z ∈ A, t ≤ f z) (hp : 0 < (μ A).toReal) :
    t ≤ ((μ A).toReal)⁻¹*(∫ z in A, f z ∂μ) := by
  have he : (μ A).toReal*t ≤ ∫ z in A, f z ∂μ := by
    calc
      _ = ∫ z in A, t ∂μ := by simp [Measure.real,smul_eq_mul]
      _ ≤ _ := setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn hA hAB
  have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailInitialPointwiseBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_TailInitialPointwise_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem TailTiltState.initial_pointwise_oai {Z : ℕ} (hZ : 1 ≤ Z)
    {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) {N K : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ θ : ℝ}
    {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
    (j : Fin (K+1)) (h₀ : 0 < p₀ j)
    (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < θ)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    (y : Space) (hy : ‖y‖ ≤ (11/10)*r₀) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | θ < innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
        (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
          (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r₀ k
  let P : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) → ℝ :=
    fun z => innerPotential r₀ (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
  let A := {z | θ < P z}
  have hA : MeasurableSet[observationInformation ell j] A :=
    measurableSet_lt measurable_const
      (jointMasterPosterior_inner_measurable (graphRawLaw F) ell j r₀ y hc hr hs hg.continuous)
  let p := ((physicalObservationLaw (graphRawLaw F) K) A).toReal
  change p < p₀ j
  by_contra! hnot
  have hp : 0 < p := h₀.trans_le hnot
  obtain ⟨G,hGn,hlaw,hE⟩ := hF.2.2 j A hA hnot
  have hb : formEnergy Z (graphFormVector G) ≤ allSectorEnergy Z+(Z:ℝ)^(7/3:ℝ) := by
    have he := actual_priced_excess_unshifted_bound Z hlam G hGn ((le_max_left _ _).trans hE)
    have hz : (1:ℝ) ≤ Z := by exact_mod_cast hZ
    have hnon : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    have hcoarse : lam*(2*(Z:ℝ)+1-(N:ℝ)) ≤ 3*(Z:ℝ)*lam := by nlinarith
    change formEnergy Z (graphFormVector G) ≤ sInf (Set.range (energy (Z:ℝ)))+(Z:ℝ)^(7/3:ℝ)
    linarith only [he,hcoarse,hbudget]
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hcount := actual_priced_particle_bound_three Z hZ hlam hN
  have hupper := normalized_inner_event_global_bound (graphRawLaw F)
    (graphFormVector_admissible G hGn) ell j y hi he hc hc1 hr hs hs1 hg hcg hgn hrad hgs hy hA hp
    (by simpa only [formRawLaw_graph] using hlaw)
    (show (1:ℝ) ≤ Z by exact_mod_cast hZ) (Real.rpow_nonneg (Nat.cast_nonneg Z) _)
    (show (N:ℝ) ≤ 3*Z by exact_mod_cast hcount) hb
  have hPi : Integrable P (physicalObservationLaw (graphRawLaw F) K) :=
    jointMasterPosterior_inner_integrable (graphRawLaw F) ell j r₀ y hi he hc hr hs hg hcg hgn hrad hgs
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K) hPi
    ((observationInformation_le ell j) A hA) (fun z hz => hz.le) hp
  exact (not_le_of_gt (hupper.trans_lt hsmall)) hlower

end CoulombAtom

end Work_TailInitialPointwise_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.TailTiltState.initial_pointwise_oai := @OAI.CoulombAtom.TailTiltState.initial_pointwise_oai
