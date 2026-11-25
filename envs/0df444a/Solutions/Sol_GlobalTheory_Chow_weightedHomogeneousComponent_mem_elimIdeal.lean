-- Prove2me | solution 1 for GlobalTheory.Chow.weightedHomogeneousComponent_mem_elimIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:19.509303+00:00
-- url     : https://prove2.me/submissions/6a27ac7f-43a1-405a-8489-c5d9499e82c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_isBlockHomogeneous_linForm
import Theorems.Thm_GlobalTheory_Chow_map_weightedHomogeneousComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']
namespace GlobalTheory.Chow
theorem _root_.solution [Fintype σ] [Finite β]
    {p : Ideal (MvPolynomial σ K)}
    {f : MvPolynomial (β × σ) K} (hf : f ∈ elimIdeal β p) (a : β → ℕ) :
    weightedHomogeneousComponent blockWeight a f ∈ elimIdeal β p := by
  classical
  letI := weightedGradedAlgebra (MvPolynomial σ K) (blockWeight : β × σ → β → ℕ)
  have hI : (incidenceIdeal β p).IsHomogeneous
      (weightedHomogeneousSubmodule (MvPolynomial σ K) (blockWeight : β × σ → β → ℕ)) := by
    refine Ideal.IsHomogeneous.sup (Ideal.homogeneous_span _ _ ?_) (Ideal.homogeneous_span _ _ ?_)
    · rintro _ ⟨g, -, rfl⟩
      exact ⟨0, isWeightedHomogeneous_C _ _⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, isBlockHomogeneous_linForm _ i⟩
  obtain ⟨m, hm⟩ := hf
  refine ⟨m, fun j => ?_⟩
  have := weightedHomogeneousComponent_mem_of_mem _ _ hI (hm j) a
  rwa [mul_comm, weightedHomogeneousComponent_C_mul, ← map_weightedHomogeneousComponent,
    mul_comm] at this
end GlobalTheory.Chow
