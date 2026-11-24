-- Prove2me | solution 1 for GlobalTheory.InverseCompactOpen.inv_exists_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:53:57.829014+00:00
-- url     : https://prove2.me/submissions/a0204617-c4af-4be1-a77c-9a4b71a2bae3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedMatrixInvariantSpaceExistsCompactOpenSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.InverseCompactOpen
namespace GlobalTheory.InverseCompactOpen
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F)
    (hU : IsOpen U) (ha : a₀ ∈ U) :
    ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := by
  have hUn : Unram F E := inferInstance
  haveI : LocallyCompactSpace F := hUn.lcF
  haveI : IsUltrametricDist F := hUn.ultraF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU a₀ ha
  have hε2 : 0 < ε / 2 := half_pos hε
  refine ⟨Metric.closedBall a₀ (ε / 2), isCompact_closedBall _ _, ?_,
    Metric.mem_closedBall_self hε2.le, ?_⟩
  · have hpi : ∀ x : Fin r → F, IsOpen (Metric.closedBall x (ε / 2)) := by
      intro x
      rw [closedBall_pi x hε2.le]
      exact isOpen_set_pi Set.finite_univ
        (fun i _ => IsUltrametricDist.isOpen_closedBall (x i) hε2.ne')
    obtain ⟨p, q, l⟩ := a₀
    rw [← closedBall_prod_same, ← closedBall_prod_same]
    exact (hpi p).prod ((hpi q).prod (IsUltrametricDist.isOpen_closedBall l hε2.ne'))
  · exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
end GlobalTheory.InverseCompactOpen
