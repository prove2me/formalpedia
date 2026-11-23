-- Prove2me | solution 1 for GlobalTheory.TruncGauss.isCompact_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:31.483865+00:00
-- url     : https://prove2.me/submissions/21332a33-c83f-46bb-9894-1f826a12e116

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.TruncGauss
namespace GlobalTheory.TruncGauss
theorem _root_.solution (n : ℕ) (C : ℝ) :
    IsCompact {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 C
  have e : {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} =
      (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      closedBall (0 : ℂ) C : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    ext H
    show _ ↔ ∀ j ∈ Set.univ, ∀ l ∈ Set.univ, H j l ∈ closedBall (0 : ℂ) C
    simp [mem_closedBall, dist_zero_right]
  rw [e]; exact h
end GlobalTheory.TruncGauss
