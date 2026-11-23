-- Prove2me | solution 1 for GlobalTheory.CubeFrame.isOpen_cubeChart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:39.86947+00:00
-- url     : https://prove2.me/submissions/0abc0f36-5298-42dc-af29-b55d5cfc7bb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}
omit [NormedSpace ℂ E] [FiniteDimensional ℂ E]
namespace GlobalTheory.CubeFrame
theorem _root_.solution {X : Type*} [TopologicalSpace X] {p : X → Fin 3 → E}
    (hp : Continuous p) {V : Finset (Fin 3) → Set E} (hV : ∀ I, IsOpen (V I)) :
    IsOpen {y | ∀ I : Finset (Fin 3), ∑ a ∈ I, p y a ∈ V I} := by
  rw [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun I => (hV I).preimage (by fun_prop)
end GlobalTheory.CubeFrame
