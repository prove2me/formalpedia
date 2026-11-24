-- Prove2me | solution 1 for GlobalTheory.JR.SuppBdd.isClosed_unitary_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:12:50.310864+00:00
-- url     : https://prove2.me/submissions/d41cb399-4ead-4fdc-84fd-050cff56d8a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactUnitariesIntegralOrbitOfHankelDetNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SuppBdd
namespace GlobalTheory.JR.SuppBdd
theorem _root_.solution {n : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    [StarRing E] [ContinuousStar E] :
    IsClosed ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) := by
  have : ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) =
      {U | star U * U = 1} ∩ {U | U * star U = 1} := by
    ext U; simp [Matrix.unitaryGroup, Unitary.mem_iff]
  rw [this]
  exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
    (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
end GlobalTheory.JR.SuppBdd
