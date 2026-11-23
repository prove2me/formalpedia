-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.norm_alg_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:57.909468+00:00
-- url     : https://prove2.me/submissions/0257f501-7ed5-4191-b2a0-36e4a9ff5e79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology Filter
open GlobalTheory GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeSplitAll.Approx
theorem _root_.solution (w : InfinitePlace F) (x : F) : ‖algebraMap F w.Completion x‖ = w x := by
  rw [show algebraMap F w.Completion x = (x : w.Completion) from rfl]
  simp only [InfinitePlace.Completion.norm_ofCompletion, UniformSpace.Completion.norm_coe]; rfl
end GlobalTheory.HeckeSplitAll.Approx
