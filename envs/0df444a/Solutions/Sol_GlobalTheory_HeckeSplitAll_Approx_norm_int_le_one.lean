-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.norm_int_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:21.885183+00:00
-- url     : https://prove2.me/submissions/dab952e9-c6e0-48a0-b184-2d17f1d71004

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_le_one_iff_int
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_int_R


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v o)
end GlobalTheory.HeckeSplitAll.Approx
