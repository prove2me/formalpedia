-- Prove2me | solution 1 for GlobalTheory.CuspRep.expU_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:15.685941+00:00
-- url     : https://prove2.me/submissions/c6cb8934-7b05-4304-8bed-0e30047e991d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CuspRep
variable {ι : Type} [Fintype ι]
omit [Fintype ι]
namespace GlobalTheory.CuspRep
theorem _root_.solution : expU (0 : ι → ℂ) = 1 := Units.ext (funext fun _ => Complex.exp_zero)
end GlobalTheory.CuspRep
