-- Prove2me | solution 1 for GlobalTheory.CuspRep.expU_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:13.232922+00:00
-- url     : https://prove2.me/submissions/47034f4d-bd4a-4a85-b480-9a3dea7149c5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele
import Theorems.Thm_GlobalTheory_CuspRep_unit_ne_zero

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
theorem _root_.solution (u : (ι → ℂ)ˣ) : expU (fun i => Complex.log ((u : ι → ℂ) i)) = u :=
  Units.ext (funext fun i => Complex.exp_log (unit_ne_zero u i))
end GlobalTheory.CuspRep
