-- Prove2me | solution 1 for GlobalTheory.CuspRep.continuous_expU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:43.312887+00:00
-- url     : https://prove2.me/submissions/83e323ed-968a-43e7-a9fc-1bed81ae2e85

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
theorem _root_.solution : Continuous (expU : (ι → ℂ) → (ι → ℂ)ˣ) :=
  Units.continuous_iff.2 ⟨continuous_pi fun i => Complex.continuous_exp.comp (continuous_apply i),
    continuous_pi fun i => Complex.continuous_exp.comp (continuous_apply i).neg⟩
end GlobalTheory.CuspRep
