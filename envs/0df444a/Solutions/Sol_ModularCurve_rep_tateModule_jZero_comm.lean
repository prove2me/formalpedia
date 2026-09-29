-- Prove2me | solution 1 for ModularCurve.rep_tateModule_jZero_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3c24a468-2801-5f40-8dec-991503b0d1c9

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_rep_tateModule_jZero_comm

set_option autoImplicit false

open ModularCurve

theorem solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (T : ModularCurve.HeckeAlg)
    (x : TateModule p (ModularCurve.JZero N)) :
    letI := ModularCurve.heckeModuleBar N
    TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (TateModule.rep p (ModularCurve.JZero N) ModularCurve.HeckeAlg T x)
      = TateModule.rep p (ModularCurve.JZero N) ModularCurve.HeckeAlg T
        (TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by
  letI := ModularCurve.heckeModuleBar N
  haveI := ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar N hcomm
  refine Subtype.ext (funext fun n => ?_)
  simp only [TateModule.rep_apply]
  exact smul_comm σ T ((x : ℕ → JZero N) n)

end S_ModularCurve_rep_tateModule_jZero_comm
end P2MW
export P2MW.S_ModularCurve_rep_tateModule_jZero_comm (solution)
