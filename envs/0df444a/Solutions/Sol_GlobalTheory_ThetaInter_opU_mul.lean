-- Prove2me | solution 1 for GlobalTheory.ThetaInter.opU_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:31.293032+00:00
-- url     : https://prove2.me/submissions/8544ecde-87cc-43ff-a0a2-7e6cccc8df4c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
namespace GlobalTheory.ThetaInter
theorem _root_.solution (x : V) (c : ℂ) (F : V → ℂ) (z : V) :
    opU H x (fun w => c * F w) z = c * opU H x F z := by
  simp only [opU]; ring
end GlobalTheory.ThetaInter
