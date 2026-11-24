-- Prove2me | solution 1 for GlobalTheory.ThetaInter.opU_opU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:44:58.193166+00:00
-- url     : https://prove2.me/submissions/3d3f01ce-38c8-4054-9dac-93554d35b4fc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_sub_swap

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
theorem _root_.solution (hH : IsHerm H) (x y : V) (F : V → ℂ) (z : V) :
    opU H x (opU H y F) z = cexp (-(Real.pi * I * (altE H x y : ℂ))) * opU H (x + y) F z := by
  simp only [opU, add_assoc, map_add, LinearMap.add_apply]
  rw [mul_assoc, mul_left_comm _ (F _), ← Complex.exp_add, ← Complex.exp_add, sub_swap hH x y]
  congr 2
  ring
end GlobalTheory.ThetaInter
