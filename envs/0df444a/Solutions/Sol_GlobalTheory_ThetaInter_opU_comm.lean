-- Prove2me | solution 1 for GlobalTheory.ThetaInter.opU_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:58:08.921856+00:00
-- url     : https://prove2.me/submissions/3b4a6aae-acf5-4aa7-aa31-ed36f7264efb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_altE_swap
import Theorems.Thm_GlobalTheory_ThetaInter_opU_opU

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
    opU H x (opU H y F) z = chi H x y * opU H y (opU H x F) z := by
  rw [opU_opU hH, opU_opU hH, altE_swap hH x y, chi, ← mul_assoc, ← Complex.exp_add, add_comm y x]
  congr 2
  push_cast
  ring
end GlobalTheory.ThetaInter
