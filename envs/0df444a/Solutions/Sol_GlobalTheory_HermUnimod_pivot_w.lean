-- Prove2me | solution 1 for GlobalTheory.HermUnimod.pivot_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:48.199879+00:00
-- url     : https://prove2.me/submissions/0f971320-e844-4bb1-ab1b-ac5341b6be8a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
import Theorems.Thm_GlobalTheory_UnitValueExistence_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
namespace GlobalTheory.HermUnimod
theorem _root_.solution {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hs : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he0 : ‖e0‖ ≤ 1) (he0' : e0 + star e0 = 1) {n : Type}
    [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E) (hG : G.IsHermitian) (hGi : Intg G)
    (hGd : ‖G.det‖ = 1) :
    ∃ i, ∃ w : n → E, (∀ a, ‖w a‖ ≤ 1) ∧ w i = 1 ∧ ‖star w ⬝ᵥ (G *ᵥ w)‖ = 1 := by
  first
  | exact @_root_.GlobalTheory.UnitValueExistence.main
  | exact _root_.GlobalTheory.UnitValueExistence.main
  | (apply _root_.GlobalTheory.UnitValueExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitValueExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitValueExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitValueExistence.main ..)
end GlobalTheory.HermUnimod
