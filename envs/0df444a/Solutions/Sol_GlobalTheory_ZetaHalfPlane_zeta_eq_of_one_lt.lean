-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.zeta_eq_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:06.445859+00:00
-- url     : https://prove2.me/submissions/89b47de3-d2a3-456c-bd3b-89e37e401f97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Theorems.Thm_GlobalTheory_ZetaFractionalIntegral_zeta_eq_sub_integral_fract


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
open GlobalTheory GlobalTheory.ZetaHalfPlane
namespace GlobalTheory.ZetaHalfPlane
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by
  first
  | exact @_root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract
  | exact _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract
  | (apply _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> assumption)
  | (intros; apply _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract ..)
end GlobalTheory.ZetaHalfPlane
