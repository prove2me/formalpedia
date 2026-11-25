-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.wQ_mul_qTriv_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:09.250701+00:00
-- url     : https://prove2.me/submissions/3cb2a54f-7436-4575-8126-60469398fc10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Theorems.Thm_GlobalTheory_Ex_NumD_tk_qTriv_right
import Theorems.Thm_GlobalTheory_Ex_NumD_tk_qTriv_left
import Theorems.Thm_GlobalTheory_Ex_NumD_wQ_qTriv_odd
import Theorems.Thm_GlobalTheory_T_wQ_characterization_and_mul_relation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {k : ℕ} (hk : Odd k) (p : N.QT k) (z : N.X) :
    N.wQ (p * N.qTriv k z) = N.wQ p * N.ψ z ^ k * p.1.2.s z ^ k := by
  have h := (GlobalTheory.T.wQ_characterization_and_mul_relation O N k hk p (N.qTriv k z)).2.1
  rw [wp, tk_qTriv_right, tk_qTriv_left, div_self', one_pow, one_mul, N.wQ_qTriv_odd hk] at h
  exact h.symm
end GlobalTheory.Ex.NumD
