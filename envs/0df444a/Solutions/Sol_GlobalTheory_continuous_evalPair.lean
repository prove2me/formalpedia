-- Prove2me | solution 1 for GlobalTheory.continuous_evalPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:03.792305+00:00
-- url     : https://prove2.me/submissions/c39eaf14-c8e0-4aaa-a667-3d1c58b11848

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsConnectedPrincipalOpen
import Theorems.Thm_GlobalTheory_evalPair_C
import Theorems.Thm_GlobalTheory_evalPair_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.evalPair_C
attribute [local simp] GlobalTheory.evalPair_X

set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {d : ℕ} (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    Continuous fun z : (Fin d → ℂ) × ℂ => evalPair z r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | monomial n s =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, evalPair_C, evalPair_X]
    exact ((MvPolynomial.continuous_eval s).comp continuous_fst).mul (continuous_snd.pow n)
end GlobalTheory
