-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.jetAt0_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:09.389856+00:00
-- url     : https://prove2.me/submissions/b953975c-f90b-4360-8ec7-f3402342ee38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Theorems.Thm_GlobalTheory_CayleyCapelli_wt_eq
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.CayleyCapelli
open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing
variable {σ : Type} {C : Type} [Field C]
namespace GlobalTheory.CayleyCapelli
theorem _root_.solution (P Q : MvPolynomial σ C) :
    jetAt0 P (Q : MvPowerSeries σ C) = pair P Q := by
  rw [pair_eq, jetAt0]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_coe, wt_eq]
end GlobalTheory.CayleyCapelli
