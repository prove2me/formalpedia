-- Prove2me | solution 1 for GlobalTheory.EtaChar.eta_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:49:13.250856+00:00
-- url     : https://prove2.me/submissions/dde019e8-8097-41d9-823a-2c2b07ec9c01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm
import Theorems.Thm_GlobalTheory_EtaChar_eta_eq_one_iff
import Theorems.Thm_GlobalTheory_EtaChar_eta_eq_neg_one_iff
import Theorems.Thm_GlobalTheory_EtaChar_sq_iff_even

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.EtaChar
namespace GlobalTheory.EtaChar
theorem _root_.solution {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    eta x = if Even k then 1 else -1 := by
  have := sq_iff_even h0 h1 hall hk
  by_cases h : Even k
  · rw [(eta_eq_one_iff x).2 (this.2 h)]; simp [h]
  · rw [(eta_eq_neg_one_iff x).2 (fun h' => h (this.1 h'))]; simp [h]
end GlobalTheory.EtaChar
