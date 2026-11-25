-- Prove2me | solution 1 for GlobalTheory.norm_formPerpVector_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:35.749424+00:00
-- url     : https://prove2.me/submissions/8083d616-d586-4592-a7ea-20f2d379bf1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_seminorm_formPerpVector_le
import Theorems.Thm_GlobalTheory_norm_innerFormLeft_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {p : ℕ} (e e' : Fin p → V) (g : V) {r : ℝ} (he : ∀ a, ‖e a‖ ≤ r)
    (he' : ∀ a, ‖e' a‖ ≤ r) (hg : ‖g‖ ≤ r) :
    ‖formPerpVector (innerFormLeft V) e e' g‖ ≤ (p + 1)! * r ^ (2 * p + 1) :=
  seminorm_formPerpVector_le (normRingSeminorm ℂ) (norm_one (α := ℂ)).le
    (normAddGroupSeminorm V) (fun x v => norm_smul_le x v) (innerFormLeft V)
    norm_innerFormLeft_le e e' g he he' hg
end GlobalTheory
