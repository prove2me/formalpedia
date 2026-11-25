-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowWt_eq_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:14.25873+00:00
-- url     : https://prove2.me/submissions/0b219e13-b41d-49d1-87e6-7fa731946cdf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_rowOp_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {h : Poly n} {c : Fin n → ℂ} (hc : ∀ a, rowOp a a h = c a • h)
    {m : Fin n × Fin n →₀ ℕ} (hm : m ∈ h.support) (a : Fin n) : (rowWt m a : ℂ) = c a := by
  have := congrArg (coeff m) (hc a)
  rw [coeff_rowOp_self, coeff_smul, smul_eq_mul] at this
  exact mul_right_cancel₀ (MvPolynomial.mem_support_iff.1 hm) this
end GroundTheory.Automorphic.HarishChandra
