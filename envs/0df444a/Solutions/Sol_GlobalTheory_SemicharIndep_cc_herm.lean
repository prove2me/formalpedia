-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.cc_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:42:50.168063+00:00
-- url     : https://prove2.me/submissions/658fc83f-89aa-4f8f-b14b-5cd318401f7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_cc
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.SemicharIndep
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.SemicharIndep
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → E) :
    cc (herm G u v) = herm G v u := by
  have h : cc (herm G u v) = ∑ a, ∑ b, cc (u a * G a b * cc (v b)) := by
    simp only [herm, cc, map_sum]
  rw [h, herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cc_mul, cc_mul, cc_cc, hG]; ring
end GlobalTheory.SemicharIndep
