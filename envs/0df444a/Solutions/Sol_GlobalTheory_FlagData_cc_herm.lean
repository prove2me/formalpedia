-- Prove2me | solution 1 for GlobalTheory.FlagData.cc_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:11:21.812899+00:00
-- url     : https://prove2.me/submissions/d94fa85e-2421-47e2-88c1-a0ae09bc7e01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmulMemOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FlagData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlagData
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (x y : Fin r → E) : FD.cc (FD.herm G x y) = FD.herm G y x := by
  have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG
  simp only [FD.herm, FD.cc, map_sum, map_mul, hG', IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.FlagData
