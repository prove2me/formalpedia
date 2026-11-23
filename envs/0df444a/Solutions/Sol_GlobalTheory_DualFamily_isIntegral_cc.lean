-- Prove2me | solution 1 for GlobalTheory.DualFamily.isIntegral_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:21.09853+00:00
-- url     : https://prove2.me/submissions/794ac4c6-494c-4c6c-87e5-720ff588716b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.DualFamily
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.DualFamily
namespace _root_.GlobalTheory.DualFamily
theorem _root_.solution {a : E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact ha.map (RingHom.toIntAlgHom (IsCMField.complexConj E).toRingEquiv.toRingHom)
end _root_.GlobalTheory.DualFamily
end GlobalTheory.DualFamily
