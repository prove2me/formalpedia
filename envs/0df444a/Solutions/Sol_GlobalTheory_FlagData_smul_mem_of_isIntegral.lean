-- Prove2me | solution 1 for GlobalTheory.FlagData.smul_mem_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:04.699023+00:00
-- url     : https://prove2.me/submissions/ae74b1c9-fa51-4e49-bc5a-4671ada90891

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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.FlagData
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin r → E)) {c : E} (hc : IsIntegral ℤ c)
    {v : Fin r → E} (hv : v ∈ Λ) : c • v ∈ Λ :=
  Λ.smul_mem (⟨c, hc⟩ : 𝓞 E) hv
end GlobalTheory.FlagData
