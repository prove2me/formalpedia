-- Prove2me | solution 1 for GlobalTheory.Height.OrderTieGuards.zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:46.731684+00:00
-- url     : https://prove2.me/submissions/db5360f4-bd6c-422d-88a9-89bf819fba44

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_NotOverAndTriv
import Theorems.Thm_GlobalTheory_Height_OrderTieGuards_nonneg_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Height GlobalTheory.Height.OrderTieGuards
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)}
namespace GlobalTheory.Height.OrderTieGuards
theorem _root_.solution (ho : IsOver (K := K) v la) {a : 𝓞 K} (ha : a ∉ la.asIdeal) :
    v (algebraMap K Ω (a : K)) = 0 :=
  le_antisymm (not_lt.1 fun h => ha ((ho a).1 h)) (nonneg_int v a)
end GlobalTheory.Height.OrderTieGuards
