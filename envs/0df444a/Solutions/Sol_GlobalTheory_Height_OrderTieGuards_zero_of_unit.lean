-- Prove2me | solution 1 for GlobalTheory.Height.OrderTieGuards.zero_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:57:41.382858+00:00
-- url     : https://prove2.me/submissions/39a2daa1-257a-4784-a0a3-890c7455881d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_NotOverAndTriv
import Theorems.Thm_GlobalTheory_Height_OrderTieGuards_zero_of_notMem

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
theorem _root_.solution (ho : IsOver (K := K) v la) {u : K} (hu : la.valuation K u = 1) :
    v (algebraMap K Ω u) = 0 := by
  obtain ⟨n, d, hnd⟩ := la.exists_primeCompl_mul_eq_of_integer u hu.le
  have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
  have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← hnd, map_mul, hu, hd, one_mul]
  have h1 := zero_of_notMem ho ((la.valuation_eq_one_iff_notMem).1 hn)
  have h2 := zero_of_notMem ho (a := d) d.2
  have h3 : algebraMap K Ω u * algebraMap K Ω ((d : 𝓞 K) : K) = algebraMap K Ω ((n : 𝓞 K) : K) := by
    rw [← map_mul]; exact congrArg _ hnd
  have h4 := congrArg v h3
  rwa [AddValuation.map_mul, h1, h2, add_zero] at h4
end GlobalTheory.Height.OrderTieGuards
