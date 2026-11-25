-- Prove2me | solution 1 for GlobalTheory.Height.OrderTieGuards.v_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:48:33.627779+00:00
-- url     : https://prove2.me/submissions/51055a7e-b33e-41bc-b5a8-6b4f08826de6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_NotOverAndTriv
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
theorem _root_.solution (hv : IsNormDiscrete v) {x : Ω} (hx : x ≠ 0) {m : ℤ} (hm : v x = m) (k : ℤ) :
    v (x ^ k) = ((k * m : ℤ) : WithTop ℤ) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one₀ hx, AddValuation.map_mul, ih, hm, ← WithTop.coe_add]; congr 1; ring
  | pred k ih =>
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (hv.1 _ (zpow_ne_zero (-(k : ℤ) - 1) hx))
    have e : x ^ (-(k : ℤ) - 1) * x = x ^ (-(k : ℤ)) := by rw [← zpow_add_one₀ hx]; congr 1; ring
    have h := congrArg v e
    rw [AddValuation.map_mul, ih, hm, ← hs, ← WithTop.coe_add, WithTop.coe_inj] at h
    rw [← hs, WithTop.coe_inj]; linarith
end GlobalTheory.Height.OrderTieGuards
