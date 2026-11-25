-- Prove2me | solution 1 for GlobalTheory.Height.OrderTieGuards.restrict_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:52:45.00229+00:00
-- url     : https://prove2.me/submissions/f0bac434-0564-4cfe-a04f-528aedbe630c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_NotOverAndTriv
import Theorems.Thm_GlobalTheory_Height_OrderTieGuards_exists_mul

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
theorem _root_.solution (hv : IsNormDiscrete v) (ho : IsOver (K := K) v la) :
    0 < ramIdx (K := K) v la ∧
      ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = ((ramIdx (K := K) v la * vLa la a : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm, ⟨p, hp, hp0, hp1⟩, h⟩ := exists_mul hv ho
  have : ramIdx (K := K) v la = m := by
    refine IsLeast.csInf_eq ⟨⟨p, hp, hp0, ?_⟩, ?_⟩
    · rw [h _ (by exact_mod_cast hp0), hp1, mul_one]
    · rintro n ⟨a, ha, ha0, hn⟩
      have h1 := (ho a).2 ha
      rw [h _ (by exact_mod_cast ha0)] at hn h1
      have h2 : m * vLa la (a : K) = n := by exact_mod_cast hn
      have h3 : 0 < m * vLa la (a : K) := by exact_mod_cast h1
      have h4 : 0 < vLa la (a : K) := (mul_pos_iff_of_pos_left hm).1 h3
      nlinarith
  rw [this]; exact ⟨hm, h⟩
end GlobalTheory.Height.OrderTieGuards
