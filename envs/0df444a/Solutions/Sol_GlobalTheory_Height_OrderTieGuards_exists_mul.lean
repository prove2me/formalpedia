-- Prove2me | solution 1 for GlobalTheory.Height.OrderTieGuards.exists_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:44.029804+00:00
-- url     : https://prove2.me/submissions/78dec23d-5bd6-4078-a134-c8039b919c3c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_NotOverAndTriv
import Theorems.Thm_GlobalTheory_Height_OrderTieGuards_zero_of_unit
import Theorems.Thm_GlobalTheory_Height_OrderTieGuards_v_zpow

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
    ∃ m : ℤ, 0 < m ∧ (∃ p ∈ la.asIdeal, p ≠ 0 ∧ vLa la (p : K) = 1) ∧
      ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = ((m * vLa la a : ℤ) : WithTop ℤ) := by
  obtain ⟨p, hp⟩ := la.intValuation_exists_uniformizer
  have hpK : la.valuation K (p : K) = WithZero.exp (-1 : ℤ) := by
    rw [← hp]; exact HeightOneSpectrum.valuation_of_algebraMap la p
  have hp0 : (p : K) ≠ 0 := by
    intro h; rw [h, map_zero] at hpK; exact WithZero.exp_ne_zero hpK.symm
  have hpm : p ∈ la.asIdeal := by
    rw [← la.intValuation_lt_one_iff_mem, hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hx : algebraMap K Ω (p : K) ≠ 0 := (map_ne_zero _).2 hp0
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hv.1 _ hx)
  have hm0 : 0 < m := by
    have := (ho p).2 hpm
    rw [← hm] at this; exact_mod_cast this
  refine ⟨m, hm0, ⟨p, hpm, fun h => hp0 (by simp [h]), by simp [vLa, hpK]⟩, fun a ha => ?_⟩
  have hva : la.valuation K a ≠ 0 := by simpa using ha
  have hu : la.valuation K (a / (p : K) ^ vLa la a) = 1 := by
    rw [map_div₀, map_zpow₀, hpK, ← WithZero.exp_zsmul, div_eq_one_iff_eq WithZero.exp_ne_zero]
    simp [vLa, WithZero.exp_log hva]
  have e : algebraMap K Ω a = algebraMap K Ω (a / (p : K) ^ vLa la a) * algebraMap K Ω (p : K) ^ vLa la a := by
    rw [← map_zpow₀ (algebraMap K Ω), ← map_mul, div_mul_cancel₀ _ (zpow_ne_zero _ hp0)]
  rw [congrArg v e, AddValuation.map_mul, zero_of_unit ho hu, zero_add, v_zpow hv hx hm.symm, mul_comm]
end GlobalTheory.Height.OrderTieGuards
