-- Prove2me | solution 1 for GlobalTheory.PlaceRestrict.exists_integral_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:16.174666+00:00
-- url     : https://prove2.me/submissions/4cd8f130-f538-40c9-ba0b-2f42354f3a33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Theorems.Thm_GlobalTheory_PlaceRestrict_exists_orders
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_exists_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_ne_zero_of_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PlaceRestrict
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace GlobalTheory.PlaceRestrict
theorem _root_.solution {Ω X : Type} [Field Ω] (S : Set X) (hS : S.Finite)
    (v : X → AddValuation Ω (WithTop ℤ)) (hinj : Set.InjOn v S)
    (hn : ∀ w ∈ S, IsNormDiscrete (v w)) (w : X) (hw : w ∈ S) (a : Ω) (ha : 0 ≤ v w a) :
    ∃ l : Ω, (∀ w' ∈ S, 0 ≤ v w' l) ∧ 0 < v w (a - l) := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, by simp, by simp [ha0]⟩
  have hm : ∀ x, ∃ m : ℤ, x ∈ S → v x a = m := fun x => by
    by_cases hx : x ∈ S
    · obtain ⟨m, hm⟩ := wa_exists_coe (v x) (hn x hx).1 ha0
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose m hm using hm
  obtain ⟨s, hs0, hs⟩ := exists_orders S hS v hinj hn
    (fun x => if x = w then 1 else min (m x) 0 - 1)
  have hsw : v w s = ((1 : ℤ) : WithTop ℤ) := by simpa using hs w hw
  have h1w : v w (1 + s) = ((0 : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_add_eq_of_lt_left _ (by
      rw [AddValuation.map_one, hsw]; exact_mod_cast (zero_lt_one : (0 : ℤ) < 1)),
      AddValuation.map_one, WithTop.coe_zero]
  have h1s : (1 + s) ≠ 0 := wa_ne_zero_of_coe _ h1w
  have hmw : 0 ≤ m w := by
    rw [hm w hw] at ha; exact_mod_cast ha
  refine ⟨a / (1 + s), fun x hx => ?_, ?_⟩
  · by_cases hxw : x = w
    · subst hxw
      rw [wa_div _ (hm x hx) h1w]
      exact_mod_cast (by omega : (0 : ℤ) ≤ m x - 0)
    · have hsx : v x s = ((min (m x) 0 - 1 : ℤ) : WithTop ℤ) := by
        have := hs x hx
        rwa [if_neg hxw] at this
      have h1x : v x (1 + s) = ((min (m x) 0 - 1 : ℤ) : WithTop ℤ) := by
        rw [AddValuation.map_add_eq_of_lt_right _ (by
          rw [AddValuation.map_one, hsx]
          exact_mod_cast (by omega : min (m x) 0 - 1 < (0 : ℤ))), hsx]
      rw [wa_div _ (hm x hx) h1x]
      exact_mod_cast (by omega : (0 : ℤ) ≤ m x - (min (m x) 0 - 1))
  · have : a - a / (1 + s) = a * s / (1 + s) := by field_simp; ring
    rw [this, wa_div _ (wa_mul _ (hm w hw) hsw) h1w]
    exact_mod_cast (by omega : (0 : ℤ) < m w + 1 - 0)
end GlobalTheory.PlaceRestrict
