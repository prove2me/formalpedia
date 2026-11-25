-- Prove2me | solution 1 for GlobalTheory.LieChart.exists_isStandardSmooth_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:11:26.384133+00:00
-- url     : https://prove2.me/submissions/b65b6c55-252f-4125-bdba-f91098780b13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieChart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
namespace GlobalTheory.LieChart
theorem _root_.solution {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
    (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V) (e : V ≤ p ⁻¹ᵁ U),
      x ∈ U ∧ U ≤ W ∧ U ≤ s ⁻¹ᵁ V ∧ (p.appLE U V e).hom.IsStandardSmooth := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth p (s x)
  have hps : ∀ y : X, p (s y) = y := fun y => by rw [← Scheme.Hom.comp_apply, hs]; rfl
  have hxU : x ∈ U := by have := e hxV; rwa [← hps x]
  obtain ⟨r, hr, hxr⟩ := hU.exists_basicOpen_le (V := W ⊓ s ⁻¹ᵁ V) ⟨x, hx, hxV⟩ hxU
  have := hV.isLocalization_basicOpen (p.appLE U V e r)
  have := hU.isLocalization_basicOpen r
  refine ⟨X.basicOpen r, hU.basicOpen r, Y.basicOpen (p.appLE U V e r), hV.basicOpen _, by simp [Scheme.Hom.appLE],
    hxr, hr.trans inf_le_left, fun y hy => ?_, ?_⟩
  · have h1 : s y ∈ V := (hr hy).2
    have h2 : s y ∈ p ⁻¹ᵁ X.basicOpen r := by
      show p (s y) ∈ X.basicOpen r
      rwa [hps]
    show s y ∈ Y.basicOpen (p.appLE U V e r)
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen] using And.intro h1 h2
  · rw [hU.appLE_eq_away_map p hV]
    exact RingHom.isStandardSmooth_localizationPreserves.away _ _ _ _ h
end GlobalTheory.LieChart
