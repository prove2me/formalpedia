-- Prove2me | solution 1 for GlobalTheory.HolomorphicArc.isHolTo_halfPlane_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:55:18.750857+00:00
-- url     : https://prove2.me/submissions/33810b97-0fbc-4126-8761-93abf7e9986f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHolToHalfPlaneMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
open GlobalTheory GlobalTheory.HolomorphicArc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
namespace GlobalTheory.HolomorphicArc
theorem _root_.solution {X : Scheme.{0}} {y : ℂ → (Sp ℂ ⟶ X)} {T T' : ℝ} (h : T ≤ T')
    (hol : IsHolTo {w : ℂ | T < w.im} y) : IsHolTo {w : ℂ | T' < w.im} y := by
  intro U f
  have e : {b | b ∈ {w : ℂ | T' < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} =
      {w : ℂ | T' < w.im} ∩ {b | b ∈ {w : ℂ | T < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => ⟨fun hb => ⟨hb.1, h.trans_lt hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
  rw [e]
  exact ⟨(isOpen_lt continuous_const Complex.continuous_im).inter (hol U f).1,
    (hol U f).2.mono Set.inter_subset_right⟩
end GlobalTheory.HolomorphicArc
