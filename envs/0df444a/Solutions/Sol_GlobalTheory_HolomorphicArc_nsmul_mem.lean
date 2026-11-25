-- Prove2me | solution 1 for GlobalTheory.HolomorphicArc.nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:52:28.307245+00:00
-- url     : https://prove2.me/submissions/8bd348fb-bbb0-4b1a-b7da-dd4543a364d9

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
theorem _root_.solution (v : D.La) : l.M • v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  have h' : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left h
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul h' Submodule.mem_top
end GlobalTheory.HolomorphicArc
