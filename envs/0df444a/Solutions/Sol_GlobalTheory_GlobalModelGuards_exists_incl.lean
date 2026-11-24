-- Prove2me | solution 1 for GlobalTheory.GlobalModelGuards.exists_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:02.034879+00:00
-- url     : https://prove2.me/submissions/8e0df2ea-a897-4c89-8b17-ada48f5873fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.GlobalModelGuards
theorem _root_.solution {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃! b : 𝓞 c.F →+* c.V W, ∀ x, ((b x : c.V W) : c.F) = (x : c.F) := by
  have hm : ∀ x : 𝓞 c.F, algebraMap (𝓞 c.F) c.F x ∈ c.V W := by
    intro x
    have hi : IsIntegral (c.V W) (x : c.F) := (RingOfIntegers.isIntegral_coe x).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    have : (y : c.F) = x := hy
    change (x : c.F) ∈ c.V W
    rw [← this]; exact y.2
  refine ⟨(algebraMap (𝓞 c.F) c.F).codRestrict (c.V W).toSubring hm, fun x => rfl, fun b hb => ?_⟩
  ext x
  exact congrArg _ (hb x)
end GlobalTheory.GlobalModelGuards
