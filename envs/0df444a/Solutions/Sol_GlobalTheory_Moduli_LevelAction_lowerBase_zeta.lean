-- Prove2me | solution 1 for GlobalTheory.Moduli.LevelAction.lowerBase_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:18:49.050443+00:00
-- url     : https://prove2.me/submissions/75dbfa69-6eb4-491d-a8ae-5169b0af40c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_zeta_pow_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.Moduli GlobalTheory.Moduli.LevelAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.Moduli.LevelAction
theorem _root_.solution {l l₂ : Level H} (jK : KA l →+* KA l₂) (hl : l.A ∣ l₂.A)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) :
    (lowerBase jK).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  apply Subtype.ext
  have h₁ : (((lowerBase jK).ζ : KA l₂) : ℂ) = zeta l.A := hj (baseKA l).ζ
  have h₂ : (((baseKA l₂).ζ : KA l₂) : ℂ) = zeta l₂.A := rfl
  rw [h₁, SubmonoidClass.coe_pow, h₂, zeta_pow_div l₂.A_pos hl]
end GlobalTheory.Moduli.LevelAction
