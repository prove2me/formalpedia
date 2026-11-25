-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.quadChar_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:25.135739+00:00
-- url     : https://prove2.me/submissions/139ad761-e97c-422e-8765-ea434c0656dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_AdelicDegreeTameRamification

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
theorem _root_.solution (H : Host E) : quadChar H ≠ 1 := by
  have h2 : ringChar (ZMod H.d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; have := H.d_mod; omega
  intro h
  apply quadraticChar_ne_one h2
  refine MulChar.injective_ringHomComp (f := Int.castRingHom ℂ) Int.cast_injective ?_
  simpa [quadChar, MulChar.ringHomComp_one] using h
end GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
