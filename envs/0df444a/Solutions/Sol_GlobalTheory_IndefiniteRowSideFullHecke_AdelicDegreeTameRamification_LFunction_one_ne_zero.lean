-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.LFunction_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:53:21.105196+00:00
-- url     : https://prove2.me/submissions/43d80158-1de5-421d-92c3-aaa08322d1c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_AdelicDegreeTameRamification
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdelicDegreeTameRamification_quadChar_ne_one

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
theorem _root_.solution (H : Host E) : (quadChar H).LFunction 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero (quadChar_ne_one H)
end GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
