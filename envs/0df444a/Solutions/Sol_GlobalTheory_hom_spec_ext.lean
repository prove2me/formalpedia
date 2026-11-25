-- Prove2me | solution 1 for GlobalTheory.hom_spec_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:17:24.02202+00:00
-- url     : https://prove2.me/submissions/3cfb888d-e2f1-4eb7-8baf-c88a17ad5fd3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
variable {B : Scheme.{0}} (pB : B ⟶ Sp k)
namespace GlobalTheory
theorem _root_.solution {T : Scheme.{0}} {A : CommRingCat.{0}} {f g : T ⟶ Spec A}
    (h : (Scheme.ΓSpecIso A).inv ≫ f.appTop = (Scheme.ΓSpecIso A).inv ≫ g.appTop) : f = g :=
  ext_of_isAffine ((cancel_epi _).1 h)
end GlobalTheory
