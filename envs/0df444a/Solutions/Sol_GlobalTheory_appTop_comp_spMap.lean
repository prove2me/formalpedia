-- Prove2me | solution 1 for GlobalTheory.appTop_comp_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:47.381249+00:00
-- url     : https://prove2.me/submissions/49928bb9-9db9-407a-82d9-e138a839c49f

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
theorem _root_.solution {T : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (f : T ⟶ Sp A') (x : A) :
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (f ≫ spMap φ).appTop).hom x =
      ((Scheme.ΓSpecIso (.of A')).inv ≫ f.appTop).hom (φ x) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl
end GlobalTheory
