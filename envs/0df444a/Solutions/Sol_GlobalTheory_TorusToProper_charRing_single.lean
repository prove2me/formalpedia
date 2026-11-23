-- Prove2me | solution 1 for GlobalTheory.TorusToProper.charRing_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:20.954193+00:00
-- url     : https://prove2.me/submissions/05615e66-aaa3-44de-8efd-c32b390af2a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]
variable (K) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusToProper
theorem _root_.solution (R : Type) [CommRing R] (φ : Multiplicative X →* Rˣ) (a : X) :
    charRing X R φ (AddMonoidAlgebra.single a 1) = φ (Multiplicative.ofAdd a) := by
  simp [charRing, charAlg]
end GlobalTheory.TorusToProper
