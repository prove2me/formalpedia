-- Prove2me | solution 1 for GlobalTheory.TorusNil.spm_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:07.182098+00:00
-- url     : https://prove2.me/submissions/f16d3d91-6d9d-4941-a002-b812798b177a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent

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
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable {C D E : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
  [CommRing E] [Algebra A E]
namespace GlobalTheory.TorusNil
theorem _root_.solution (φ : C →ₐ[A] D) : (spm φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl
end GlobalTheory.TorusNil
