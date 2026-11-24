-- Prove2me | solution 1 for GlobalTheory.TorusNil.spm_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:34:00.614189+00:00
-- url     : https://prove2.me/submissions/80b42cb4-0d9e-40da-9b1f-1fab10550f4d

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
theorem _root_.solution {φ ψ : C →ₐ[A] D} (h : spm φ = spm ψ) : φ = ψ := by
  have h1 := Spec.map_injective (congrArg CommaMorphism.left h)
  ext a
  exact congrArg (fun g : CommRingCat.of C ⟶ CommRingCat.of D => g.hom a) h1
end GlobalTheory.TorusNil
