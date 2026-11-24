-- Prove2me | solution 1 for GlobalTheory.TorusNil.spm_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:48:25.588801+00:00
-- url     : https://prove2.me/submissions/91c82559-379c-4525-8fc5-2a91dbfcc27c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_spm_left

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
theorem _root_.solution (φ : C →ₐ[A] D) (ψ : D →ₐ[A] E) : spm (ψ.comp φ) = spm ψ ≫ spm φ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spm_left, spm_left, spm_left]
  exact (Spec.map_comp (CommRingCat.ofHom φ.toRingHom) (CommRingCat.ofHom ψ.toRingHom))
end GlobalTheory.TorusNil
