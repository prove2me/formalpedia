-- Prove2me | solution 1 for GlobalTheory.TorusNil.torus_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:42.216154+00:00
-- url     : https://prove2.me/submissions/51f67685-68aa-4404-85df-2a0e278076d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_torusPt_mul
import Theorems.Thm_GlobalTheory_TorusNil_spm_torusPt

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
variable (A) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusNil
theorem _root_.solution :
    (spm (dm A X (AddMonoidHom.inl X X)) ≫ torusPt A X (AddMonoidAlgebra.of A X)) *
      (spm (dm A X (AddMonoidHom.inr X X)) ≫ torusPt A X (AddMonoidAlgebra.of A X)) =
    spm (dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X))) ≫
      torusPt A X (AddMonoidAlgebra.of A X) := by
  rw [spm_torusPt, spm_torusPt, spm_torusPt, ← torusPt_mul]
  congr 1
  ext x
  simp [AddMonoidAlgebra.single_mul_single]
end GlobalTheory.TorusNil
