-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_algOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:42.650735+00:00
-- url     : https://prove2.me/submissions/b5923bc2-5cd6-4117-9178-db82b13c6349

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]
variable (O : LAlg R₀) {A : Type} [CommRing A] [Algebra (O : Type) A] [Algebra R₀ A]
  [IsScalarTower R₀ (O : Type) A]
namespace GlobalTheory.FinOf
theorem _root_.solution [Module.Finite (O : Type) A] (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    algOf (finOf_sO O I) = (inferInstance : Algebra (O : Type) (A ⧸ I)) :=
  Algebra.algebra_ext _ _ fun _ => rfl
end GlobalTheory.FinOf
