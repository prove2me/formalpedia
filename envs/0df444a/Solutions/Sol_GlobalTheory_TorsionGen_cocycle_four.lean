-- Prove2me | solution 1 for GlobalTheory.TorsionGen.cocycle_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:52:45.144914+00:00
-- url     : https://prove2.me/submissions/9595aeba-b20a-4e2c-b82f-c615aa59e7c1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdCocycleMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionGen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {A U : Type} [CommGroup A] [CommGroup U]
namespace GlobalTheory.TorsionGen
theorem _root_.solution (t : A → A → U) (coc : ∀ y y' y'', t (y * y') y'' * t y y' = t y (y' * y'') * t y' y'')
    (sym : ∀ y y', t y y' = t y' y) (p q a b : A) :
    t (p * q) (a * b) * t p q * t a b = t (p * a) (q * b) * t p a * t q b := by
  have e₁ := coc p q (a * b)
  have e₂ := coc q a b
  have e₃ := coc p a (q * b)
  have e₄ := coc a q b
  rw [_root_.mul_left_comm a q b] at e₃
  rw [_root_.mul_comm a q, sym a q] at e₄
  rw [e₁, e₃, _root_.mul_assoc, _root_.mul_assoc, ← e₂, ← e₄]
end GlobalTheory.TorsionGen
