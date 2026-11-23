-- Prove2me | solution 1 for GlobalTheory.DivisibleHom.comp_mulA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:21.764667+00:00
-- url     : https://prove2.me/submissions/9b4aee92-e624-42b0-a575-89e676474525

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DivisibleHom
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.DivisibleHom
namespace _root_.GlobalTheory.DivisibleHom
theorem _root_.solution {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) :
    x ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n = x ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [comp_pow, Category.comp_id]
end _root_.GlobalTheory.DivisibleHom
end GlobalTheory.DivisibleHom
