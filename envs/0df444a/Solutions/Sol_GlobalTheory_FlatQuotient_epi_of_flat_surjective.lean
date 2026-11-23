-- Prove2me | solution 1 for GlobalTheory.FlatQuotient.epi_of_flat_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:35.985793+00:00
-- url     : https://prove2.me/submissions/ed2f6259-6cfb-4cbf-88e5-f931303c2bff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FlatQuotient
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.FlatQuotient
namespace _root_.GlobalTheory.FlatQuotient
theorem _root_.solution {X Y : Over S} (f : X ⟶ Y) [Flat f.left] [Surjective f.left] :
    Epi f := by
  have hepi : Epi f.left := Flat.epi_of_flat_of_surjective f.left
  exact (Over.forget S).epi_of_epi_map hepi
end _root_.GlobalTheory.FlatQuotient
end GlobalTheory.FlatQuotient
