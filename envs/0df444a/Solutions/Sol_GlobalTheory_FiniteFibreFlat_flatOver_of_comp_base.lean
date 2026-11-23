-- Prove2me | solution 1 for GlobalTheory.FiniteFibreFlat.flatOver_of_comp_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:19.551012+00:00
-- url     : https://prove2.me/submissions/7f361270-681c-4f3a-8b83-f7c7c41139c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres

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
open GlobalTheory
open GlobalTheory.FiniteFibreFlat
open TensorProduct IsLocalRing
open FibreFlat
variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y}
namespace GlobalTheory.FiniteFibreFlat
theorem _root_.solution {S₀ : Scheme.{0}} {g : Y ⟶ S₀} {u : S₀ ⟶ S} {t : S' ⟶ S₀}
    (H : FlatOver f (g ≫ u) (t ≫ u)) : FlatOver f g t :=
  fun _ _ a b j h sq e => H a b j h sq (by rw [← Category.assoc, e, Category.assoc])
end GlobalTheory.FiniteFibreFlat
