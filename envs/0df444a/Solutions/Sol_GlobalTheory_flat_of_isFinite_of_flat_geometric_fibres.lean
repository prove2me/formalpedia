-- Prove2me | solution 1 for GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:26.743211+00:00
-- url     : https://prove2.me/submissions/1c546c17-3a6a-4170-970b-c9de577ca842

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_flatOver_descend
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_flat_of_flatOver_fields
import Theorems.Thm_GlobalTheory_FibreFlat_flatOver_of_pullback


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
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFiniteType Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by
  intro S _ X Y f h1 h2 h3 H
  refine FiniteFibreFlat.flat_of_flatOver_fields f.left Y.hom
    (LocallyOfFiniteType.isLocallyNoetherian Y.hom) (by rwa [Over.w]) h3 fun k _ t => ?_
  exact FiniteFibreFlat.flatOver_descend
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    (FibreFlat.flatOver_of_pullback f _ (H _ _))
end GlobalTheory
