-- Prove2me | solution 1 for GlobalTheory.ThetaSplit.exists_rational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:33:00.844595+00:00
-- url     : https://prove2.me/submissions/7dd5036b-1f34-4ae6-8725-b965d4f67c99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit
namespace GlobalTheory.ThetaSplit
theorem _root_.solution {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] {X : Scheme.{0}} (f : X ⟶ Sp k)
    [IsFinite f] (y : Sp k' ⟶ X) : ∃ c : Sp k ⟶ X, c ≫ f = 𝟙 _ ∧ (y ≫ f) ≫ c = y := by
  have hd : DiscreteTopology X := by
    have h := f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)
    have e : f ⁻¹' {IsLocalRing.closedPoint k} = Set.univ := Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
    exact isDiscrete_univ_iff.1 ((congrArg _root_.IsDiscrete e).mp h)
  have hx : IsClosed {y (IsLocalRing.closedPoint k')} := isClosed_discrete _
  refine ⟨pointOfClosedPoint f _ hx, pointOfClosedPoint_comp _ _ _, ?_⟩
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k' X y
  calc (y ≫ f) ≫ pointOfClosedPoint f _ hx
      = ((Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo y)) ≫
          X.fromSpecResidueField (y (IsLocalRing.closedPoint k'))) ≫ f) ≫ pointOfClosedPoint f _ hx := by rw [e]
    _ = Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo y)) ≫
          X.fromSpecResidueField (y (IsLocalRing.closedPoint k')) := by
        rw [Category.assoc, Category.assoc, ← Category.assoc (X.fromSpecResidueField _),
          ← SpecMap_residueFieldIsoBase_inv f _ hx, pointOfClosedPoint]
        refine congrArg (_ ≫ ·) ?_
        rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
    _ = y := e
end GlobalTheory.ThetaSplit
