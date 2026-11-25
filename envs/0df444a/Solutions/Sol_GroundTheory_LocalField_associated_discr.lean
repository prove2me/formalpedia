-- Prove2me | solution 1 for GroundTheory.LocalField.associated_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:55.720078+00:00
-- url     : https://prove2.me/submissions/a77a81ad-0f1a-448c-8806-e90db2f0ea7a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance high] FaithfulSMul.to_isTorsionFree
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B] [Algebra A B]
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b : Module.Basis ι A B) (b' : Module.Basis ι' A B) :
    Associated (Algebra.discr A b') (Algebra.discr A b) := by
  let e : ι ≃ ι' := b.indexEquiv b'
  let b'' := b'.reindex e.symm
  have h1 : Algebra.discr A b'' = Algebra.discr A b' := by
    have := Algebra.discr_reindex A b' e.symm
    rwa [Module.Basis.coe_reindex]
  have h2 : Algebra.discr A b = (b''.toMatrix b).det ^ 2 * Algebra.discr A b'' := by
    convert Algebra.discr_of_matrix_vecMul b'' (b''.toMatrix b)
    rw [Module.Basis.toMatrix_map_vecMul]
  have hdet : IsUnit (b''.toMatrix b).det := by
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b'']
    exact LinearEquiv.isUnit_det (LinearEquiv.refl A B) b b''
  refine ⟨(hdet.pow 2).unit, ?_⟩
  rw [IsUnit.unit_spec, h2, h1, mul_comm]
end GroundTheory.LocalField
