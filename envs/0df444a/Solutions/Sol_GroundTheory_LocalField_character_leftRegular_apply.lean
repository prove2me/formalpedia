-- Prove2me | solution 1 for GroundTheory.LocalField.character_leftRegular_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:55.806366+00:00
-- url     : https://prove2.me/submissions/190c056b-5c96-4223-a30c-36f02c3d227c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters

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
open Module Representation
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution [DecidableEq G] (g : G) :
    (Representation.leftRegular ℂ G).character g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  rw [Representation.character, Representation.ofMulAction_def]
  have : ((MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
      Finsupp.lmapDomain ℂ ℂ (g • · : G → G) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) =
      (MonoidAlgebra.coeffLinearEquiv (R := ℂ) (S := ℂ) (M := G)).symm.conj
        (Finsupp.lmapDomain ℂ ℂ (g • · : G → G)) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [this, LinearMap.trace_conj', LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basisSingleOne),
    Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
    Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.single_apply, smul_eq_mul, mul_eq_right]
  split_ifs with hg
  · simp
  · simp
end GroundTheory.LocalField
