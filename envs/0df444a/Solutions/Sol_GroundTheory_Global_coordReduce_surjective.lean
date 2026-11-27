-- Prove2me | solution 1 for GroundTheory.Global.coordReduce_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:01.171457+00:00
-- url     : https://prove2.me/submissions/ca3aded4-7ad3-405e-a171-f08c4b4b9b0d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
noncomputable section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)
namespace GroundTheory.Global
theorem _root_.solution : Function.Surjective (coordReduce W) := by
  intro y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (mapRingHom (residue 𝒪))
    (Polynomial.map_surjective (residue 𝒪) residue_surjective) p
  exact ⟨CoordinateRing.mk W q, by rw [CoordinateRing.map_mk, ← hq]⟩
end GroundTheory.Global
