-- Prove2me | solution 1 for GlobalTheory.GrpTangent.sqZeroMap_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:43.862885+00:00
-- url     : https://prove2.me/submissions/748edfc6-6309-40f2-8764-04b570fcc562

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]
namespace GlobalTheory.GrpTangent
theorem _root_.solution {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] (l : R →ₗ[R] M) (l' : M →ₗ[R] R) :
    sqZeroMap l' ≫ sqZeroMap l = epsScale (l' (l 1)) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [epsScaleR, this]
end GlobalTheory.GrpTangent
