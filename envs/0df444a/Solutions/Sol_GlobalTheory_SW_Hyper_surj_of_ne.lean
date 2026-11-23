-- Prove2me | solution 1 for GlobalTheory.SW.Hyper.surj_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:32.802326+00:00
-- url     : https://prove2.me/submissions/49025a3c-ac45-4531-b361-8d6c687f943c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Hyper
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
namespace GlobalTheory.SW.Hyper
theorem _root_.solution (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    ∃ v, f v = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext fun x => by simpa using h x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hw
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨c • w, ?_⟩
  rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm, hb]
end GlobalTheory.SW.Hyper
