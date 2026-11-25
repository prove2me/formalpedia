-- Prove2me | solution 1 for GlobalTheory.PointSupport.exists_algHom_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:08:23.255353+00:00
-- url     : https://prove2.me/submissions/6596d2dc-4d6a-41af-8da4-b8858db4874f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_comp
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.PointSupport
open TensorProduct
open TensorProduct
namespace GlobalTheory.PointSupport
namespace _root_.GlobalTheory.PointSupport
theorem _root_.solution (K : Type) [Field K] [IsAlgClosed K] (R : Type)
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (M : Ideal R) [M.IsMaximal] :
    ∃ χ : R →ₐ[K] K, RingHom.ker χ = M := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  let e : K ≃ₐ[K] R ⧸ M :=
    AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
end _root_.GlobalTheory.PointSupport
end GlobalTheory.PointSupport
