-- Prove2me | solution 1 for GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:34:32.862404+00:00
-- url     : https://prove2.me/submissions/74293d8e-74ae-4a07-a064-947af9c7c561

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetCosetsIntegralNormUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSelfDualIntegralHermitianLatticesModUnits
import Theorems.Thm_GlobalTheory_HullClasses_finite_mod_T_of
import Theorems.Thm_GlobalTheory_T_eq_mul_integralClosure_of_separable_involution_algebra
import Theorems.Thm_GlobalTheory_T_exists_finset_cosets_integral_norm_units
import Theorems.Thm_GlobalTheory_T_finite_submodules_between_mulLeftImage_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.HullClasses
namespace GlobalTheory.HullClasses
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x →
    ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S :=
  fun K B hsep x _ _ c hc0 =>
    finite_mod_T_of K B (GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra K B hsep) (GlobalTheory.T.exists_finset_cosets_integral_norm_units K B hsep) (GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B) x c hc0
end GlobalTheory.HullClasses
