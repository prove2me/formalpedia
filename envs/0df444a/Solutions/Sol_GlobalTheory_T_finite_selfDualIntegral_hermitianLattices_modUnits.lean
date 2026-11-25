-- Prove2me | solution 1 for GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:53:13.578686+00:00
-- url     : https://prove2.me/submissions/083309d0-f449-4e4b-9d06-7048151e7a74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSelfDualIntegralHermitianLatticesModUnits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSelfDualIntegralHermitianLatticesModUnitsStatement
import Theorems.Thm_GlobalTheory_HullClasses_exists_unit_mulLat_mem_of_selfDual_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧ ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) → (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range) → ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by
  first | exact @GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice | exact GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice | (intros; apply GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice <;> assumption)
end _root_.GlobalTheory.T
