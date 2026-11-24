-- Prove2me | solution 1 for GlobalTheory.T.torus_orbit_lattice_count_bounded_by_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:13.365932+00:00
-- url     : https://prove2.me/submissions/a5dbf2d7-dc1d-4b69-b4c7-c613c79ca4fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRho
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRhoStatement
import Theorems.Thm_GlobalTheory_TorusOrbitLat_orbit_count


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  first | exact @GlobalTheory.TorusOrbitLat.orbit_count | exact GlobalTheory.TorusOrbitLat.orbit_count | (intros; apply GlobalTheory.TorusOrbitLat.orbit_count <;> assumption)
end _root_.GlobalTheory.T
