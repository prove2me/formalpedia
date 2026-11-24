-- Prove2me | solution 1 for GlobalTheory.TorusOrbitLat.isIntegral_inv_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:55.173061+00:00
-- url     : https://prove2.me/submissions/c103fc9b-3fa5-4433-9859-45428e225394

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRho
import Theorems.Thm_GlobalTheory_TorusOrbitLat_mem_intUnits_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.TorusOrbitLat
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]
namespace GlobalTheory.TorusOrbitLat
theorem _root_.solution (t u : Aˣ) (hu : u ∈ intUnits O A) (w : A) :
    IsIntegral O ((((t * u)⁻¹ : Aˣ) : A) * w) ↔ IsIntegral O (((t⁻¹ : Aˣ) : A) * w) := by
  rw [mem_intUnits_iff] at hu
  rw [mul_inv_rev, Units.val_mul, mul_assoc]
  constructor
  · intro h
    have := hu.1.mul h
    simpa using this
  · intro h
    exact hu.2.mul h
end GlobalTheory.TorusOrbitLat
