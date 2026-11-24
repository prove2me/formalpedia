-- Prove2me | solution 1 for GlobalTheory.TorusOrbitLat.mulLat_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:48:20.584283+00:00
-- url     : https://prove2.me/submissions/7bb98d09-33de-403a-9ee7-946439bf60b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRho
import Theorems.Thm_GlobalTheory_TorusOrbitLat_mem_stabLat_iff
import Theorems.Thm_GlobalTheory_TorusOrbitLat_mem_mulLat_unit

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
theorem _root_.solution (u v : Aˣ) (L : Submodule O A) :
    mulLat O (u : A) L = mulLat O (v : A) L ↔ u⁻¹ * v ∈ stabLat O L := by
  rw [mem_stabLat_iff]
  constructor
  · intro h y
    calc y ∈ L ↔ (v : A) * y ∈ mulLat O (v : A) L := by rw [mem_mulLat_unit]; simp
      _ ↔ (v : A) * y ∈ mulLat O (u : A) L := by rw [h]
      _ ↔ ((u⁻¹ * v : Aˣ) : A) * y ∈ L := by rw [mem_mulLat_unit, Units.val_mul, mul_assoc]
  · intro h
    ext w
    rw [mem_mulLat_unit, mem_mulLat_unit, h (((v⁻¹ : Aˣ) : A) * w)]
    simp [mul_assoc]
end GlobalTheory.TorusOrbitLat
