-- Prove2me | solution 1 for GlobalTheory.TorusOrbitLat.mem_mulLat_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:00.266267+00:00
-- url     : https://prove2.me/submissions/f21ae7f6-4847-4b99-afc5-ff6d1ad0cb9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRho

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
theorem _root_.solution (u : Aˣ) (L : Submodule O A) (w : A) :
    w ∈ mulLat O (u : A) L ↔ ((u⁻¹ : Aˣ) : A) * w ∈ L := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩
end GlobalTheory.TorusOrbitLat
