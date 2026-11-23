-- Prove2me | solution 1 for GlobalTheory.HullClasses.mulLat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:06.546093+00:00
-- url     : https://prove2.me/submissions/d35e4ad0-57c9-45e4-ab3c-753bcda91f8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
import Theorems.Thm_GlobalTheory_HullClasses_mem_mulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.HullClasses
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (s t : A) (L : Submodule O A) :
    mulLat O (s * t) L = mulLat O s (mulLat O t L) := by
  ext y; simp only [mem_mulLat]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨t * z, ⟨z, hz, rfl⟩, by ring⟩
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, by ring⟩
end GlobalTheory.HullClasses
