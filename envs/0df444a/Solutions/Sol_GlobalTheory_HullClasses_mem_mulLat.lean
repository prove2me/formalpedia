-- Prove2me | solution 1 for GlobalTheory.HullClasses.mem_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:38.655187+00:00
-- url     : https://prove2.me/submissions/41d44784-5f92-450b-8caa-c49d434de40d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat

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
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t y : A) (L : Submodule O A) :
    y ∈ mulLat O t L ↔ ∃ z ∈ L, t * z = y := by
  simp [mulLat]
end GlobalTheory.HullClasses
