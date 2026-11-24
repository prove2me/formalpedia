-- Prove2me | solution 1 for GlobalTheory.HullClasses.mulLat_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:37:14.850808+00:00
-- url     : https://prove2.me/submissions/2f17c8a4-6e3d-45ba-a009-8f2b7590b535

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
import Theorems.Thm_GlobalTheory_HullClasses_mulLat_mul

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
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (r s t : A) (L : Submodule O A)
    (h : mulLat O s L ≤ mulLat O t L) : mulLat O (r * s) L ≤ mulLat O (r * t) L := by
  rw [mulLat_mul, mulLat_mul]; exact Submodule.map_mono h
end GlobalTheory.HullClasses
