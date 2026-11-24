-- Prove2me | solution 1 for GlobalTheory.HullClasses.mulLat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:37:15.539401+00:00
-- url     : https://prove2.me/submissions/aa451d87-be7f-4b8d-883d-14305163ae9a

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
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) :
    mulLat O 1 L = L := by
  ext y; simp [mem_mulLat]
end GlobalTheory.HullClasses
