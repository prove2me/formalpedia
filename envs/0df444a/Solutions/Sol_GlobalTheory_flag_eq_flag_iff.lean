-- Prove2me | solution 1 for GlobalTheory.flag_eq_flag_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:14.48075+00:00
-- url     : https://prove2.me/submissions/4d518868-cb55-4041-a426-8ce63fa2f1b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_flag_basisMulGL_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]
variable {ι R}
variable {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (b b' : Basis (Fin n) R M) :
    b'.flag = b.flag ↔ basisChange b b' ∈ upperTriangularGL (Fin n) R := by
  rw [← flag_basisMulGL_eq_iff b, basisMulGL_basisChange]
end GlobalTheory
