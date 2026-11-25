-- Prove2me | solution 1 for GlobalTheory.FullFlag.IsAdapted.basisMulGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:54.288897+00:00
-- url     : https://prove2.me/submissions/f746aed8-ef7e-4933-b2d5-a7f2f920c48e

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}
namespace GlobalTheory.FullFlag
namespace IsAdapted
theorem _root_.solution {F : FullFlag R M n} {b : Basis (Fin n) R M} (hb : F.IsAdapted b)
    (g : GL (Fin n) R) : F.IsAdapted (basisMulGL b g) ↔ g ∈ upperTriangularGL (Fin n) R := by
  rw [← flag_basisMulGL_eq_iff b, IsAdapted, ← hb]
end IsAdapted
end GlobalTheory.FullFlag
