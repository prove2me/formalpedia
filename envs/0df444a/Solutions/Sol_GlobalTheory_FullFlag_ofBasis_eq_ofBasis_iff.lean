-- Prove2me | solution 1 for GlobalTheory.FullFlag.ofBasis_eq_ofBasis_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:02.245514+00:00
-- url     : https://prove2.me/submissions/1dcf09d0-3f72-43f5-9ae8-194e43e0eeed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_flag_eq_flag_iff

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
theorem _root_.solution (b b' : Basis (Fin n) R M) :
    ofBasis b' = ofBasis b ↔ ∃ g ∈ upperTriangularGL (Fin n) R, basisMulGL b g = b' := by
  rw [FullFlag.ext_iff, ofBasis_sub, ofBasis_sub, flag_eq_flag_iff]
  refine ⟨fun h => ⟨_, h, basisMulGL_basisChange b b'⟩, ?_⟩
  rintro ⟨g, hg, rfl⟩
  simpa using hg
end GlobalTheory.FullFlag
