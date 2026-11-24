-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.mem_stab_iff_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:27.10875+00:00
-- url     : https://prove2.me/submissions/96cc24a1-2447-4d83-82b3-2c25b7283cb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)
variable {F}
variable (F)
variable {F}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {g : GL (Fin n) k} : g ∈ F.stab ↔ ∀ V ∈ F.carrier, V.map g.val.mulVecLin = V := by
  constructor
  · intro hg V hV
    refine le_antisymm ?_ fun v hv => ⟨g⁻¹.val *ᵥ v, hg.2 V hV v hv, by simp [mulVec_mulVec]⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hg.1 V hV v hv
  · intro h
    refine ⟨fun V hV v hv => (h V hV).le ⟨v, hv, rfl⟩, fun V hV v hv => ?_⟩
    obtain ⟨w, hw, rfl⟩ := (h V hV).ge hv
    simpa [mulVec_mulVec] using hw
end GlobalTheory.Tw.PFlag
