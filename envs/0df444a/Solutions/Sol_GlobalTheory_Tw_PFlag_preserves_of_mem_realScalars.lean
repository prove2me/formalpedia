-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.preserves_of_mem_realScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:11.881699+00:00
-- url     : https://prove2.me/submissions/a6e6c929-596d-4b48-8a59-d316a26490d6

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
variable {n : ℕ}
open GlobalTheory.Tw.PFlag
variable {F : PFlag n ℂ}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ F.realScalars) :
    ∀ V ∈ F.carrier, ∀ v ∈ F.summand V, X *ᵥ v ∈ F.summand V := fun V hV v hv => by
  obtain ⟨c, hc⟩ := hX V hV
  rw [hc v hv]; exact (F.summand V).smul_of_tower_mem c hv
end GlobalTheory.Tw.PFlag
