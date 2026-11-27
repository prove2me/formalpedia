-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.mem_lieQ_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:56.255484+00:00
-- url     : https://prove2.me/submissions/c969fe9a-1d0b-4633-a6f8-cd493c22bc3b

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
theorem _root_.solution {V : Submodule k (Fin n → k)} {X : Matrix (Fin n) (Fin n) k} :
    X ∈ (single V).lieQ ↔ ∀ v ∈ V, X *ᵥ v ∈ V := by
  refine ⟨fun h => h V (by simp [single]), fun h V' hV' v hv => ?_⟩
  rcases hV' with rfl | rfl | rfl
  · rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  · exact h v hv
  · trivial
end GlobalTheory.Tw.PFlag
