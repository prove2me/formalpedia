-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.lt_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:59.380622+00:00
-- url     : https://prove2.me/submissions/96be549a-8179-4d40-ac2d-117b53d8fc27

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_vanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}
variable [NonarchimedeanAddGroup k] [LocallyCompactSpace k]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t) {n : ℕ} (hn : n < d)
    (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ) :
    ∀ φ ∈ SB _, l φ = 0 := by
  refine vanish ξ ϖ hξ l hl fun φ _ h => ?_
  rw [show φ = 0 from funext fun X => h X ?_, map_zero]
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := X.mulVecLin) (by simpa using hn))
  exact ⟨v, h0, hv⟩
end GlobalTheory.ThK.Dbl.LD
