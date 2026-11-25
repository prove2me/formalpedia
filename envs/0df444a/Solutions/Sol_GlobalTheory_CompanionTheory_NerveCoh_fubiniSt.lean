-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.fubiniSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:23.58852+00:00
-- url     : https://prove2.me/submissions/d34de4d0-6ba8-4b4c-9d68-03fd49e6a5ef

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_qiso_of_cone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
open MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.NerveCoh
theorem _root_.solution : CxSt → FubiniSt := by
  intro _ R _ C _ F D _ _ _ G m h
  have hτ : ∀ T j, ((trOf m).aug T).Ex j := by
    intro T j
    obtain ⟨h1, h2, h3⟩ := h T
    match j with
    | 0 => exact h1
    | 1 => exact h2
    | k + 2 => exact h3 k
  obtain ⟨q1, q2, q3, q4⟩ := qiso_of_cone (trOf m).pull fun k ↦ cone_ex k (trOf m) hτ
  refine ⟨⟨fun x hx hy ↦ ?_, fun z hz ↦ ?_⟩, fun n ↦ ⟨fun x hx hy ↦ ?_, fun z hz ↦ ?_⟩⟩
  · obtain ⟨y, hy⟩ := hy
    exact ⟨0, by
      rw [LinearMap.zero_apply]
      exact (q1 x hx hy.symm).symm⟩
  · obtain ⟨x, h1, h2⟩ := q2 z hz
    exact ⟨x, 0, h1, (sub_eq_zero.2 h2)⟩
  · obtain ⟨y, hy⟩ := hy
    exact q3 n x hx y hy
  · exact q4 n z hz
end GlobalTheory.CompanionTheory.NerveCoh
