-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.mem_map_ker_of_app_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:54:08.783396+00:00
-- url     : https://prove2.me/submissions/9b90d0c0-e79f-46b7-b9d4-5964007796b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_isPushout
import Theorems.Thm_GlobalTheory_ProperFunctions_appLE_top_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p]
    {U : X.Opens} (hU : IsAffineOpen U) (x : Γ(X, U)) (hx : g.app U x = 0) :
    x ∈ (RingHom.ker f.appTop.hom).map (p.appLE ⊤ U (le_preimage_top p U)).hom := by
  have := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (UY := g ⁻¹ᵁ U) (le_preimage_top f ⊤) (le_preimage_top p U) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top T) hU
  have h := (isIso_pushoutSection_iff ..).mp this
  rw [appLE_top_top, Scheme.Hom.appLE_eq_app] at h
  exact mem_map_ker_of_isPushout h (p.flat_appLE (isAffineOpen_top S) hU _) x hx
end GlobalTheory.ProperFunctions
