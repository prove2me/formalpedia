-- Prove2me | solution 1 for GlobalTheory.HullClasses.isLat_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:25.069968+00:00
-- url     : https://prove2.me/submissions/0b2f6f8f-1394-4c45-ac0c-9353ff9f1471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat

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
theorem _root_.solution (u : B.Aˣ) {L : Submodule K.O B.A} (hL : IsLat K.O K.E L) :
    IsLat K.O K.E (mulLat K.O (u : B.A) L) := by
  refine ⟨hL.1.map _, ?_⟩
  have : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) =
      (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A) := by
    ext y; simp [mulLat]
  rw [this, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y; exact ⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp⟩
end GlobalTheory.HullClasses
