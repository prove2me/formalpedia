-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TorusAction.isLat_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:17.396775+00:00
-- url     : https://prove2.me/submissions/1921572c-aae2-4ceb-a0db-53fa67b4dd5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusSubmoduleMulLeftImageMemSelfDualStableLatti

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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TorusAction
open InvAlg
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.TorusAction
theorem _root_.solution (u : B.Aˣ) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L) :
    IsLat K.O K.E (mulLat K.O (u : B.A) L) := by
  refine ⟨hL.1.map _, ?_⟩
  have hc : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) =
      (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A) := by
    unfold mulLat; rw [Submodule.map_coe]; rfl
  rw [hc, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp [← mul_assoc]⟩
end GlobalTheory.UnitLemma.TorusAction
