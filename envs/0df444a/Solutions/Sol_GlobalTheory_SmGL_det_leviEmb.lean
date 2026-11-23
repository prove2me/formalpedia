-- Prove2me | solution 1 for GlobalTheory.SmGL.det_leviEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:20.121176+00:00
-- url     : https://prove2.me/submissions/c9107f6f-5dd4-4a78-84e8-c8851b748ece

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_det_parab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
omit [LinearOrder α]
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.leviEmb R e g) =
      ∏ a, GeneralLinearGroup.det (g a) := by
  classical
  letI : LinearOrder α := LinearOrder.lift' _ (Fintype.equivFin α).injective
  have h := _root_.GlobalTheory.SmGL.det_parab R e
    ⟨_, _root_.GlobalTheory.SmGL.leviEmb_mem_parab R e g⟩
  rwa [_root_.GlobalTheory.SmGL.leviProj_leviEmb] at h
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
