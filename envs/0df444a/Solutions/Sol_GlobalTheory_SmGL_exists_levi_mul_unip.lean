-- Prove2me | solution 1 for GlobalTheory.SmGL.exists_levi_mul_unip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:54.935238+00:00
-- url     : https://prove2.me/submissions/ec80f664-669d-4cb4-879d-68bd73d2db83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_coe_mem_unipRad

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
variable {R}
variable (R)
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution (e : (Σ a, m a) ≃ n)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    ∃ u ∈ _root_.GlobalTheory.SmGL.unipRad R e,
      (p : GL n R) = _root_.GlobalTheory.SmGL.leviEmb R e (_root_.GlobalTheory.SmGL.leviProj R e p) * u := by
  let L : _root_.GlobalTheory.SmGL.parab R e :=
    ⟨_root_.GlobalTheory.SmGL.leviEmb R e (_root_.GlobalTheory.SmGL.leviProj R e p),
      _root_.GlobalTheory.SmGL.leviEmb_mem_parab R e _⟩
  refine ⟨((L⁻¹ * p : _root_.GlobalTheory.SmGL.parab R e) : GL n R),
    (_root_.GlobalTheory.SmGL.coe_mem_unipRad R _).2 ?_, ?_⟩
  · rw [map_mul, map_inv, _root_.GlobalTheory.SmGL.leviProj_leviEmb, inv_mul_cancel]
  · rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mul_inv_cancel_left _ _).symm
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
