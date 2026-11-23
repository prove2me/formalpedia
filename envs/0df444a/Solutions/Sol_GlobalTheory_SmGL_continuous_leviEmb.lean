-- Prove2me | solution 1 for GlobalTheory.SmGL.continuous_leviEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:35.794201+00:00
-- url     : https://prove2.me/submissions/b596a49d-ead0-424e-acb2-25126413d6f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower

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
open Classical
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution [TopologicalSpace R] {α : Type} {m : α → Type}
    [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) :
    Continuous (_root_.GlobalTheory.SmGL.leviEmb R e) := by
  have hval : Continuous fun g : _root_.GlobalTheory.SmGL.Levi R m =>
      ((_root_.GlobalTheory.SmGL.leviEmb R e g : GL n R) : Matrix n n R) := by
    show Continuous fun g : _root_.GlobalTheory.SmGL.Levi R m =>
      Matrix.reindex e e (blockDiagonal' fun a => (g a : Matrix (m a) (m a) R))
    exact (Continuous.matrix_blockDiagonal'
      (continuous_pi fun a => Units.continuous_val.comp (continuous_apply a))).matrix_reindex e e
  have hinv : Continuous fun g : _root_.GlobalTheory.SmGL.Levi R m => g⁻¹ :=
    continuous_pi fun a => Units.continuous_iff.2
      ⟨Units.continuous_coe_inv.comp (continuous_apply a),
        by simp; exact Units.continuous_val.comp (continuous_apply a)⟩
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  convert hval.comp hinv using 1
  funext g
  simp [map_inv]
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
