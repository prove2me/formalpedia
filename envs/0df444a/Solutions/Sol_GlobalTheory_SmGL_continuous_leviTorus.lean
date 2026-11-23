-- Prove2me | solution 1 for GlobalTheory.SmGL.continuous_leviTorus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:54.386368+00:00
-- url     : https://prove2.me/submissions/a1f0dc03-cddc-421c-a152-0f8f7c8aebfb

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
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution [TopologicalSpace R] (n : Type) :
    Continuous (_root_.GlobalTheory.SmGL.leviTorus R n) :=
  continuous_pi fun i => Units.continuous_iff.2
    ⟨continuous_pi fun x => continuous_pi fun y => by
        simp [_root_.GlobalTheory.SmGL.leviTorus, GeneralLinearGroup.scalar]
        exact Units.continuous_val.comp (continuous_apply i),
      continuous_pi fun x => continuous_pi fun y => by
        simp [_root_.GlobalTheory.SmGL.leviTorus, GeneralLinearGroup.scalar]
        exact Units.continuous_coe_inv.comp (continuous_apply i)⟩
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
