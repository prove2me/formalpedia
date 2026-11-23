-- Prove2me | solution 1 for GlobalTheory.SmGL.det_eq_one_of_mem_unipRad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:01.277129+00:00
-- url     : https://prove2.me/submissions/41408710-d067-44c5-ac3c-32535810da2d

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
theorem _root_.solution {e : (Σ a, m a) ≃ n} {u : GL n R}
    (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) : GeneralLinearGroup.det u = 1 := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hu
  show GeneralLinearGroup.det (p : GL n R) = 1
  rw [_root_.GlobalTheory.SmGL.det_parab, MonoidHom.mem_ker.1 hp]
  simp
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
