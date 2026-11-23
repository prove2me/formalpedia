-- Prove2me | solution 1 for GlobalTheory.SmGL.mem_unipRadLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:30.229106+00:00
-- url     : https://prove2.me/submissions/8a07bd52-6256-40ed-b612-8334ecd2e171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad

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
theorem _root_.solution {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.unipRadLower R e ↔ g ∈ _root_.GlobalTheory.SmGL.parabLower R e ∧
      ∀ a (i j : m a),
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j :=
  _root_.GlobalTheory.SmGL.mem_unipRad (e := _root_.GlobalTheory.SmGL.opp e)
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
