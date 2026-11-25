-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.lt_of_elimKey_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:26.786055+00:00
-- url     : https://prove2.me/submissions/4b944874-18d1-42e5-8006-8cd6bd5b1089

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {i j : Fin n} (h : elimKey β i < elimKey β j) (hβ : Monotone β) :
    i < j := by
  rw [elimKey, elimKey, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨-, h⟩
  · exact lt_of_not_ge fun hji => (hβ hji).not_gt h
  · exact h
end GroundTheory.Automorphic.Parabolic
