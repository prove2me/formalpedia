-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.psiN_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:47.87081+00:00
-- url     : https://prove2.me/submissions/ef09e4da-fcd6-4f62-bb81-1eaeb43e7324

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (g : GL (Fin n) F) : psiN ψ₀ g ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ₀ (superdiagSum (g : Matrix (Fin n) (Fin n) F))
    (-superdiagSum (g : Matrix (Fin n) (Fin n) F))
  rw [add_neg_cancel, AddChar.map_zero_eq_one] at this
  rw [psiN] at h
  rw [h, zero_mul] at this
  exact one_ne_zero this
end GroundTheory.Automorphic.Whittaker
