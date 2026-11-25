-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.eq_zero_or_one_of_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:07.863422+00:00
-- url     : https://prove2.me/submissions/821d94e0-6d5b-4ff9-8d65-e1944e5b7a8c

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  GroundTheory.Global.SemiLocal
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution {L : Type*} [Field L] {x : L} (h : x * x = x) : x = 0 ∨ x = 1 := by
  have h1 : x * (x - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (sub_eq_zero.1 h2)
end GroundTheory.BlockD.ThmBHecke
