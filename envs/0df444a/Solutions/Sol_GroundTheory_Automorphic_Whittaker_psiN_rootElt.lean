-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.psiN_rootElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:52.729476+00:00
-- url     : https://prove2.me/submissions/2287c0ff-5751-43ae-9519-9a672c5c3ef7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_superdiagSum_add
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_superdiagSum_single

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
theorem _root_.solution (ψ₀ : AddChar F ℂ) {i j : Fin n} (h : i ≠ j) (a : F) :
    psiN ψ₀ (rootElt i j a) = if j.val = i.val + 1 then ψ₀ a else 1 := by
  rw [psiN, coe_rootElt h, superdiagSum_add, superdiagSum_one, zero_add, superdiagSum_single]
  split_ifs
  · rfl
  · exact AddChar.map_zero_eq_one ψ₀
end GroundTheory.Automorphic.Whittaker
