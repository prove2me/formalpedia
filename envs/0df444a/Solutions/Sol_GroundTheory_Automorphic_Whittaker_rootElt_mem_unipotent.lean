-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rootElt_mem_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:15.151727+00:00
-- url     : https://prove2.me/submissions/1d3da622-a312-47d8-9f05-aaafc8efa566

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rootElt_apply

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
theorem _root_.solution {i j : Fin n} (h : i < j) (a : F) :
    rootElt i j a ∈ Iwasawa.unipotent F n := by
  have hne : i ≠ j := ne_of_lt h
  refine ⟨fun r c hrc => ?_, fun r => ?_⟩
  · rw [rootElt_apply hne, Matrix.one_apply_ne (ne_of_gt (show c < r from hrc)), zero_add]
    refine if_neg fun e => ?_
    rw [← e.1, ← e.2] at hrc
    exact lt_asymm h hrc
  · rw [rootElt_apply hne, Matrix.one_apply_eq, if_neg fun e => hne (e.1.trans e.2.symm), add_zero]
end GroundTheory.Automorphic.Whittaker
