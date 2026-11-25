-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.continuous_rootElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:39.123107+00:00
-- url     : https://prove2.me/submissions/9e9fe3dc-2d03-4923-9fe5-c5ff9ebffa57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rootElt_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rootElt_neg
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ}
variable [IsTopologicalRing F]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (i j : Fin n) : Continuous (rootElt i j : F → GL (Fin n) F) := by
  by_cases h : i = j
  · subst h
    have : (rootElt i i : F → GL (Fin n) F) = fun _ => 1 := funext fun a => rootElt_self i a
    rw [this]
    exact continuous_const
  have hval : Continuous fun a : F => ((rootElt i j a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    refine continuous_matrix fun r c => ?_
    simp only [rootElt_apply h]
    refine continuous_const.add ?_
    split_ifs
    · exact continuous_id
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun a : F => (((rootElt i j a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      fun a => ((rootElt i j (-a) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    funext a
    rw [rootElt_neg]
  rw [this]
  exact hval.comp continuous_neg
end GroundTheory.Automorphic.Whittaker
