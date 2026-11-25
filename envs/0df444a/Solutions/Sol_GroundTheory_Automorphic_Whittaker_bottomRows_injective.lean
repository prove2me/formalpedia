-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.bottomRows_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:30.371139+00:00
-- url     : https://prove2.me/submissions/81612866-8539-4f73-8378-40a2a73fe20d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
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
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (k : Fin n) : Function.Injective (bottomRows k) := by
  intro a b h
  simp only [bottomRows, Fin.ext_iff] at h
  exact Fin.ext (by omega)
end GroundTheory.Automorphic.Whittaker
