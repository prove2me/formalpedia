-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.superdiagSum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:56.195384+00:00
-- url     : https://prove2.me/submissions/a95f1f7b-0a7c-48c2-ada8-0b7a3b615a9c

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
theorem _root_.solution (i j : Fin n) (a : F) :
    superdiagSum (Matrix.single i j a) = if j.val = i.val + 1 then a else 0 := by
  unfold superdiagSum
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [Matrix.single_apply_same]
  · intro c _ hc
    rw [Matrix.single_apply_of_col_ne i i hc.symm, ite_self]
  · intro h
    exact absurd (Finset.mem_univ j) h
  · intro r _ hr
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Matrix.single_apply_of_row_ne hr.symm, ite_self]
  · intro h
    exact absurd (Finset.mem_univ i) h
end GroundTheory.Automorphic.Whittaker
