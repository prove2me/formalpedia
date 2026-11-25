-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.iterPd_mem_geDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:13.560078+00:00
-- url     : https://prove2.me/submissions/0f791ff8-e52b-4184-97e9-a7c4b360cb53

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pderiv_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (w : List (Fin n × Fin n)) {t : ℕ} {f : Poly n} (hf : f ∈ geDeg t) :
    iterPd w f ∈ geDeg (t - w.length) := by
  induction w with
  | nil => simpa using hf
  | cons a w ih =>
    rw [iterPd_cons, List.length_cons, ← Nat.sub_sub]
    exact pderiv_mem_geDeg _ ih
end GroundTheory.Automorphic.HarishChandra
