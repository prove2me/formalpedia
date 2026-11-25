-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_congruence_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:06.31779+00:00
-- url     : https://prove2.me/submissions/68851d52-7466-4b5e-b190-83dd502431ee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_hasBasis_nhds_one


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hσ : IsSmooth σ) (v : W) :
    ∃ j : ℕ, ∀ m : levi F n β, (m : GL (Fin n) F) ∈ congruenceSubgroup F n j → σ m v = v := by
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 (hσ v)
  have h1 : (1 : GL (Fin n) F) ∈ U := by
    have : (1 : levi F n β) ∈ (stabilizerOf σ v : Set (levi F n β)) := (stabilizerOf σ v).one_mem
    rw [← hUe] at this
    exact this
  obtain ⟨j, -, hj⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hU.mem_nhds h1)
  refine ⟨j, fun m hm => ?_⟩
  have : m ∈ (stabilizerOf σ v : Set (levi F n β)) := by
    rw [← hUe]
    exact hj hm
  exact this
end GroundTheory.Automorphic.Parabolic
