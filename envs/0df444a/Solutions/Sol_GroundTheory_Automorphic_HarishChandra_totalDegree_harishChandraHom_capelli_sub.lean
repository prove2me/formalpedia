-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.totalDegree_harishChandraHom_capelli_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:34.824857+00:00
-- url     : https://prove2.me/submissions/06ae0475-d2e0-4a25-a259-eb4d9a2c9ed5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_polyLE_mono
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_capelli_sub_mem
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_sub_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_psum_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_capelli_mem_center
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_harishChandraHom_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (k : ℕ) :
    (harishChandraHom (⟨capelli (k + 1), capelli_mem_center _⟩ : Subalgebra.center ℂ (U n)) -
      psum (Fin n) ℂ (k + 1)).totalDegree < k + 1 := by
  rw [harishChandraHom_apply]
  set P := hcProjLin (capelli (n := n) (k + 1))
  have h1 : P - psum (Fin n) ℂ (k + 1) ∈ polyLE n k := hcProjLin_capelli_sub_mem k
  have hP : P ∈ polyLE n (k + 1) := by
    have := Submodule.add_mem _ (polyLE_mono (Nat.le_succ k) h1) (psum_mem_polyLE (k + 1))
    rwa [sub_add_cancel] at this
  have h2 := translate_sub_mem_polyLE (-rhoVec n) (k + 1) P hP
  rw [Nat.add_sub_cancel] at h2
  have : translate (-rhoVec n) P - psum (Fin n) ℂ (k + 1) =
      (translate (-rhoVec n) P - P) + (P - psum (Fin n) ℂ (k + 1)) := by ring
  rw [this]
  exact Nat.lt_succ_of_le (mem_polyLE.1 (Submodule.add_mem _ h2 h1))
end GroundTheory.Automorphic.HarishChandra
