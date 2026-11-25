-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcProjLin_mem_polyLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:57.0377+00:00
-- url     : https://prove2.me/submissions/bacd3e6d-a888-4e23-927e-72b08b291ea4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_canon_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_filt_le_canonSpan


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
theorem _root_.solution {d : ℕ} {u : U n} (hu : u ∈ filt d) : hcProjLin u ∈ polyLE n d := by
  have hu' : u ∈ Submodule.span ℂ {u | ∃ m : Fin n × Fin n →₀ ℕ, (∀ a ∈ m.support, True) ∧
      0 ≤ m.degree ∧ m.degree ≤ d ∧ canon m = u} := filt_le_canonSpan d hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, -, -, hm, rfl⟩ := hx
    exact hcProjLin_canon_mem_polyLE hm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
end GroundTheory.Automorphic.HarishChandra
