-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mem_adjoin_psum_of_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:56.688465+00:00
-- url     : https://prove2.me/submissions/7b9e24bd-b979-4402-8b80-c4cd499b02da

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_esymm_mem_adjoin_psum
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_aeval_mem_of_forall_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {p : MvPolynomial (Fin n) ℂ} (hp : p.IsSymmetric) :
    p ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by
  obtain ⟨F, hF⟩ := esymmAlgHom_fin_surjective ℂ (le_refl n) ⟨p, hp⟩
  have e := congrArg Subtype.val hF
  rw [esymmAlgHom_apply] at e
  have e' : aeval (fun i : Fin n => esymm (Fin n) ℂ ((i : ℕ) + 1)) F = p := e
  rw [← e']
  exact aeval_mem_of_forall_mem _ (fun i => esymm_mem_adjoin_psum _ (by omega)) F
end GroundTheory.Automorphic.HarishChandra
