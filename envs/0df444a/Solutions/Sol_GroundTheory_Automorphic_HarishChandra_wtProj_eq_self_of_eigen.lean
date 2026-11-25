-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.wtProj_eq_self_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:04.822538+00:00
-- url     : https://prove2.me/submissions/48f97c01-8915-49ee-9e56-4c0f4e9c6e07

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowWt_eq_of_eigen
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_eq_self_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {h : Poly n} (ν : Fin n → ℕ)
    (hc : ∀ a, rowOp a a h = (ν a : ℂ) • h) : wtProj ν h = h := by
  rw [wtProj_eq_self_iff]
  intro m hm
  funext a
  exact_mod_cast rowWt_eq_of_eigen hc hm a
end GroundTheory.Automorphic.HarishChandra
