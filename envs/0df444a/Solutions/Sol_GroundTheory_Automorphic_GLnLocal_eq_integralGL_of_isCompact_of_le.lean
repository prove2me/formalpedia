-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.eq_integralGL_of_isCompact_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:56.554004+00:00
-- url     : https://prove2.me/submissions/60c8a14a-18d7-4680-93fd-88c2c8cf62b9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_conj_mem_integralGL_of_conj_inv_mem
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_conj_le_integralGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) (hle : integralGL F n ≤ H) :
    H = integralGL F n := by
  obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hH
  refine le_antisymm (fun h hh => ?_) hle
  have h1 := conj_mem_integralGL_of_conj_inv_mem F n (fun k hk => hg k (hle hk)) (hg h hh)
  have : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
  rwa [this] at h1
end GroundTheory.Automorphic.GLnLocal
