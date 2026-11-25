-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.psiN_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:30.300674+00:00
-- url     : https://prove2.me/submissions/df967b13-eb36-4ffe-af92-edf0c70f060c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_psiN_inv
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_psiN_sigma

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
theorem _root_.solution (ψ₀ : AddChar F ℂ) {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    psiN ψ₀ (theta u) = (psiN ψ₀ u)⁻¹ := by
  rw [theta, psiN_inv ψ₀ (sigma_mem_unipotent hu), psiN_sigma]
end GroundTheory.Automorphic.Whittaker
