-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.psiN_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:46.86834+00:00
-- url     : https://prove2.me/submissions/78e8e1b0-b436-4a62-a266-a406dac619d9

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
theorem _root_.solution {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    psiN ψ₀ u⁻¹ = (psiN ψ₀ u)⁻¹ := by
  have h : psiN ψ₀ u⁻¹ * psiN ψ₀ u = 1 := by
    rw [← psiN_mul ψ₀ ((Iwasawa.unipotent F n).inv_mem hu) hu, inv_mul_cancel, psiN_one]
  exact eq_inv_of_mul_eq_one_left h
end GroundTheory.Automorphic.Whittaker
