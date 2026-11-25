-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigma_mul_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:18.235137+00:00
-- url     : https://prove2.me/submissions/37124d1b-e1ac-4c84-9ce1-76032997878b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_theta_eq

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
theorem _root_.solution (a g b : GL (Fin n) F) :
    sigma (a * g * b⁻¹) = theta b * sigma g * (theta a)⁻¹ := by
  rw [sigma_mul, sigma_mul, theta_eq, theta, inv_inv, mul_assoc]
end GroundTheory.Automorphic.Whittaker
