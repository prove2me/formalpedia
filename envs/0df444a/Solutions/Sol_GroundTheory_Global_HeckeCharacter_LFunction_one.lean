-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.LFunction_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:57.179001+00:00
-- url     : https://prove2.me/submissions/09225860-c144-4de4-a5be-5064c9c59713

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_coeff_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution (s : ℂ) : (1 : HeckeCharacter K).LFunction s = dedekindZeta K s := by
  rw [LFunction, dedekindZeta]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  have hy : ∀ y : {I : Ideal (𝓞 K) // absNorm I = n}, (1 : HeckeCharacter K).coeff y = 1 := by
    intro y
    refine coeff_one fun h ↦ hn ?_
    rw [← y.2, h, Ideal.absNorm_bot]
  rw [LCoeff, tsum_congr hy, tsum_const, nsmul_eq_mul, mul_one]
end GroundTheory.Global.HeckeCharacter
