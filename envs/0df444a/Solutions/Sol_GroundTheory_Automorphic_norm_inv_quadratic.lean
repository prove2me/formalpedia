-- Prove2me | solution 1 for GroundTheory.Automorphic.norm_inv_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:48.124652+00:00
-- url     : https://prove2.me/submissions/3ce2bdf2-1620-4116-b8ce-0d0a2d05e798

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification

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
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
namespace GroundTheory.Automorphic
theorem _root_.solution (z : E) : Algebra.norm F z⁻¹ = (Algebra.norm F z)⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, Algebra.norm_zero, inv_zero]
  · exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hz, map_one])
end GroundTheory.Automorphic
