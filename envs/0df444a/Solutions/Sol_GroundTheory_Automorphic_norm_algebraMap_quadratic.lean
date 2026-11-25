-- Prove2me | solution 1 for GroundTheory.Automorphic.norm_algebraMap_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:08.01361+00:00
-- url     : https://prove2.me/submissions/b95fcfd1-ed19-4c2d-8e66-f80e35ebd883

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
theorem _root_.solution (t : F) : Algebra.norm F (algebraMap F E t) = t ^ 2 := by
  rw [Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]
end GroundTheory.Automorphic
