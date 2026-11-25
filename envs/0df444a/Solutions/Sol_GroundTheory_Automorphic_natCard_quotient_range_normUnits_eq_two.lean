-- Prove2me | solution 1 for GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:41.049535+00:00
-- url     : https://prove2.me/submissions/ea3db491-8eb4-4717-8c0e-fbcf1b5baa7a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Theorems.Thm_GroundTheory_LocalField_exists_isNonarchimedeanLocalField_valuativeExtension
import Theorems.Thm_GroundTheory_LocalField_natCard_units_quotient_range_normUnits


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
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
namespace GroundTheory.Automorphic
theorem _root_.solution :
    Nat.card (Fˣ ⧸ (normUnits F E).range) = 2 := by
  obtain ⟨_, _, _, _⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F E
  rw [natCard_units_quotient_range_normUnits, Algebra.IsQuadraticExtension.finrank_eq_two]
end GroundTheory.Automorphic
