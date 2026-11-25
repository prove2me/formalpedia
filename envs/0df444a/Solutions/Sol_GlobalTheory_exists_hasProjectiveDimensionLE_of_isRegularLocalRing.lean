-- Prove2me | solution 1 for GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:49.819459+00:00
-- url     : https://prove2.me/submissions/03856239-ce45-4e96-abb9-dd2e7518459a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Theorems.Thm_GlobalTheory_projectiveDimension_quotient_maximalIdeal_ne_top
import Theorems.Thm_GlobalTheory_exists_hasProjectiveDimensionLE_of_residueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n :=
  fun R _ _ M _ _ _ => exists_hasProjectiveDimensionLE_of_residueField R
    (projectiveDimension_quotient_maximalIdeal_ne_top R) M
end GlobalTheory
