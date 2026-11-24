-- Prove2me | solution 1 for GlobalTheory.AdLat.valued_natCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:31.867425+00:00
-- url     : https://prove2.me/submissions/65b38dde-036f-4dcd-883b-b7ffa42e3a1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Theorems.Thm_GlobalTheory_AdLat_valued_natCast_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.AdLat
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.AdLat
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) ≤ 1 := by
  rw [valued_natCast_eq]; exact v.intValuation_le_one _
end GlobalTheory.AdLat
