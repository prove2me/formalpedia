-- Prove2me | solution 1 for GlobalTheory.AdLat.valued_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:24.552808+00:00
-- url     : https://prove2.me/submissions/592befe1-c9ae-4e5e-982e-0a38b6e22622

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    Valued.v (N : v.adicCompletion F) ≠ 0 := by
  rw [valued_natCast_eq]
  exact v.intValuation_ne_zero _ (by exact_mod_cast hN.ne')
end GlobalTheory.AdLat
