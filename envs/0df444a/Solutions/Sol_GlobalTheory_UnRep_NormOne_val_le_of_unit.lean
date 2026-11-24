-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.val_le_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:21.748685+00:00
-- url     : https://prove2.me/submissions/0a220fcd-cdd2-4d8c-9a3c-3a48ff1249a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes
import Theorems.Thm_GlobalTheory_UnRep_NormOne_val_le_of_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (y : E) (D : ℕ) (hD : (D : 𝓞 E) ∉ P.asIdeal)
    (hy : P.valuation E y = 1) : P.valuation E ((y - 1) / D) ≤ 1 := by
  have hD0 : (D : E) ≠ 0 := by
    intro h
    have : D = 0 := by exact_mod_cast h
    apply hD; simp [this]
  refine val_le_of_mul P _ (y - 1) (D : 𝓞 E) hD (by simp [hD0]) ?_
  exact Valuation.map_sub_le _ hy.le (by simp)
end GlobalTheory.UnRep.NormOne
