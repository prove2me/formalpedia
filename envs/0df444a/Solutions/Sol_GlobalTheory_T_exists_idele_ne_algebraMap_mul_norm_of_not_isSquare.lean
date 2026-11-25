-- Prove2me | solution 1 for GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:50.554081+00:00
-- url     : https://prove2.me/submissions/0de887ca-4dfd-49e7-993e-ca2b0c96b486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNormStatement
import Theorems.Thm_GlobalTheory_QNorm_exists_idele_not_mul_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  first | exact @GlobalTheory.QNorm.exists_idele_not_mul_norm | exact GlobalTheory.QNorm.exists_idele_not_mul_norm | (intros; apply GlobalTheory.QNorm.exists_idele_not_mul_norm <;> assumption)
end _root_.GlobalTheory.T
