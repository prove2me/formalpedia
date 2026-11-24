-- Prove2me | solution 1 for GlobalTheory.AdLat.hermA_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:25:06.143831+00:00
-- url     : https://prove2.me/submissions/0d45423d-8eac-4875-8fd5-bbbcf5d4b68b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLattice
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c G (-x) y = - hermA c G x y := by
  simp only [hermA, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
end GlobalTheory.AdLat
