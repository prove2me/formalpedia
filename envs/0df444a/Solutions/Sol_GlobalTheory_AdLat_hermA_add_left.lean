-- Prove2me | solution 1 for GlobalTheory.AdLat.hermA_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:24:59.382514+00:00
-- url     : https://prove2.me/submissions/e73c5735-0b34-493b-9d11-8e60b35789b9

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
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → RA F E) :
    hermA c G (x + x') y = hermA c G x y + hermA c G x' y := by
  simp only [hermA, Pi.add_apply, add_mul, Finset.sum_add_distrib]
end GlobalTheory.AdLat
