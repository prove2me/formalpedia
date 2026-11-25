-- Prove2me | solution 1 for GlobalTheory.AdLat.Half.herm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:24.749871+00:00
-- url     : https://prove2.me/submissions/d6eef2df-6eaf-41b7-a0df-6115a098a199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralTmulOneMulMemAdelicCompletion
import Theorems.Thm_GlobalTheory_AdLat_hermA_add_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Half
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.Half
namespace _root_.GlobalTheory.AdLat.Half
theorem _root_.solution (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (x + x') y =
      _root_.GlobalTheory.AdLat.hermA c G x y + _root_.GlobalTheory.AdLat.hermA c G x' y :=
  _root_.GlobalTheory.AdLat.hermA_add_left c G x x' y
end _root_.GlobalTheory.AdLat.Half
end GlobalTheory.AdLat.Half
