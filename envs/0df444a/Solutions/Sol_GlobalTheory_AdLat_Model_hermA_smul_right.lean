-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.hermA_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:26:27.239465+00:00
-- url     : https://prove2.me/submissions/0075906f-9b94-4cb7-9851-0a75ed00ca48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat.Model
namespace _root_.GlobalTheory.AdLat.Model
theorem _root_.solution (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (t : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (t • y) =
      _root_.GlobalTheory.AdLat.sg _ c t * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end _root_.GlobalTheory.AdLat.Model
end GlobalTheory.AdLat.Model
