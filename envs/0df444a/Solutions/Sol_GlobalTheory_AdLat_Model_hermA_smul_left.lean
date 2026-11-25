-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.hermA_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:27:50.890562+00:00
-- url     : https://prove2.me/submissions/87738d17-b0b3-4292-b27f-e80b4a87ba2d

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
    _root_.GlobalTheory.AdLat.hermA c G (t • x) y = t * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end _root_.GlobalTheory.AdLat.Model
end GlobalTheory.AdLat.Model
