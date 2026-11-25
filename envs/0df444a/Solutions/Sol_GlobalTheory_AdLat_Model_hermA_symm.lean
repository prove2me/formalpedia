-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.hermA_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:26:32.872984+00:00
-- url     : https://prove2.me/submissions/d75f89bb-a283-4a75-9c4d-04bb18bacc09

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
theorem _root_.solution (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, c (G a b) = G b a) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.sg _ c (_root_.GlobalTheory.AdLat.hermA c G x y) =
      _root_.GlobalTheory.AdLat.hermA c G y x := by
  have hinv : ∀ z : _root_.GlobalTheory.AdLat.RA F E,
      _root_.GlobalTheory.AdLat.sg _ c (_root_.GlobalTheory.AdLat.sg _ c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [_root_.GlobalTheory.AdLat.sg, hc]
    | add u w hu hw => rw [map_add, map_add, hu, hw]
  have hG' : ∀ a b, _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] G a b) = 1 ⊗ₜ[F] G b a := by
    intro a b
    simp [_root_.GlobalTheory.AdLat.sg, hG]
  simp only [_root_.GlobalTheory.AdLat.hermA, map_sum, map_mul, hinv, hG']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end _root_.GlobalTheory.AdLat.Model
end GlobalTheory.AdLat.Model
