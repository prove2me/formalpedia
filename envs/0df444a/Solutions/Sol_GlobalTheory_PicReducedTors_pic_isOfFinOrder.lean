-- Prove2me | solution 1 for GlobalTheory.PicReducedTors.pic_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:36.335834+00:00
-- url     : https://prove2.me/submissions/ad03c61a-653d-4dce-aaa3-6b7be118c180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatMulMemRangePiQuotientMinimalPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderPicOfIsReducedFiniteInt
import Theorems.Thm_GlobalTheory_T_isOfFinOrder_of_isOfFinOrder_pic_mapRingHom
import Theorems.Thm_P2M_GlobalTheory_T_exists_nat_mul_mem_range_pi_quotient_minimalPrimes__7a270af932d6
import Theorems.Thm_P2M_GlobalTheory_T_pic_isOfFinOrder_of_finite_int__b828631832c9
import Theorems.Thm_P2M_GlobalTheory_T_pic_pi_isOfFinOrder__3e36705ac5d3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PicReducedTors
namespace GlobalTheory.PicReducedTors
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by
  intro B _ _ _ M
  haveI : IsNoetherian ℤ B := inferInstance
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let φ := Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)
  haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance
  obtain ⟨n, hn, hmul⟩ := GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' B
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      have := congrFun hb ⟨P, hP⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact this
    obtain ⟨k, hk⟩ := hrad
    exact IsReduced.eq_zero b ⟨k, by simpa using hk⟩
  refine GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B _ φ n hinj hn hmul M ?_
  refine GlobalTheory.T.pic_pi_isOfFinOrder' _ _ (fun P N => ?_) _
  haveI : (P : Ideal B).IsPrime := P.2.1.1
  exact GlobalTheory.T.pic_isOfFinOrder_of_finite_int' _ N
end GlobalTheory.PicReducedTors
