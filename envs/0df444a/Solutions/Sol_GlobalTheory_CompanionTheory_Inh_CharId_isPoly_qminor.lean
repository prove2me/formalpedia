-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CharId.isPoly_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:10:27.46027+00:00
-- url     : https://prove2.me/submissions/12a52f16-bc50-439e-8faa-38df991af7b8

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_const
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_prod_ofFn
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_isPoly_Tm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset TensorProduct Formalism.HermitianLatticeCounting.S8
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inh GlobalTheory.CompanionTheory.Inh.CharId
open Polynomial Formalism.REAL
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace GlobalTheory.CompanionTheory.Inh.CharId
theorem _root_.solution {n t : ℕ} (E : Fin n → Fin n → B) (a b : Fin t → Fin n) (c : ℂ) :
    IsPolyFun (fun u => qminor E a b (u + c)) := by
  unfold qminor
  refine IsPolyFun.sum _ _ fun σ => (IsPolyFun.const _).mul
    (IsPolyFun.prod_ofFn t (fun k u => Tm E (u + c - (k : ℂ)) (a (σ k)) (b k)) fun k => ?_)
  have := isPoly_Tm E ((k : ℂ) - c) (a (σ k)) (b k)
  convert this using 3
  ring
end GlobalTheory.CompanionTheory.Inh.CharId
