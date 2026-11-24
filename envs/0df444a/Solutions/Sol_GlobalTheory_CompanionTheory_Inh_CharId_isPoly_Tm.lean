-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CharId.isPoly_Tm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:20.135541+00:00
-- url     : https://prove2.me/submissions/c2bff34b-fb10-4fda-9cf1-e3f6c0902218

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_const
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_scalar
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_add

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → B) (c : ℂ) (a b : Fin n) :
    IsPolyFun (fun u => Tm E (u - c) a b) := by
  unfold Tm
  by_cases h : a = b
  · simp only [h, if_true, sub_eq_add_neg, map_add]
    exact (IsPolyFun.scalar.add (IsPolyFun.const _)).add (IsPolyFun.const _)
  · simp only [h, if_false]
    exact IsPolyFun.const _
end GlobalTheory.CompanionTheory.Inh.CharId
