-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.prod_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:21.034448+00:00
-- url     : https://prove2.me/submissions/c0bbe01a-8be7-42a8-a468-921f76e284bb

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_const
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_mul

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
namespace IsPolyFun
theorem _root_.solution : ∀ (t : ℕ) (f : Fin t → ℂ → B), (∀ i, IsPolyFun (f i)) →
    IsPolyFun (fun u => (List.ofFn fun k => f k u).prod)
  | 0, f, _ => by simpa using IsPolyFun.const (1 : B)
  | t + 1, f, h => by
    simpa [List.ofFn_succ] using (h 0).mul (solution t (fun k => f k.succ) fun k => h _)
end IsPolyFun
end GlobalTheory.CompanionTheory.Inh.CharId
