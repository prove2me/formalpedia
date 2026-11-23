-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:36.975373+00:00
-- url     : https://prove2.me/submissions/6a88ebe5-d262-4684-97e1-3a7edb2b1c40

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_const
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
namespace IsPolyFun
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℂ → B) (h : ∀ i, IsPolyFun (f i)) :
    IsPolyFun (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPolyFun.const (0 : B)
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (h a).add ih
end IsPolyFun
end GlobalTheory.CompanionTheory.Inh.CharId
