-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:40.624192+00:00
-- url     : https://prove2.me/submissions/bfb07451-87b9-434f-a907-e1b095ae66a2

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity

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
theorem _root_.solution {f g : ℂ → B} (hf : IsPolyFun f) (hg : IsPolyFun g) : IsPolyFun (fun u => f u + g u) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun u => by simp [hP, hQ]⟩
end IsPolyFun
end GlobalTheory.CompanionTheory.Inh.CharId
