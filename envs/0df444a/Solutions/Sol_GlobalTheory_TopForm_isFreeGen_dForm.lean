-- Prove2me | solution 1 for GlobalTheory.TopForm.isFreeGen_dForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:46.807259+00:00
-- url     : https://prove2.me/submissions/da68fd3f-46c1-4ffd-b3f0-10b12f4a9484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_P2M_GlobalTheory_TopForm_isFreeGen__Multi_52fc91f67394

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}
namespace GlobalTheory.TopForm
theorem _root_.solution (x : Fin D → A) (b : Module.Basis (Fin D) A (Omega α))
    (hb : ∀ i, b i = dFun α (x i)) : IsFreeGen A (dForm α x) := by
  have := isFreeGen_ιMulti b
  rwa [show (b : Fin D → Omega α) = fun i => dFun α (x i) from funext hb] at this
end GlobalTheory.TopForm
