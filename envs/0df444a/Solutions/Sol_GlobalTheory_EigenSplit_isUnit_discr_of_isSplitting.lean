-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isUnit_discr_of_isSplitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:40:00.028068+00:00
-- url     : https://prove2.me/submissions/44ce5c87-c521-47e1-8ab4-d9cc92eaea06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_iff_isUnit_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution {σ : ι → 𝓞 E →+* R} (b : Module.Basis ι ℤ (𝓞 E))
    (hd : (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R))
    (h : IsSplitting σ) : IsUnit (NumberField.discr E : R) :=
  hd ▸ ((isSplitting_iff_isUnit_det σ b).1 h).pow 2
end GlobalTheory.EigenSplit
