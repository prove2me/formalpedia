-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isSplitting_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:29:25.101244+00:00
-- url     : https://prove2.me/submissions/98232158-3cc4-4412-a36b-0f4aee50b13e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_nonempty_basis
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_map
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_of_isDomain
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isUnit_discr

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
omit [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {σ : ι → 𝓞 E →+* S} (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E)
    (f : S →+* R) (hu : IsUnit (NumberField.discr E : R)) :
    IsSplitting fun i => f.comp (σ i) := by
  classical
  obtain ⟨b⟩ := nonempty_basis hc
  exact isSplitting_of_isUnit_discr b
    (det_sq_eq_discr_map (det_sq_eq_discr_of_isDomain hσ b) f) hu
end GlobalTheory.EigenSplit
