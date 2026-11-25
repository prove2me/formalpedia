-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isSplitting_conjugateHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:39:55.348898+00:00
-- url     : https://prove2.me/submissions/c27921bd-cc60-45bc-9f86-37ac65906b28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_nonempty_basis
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_conjugateHom
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
theorem _root_.solution {L : Type*} [Field L] [Algebra (𝓞 L) R] {φ : ι → E →+* L}
    (hφ : Function.Injective φ) (hc : Fintype.card ι = Module.finrank ℚ E)
    (hu : IsUnit (NumberField.discr E : R)) : IsSplitting fun i => conjugateHom L R (φ i) := by
  classical
  obtain ⟨b⟩ := nonempty_basis hc
  exact isSplitting_of_isUnit_discr b (det_sq_conjugateHom hφ b) hu
end GlobalTheory.EigenSplit
