-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isSplitting_of_isUnit_discr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:24.657098+00:00
-- url     : https://prove2.me/submissions/2d9c3078-3d50-471a-b329-42f8c41f6031

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
    (hu : IsUnit (NumberField.discr E : R)) : IsSplitting σ :=
  (isSplitting_iff_isUnit_det σ b).2 ((isUnit_pow_iff two_ne_zero).1 (hd ▸ hu))
end GlobalTheory.EigenSplit
