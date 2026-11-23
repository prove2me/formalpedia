-- Prove2me | solution 1 for GlobalTheory.EigenSplit.det_sq_eq_discr_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:33.207511+00:00
-- url     : https://prove2.me/submissions/385d4632-59d0-43e8-812a-6387cae5f5c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

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
theorem _root_.solution {σ : ι → 𝓞 E →+* R} {b : Module.Basis ι ℤ (𝓞 E)}
    (hd : (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R))
    {R' : Type*} [CommRing R'] (f : R →+* R') :
    (Matrix.of fun i j => f.comp (σ i) (b j)).det ^ 2 = (NumberField.discr E : R') := by
  have := congrArg f hd
  rw [map_pow, RingHom.map_det, map_intCast] at this
  exact this
end GlobalTheory.EigenSplit
