-- Prove2me | solution 1 for GlobalTheory.EigenSplit.det_sq_conjugateHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:01.496933+00:00
-- url     : https://prove2.me/submissions/f2ae2641-3d08-4f17-b1b9-9ea2345edaaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_map
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_of_field

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
theorem _root_.solution {L : Type*} [Field L] [Algebra (𝓞 L) R] {φ : ι → E →+* L}
    (hφ : Function.Injective φ) (b : Module.Basis ι ℤ (𝓞 E)) :
    (Matrix.of fun i j => conjugateHom L R (φ i) (b j)).det ^ 2 = (NumberField.discr E : R) := by
  refine det_sq_eq_discr_map (σ := fun i => NumberField.RingOfIntegers.mapRingHom (φ i)) ?_ _
  apply NumberField.RingOfIntegers.coe_injective
  have := det_sq_eq_discr_of_field hφ b
  rw [map_pow, RingHom.map_det, map_intCast, ← this]
  congr 2
end GlobalTheory.EigenSplit
