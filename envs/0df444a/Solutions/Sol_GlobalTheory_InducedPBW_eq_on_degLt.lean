-- Prove2me | solution 1 for GlobalTheory.InducedPBW.eq_on_degLt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:53.785949+00:00
-- url     : https://prove2.me/submissions/93df9216-d6ed-47a3-94a7-8433feed94c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.InducedPBW
variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
namespace GlobalTheory.InducedPBW
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module R W] {n : ℕ}
    (f f' : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W)
    (h : ∀ α v, α.degree < n → f (zv α v) = f' (zv α v)) : ∀ m ∈ degLt R ι V n, f m = f' m := by
  intro m hm
  have := map_degLt (f - f') ⊥ (fun α v hα => by simp [h α v hα]) m hm
  simpa [sub_eq_zero] using this
end GlobalTheory.InducedPBW
