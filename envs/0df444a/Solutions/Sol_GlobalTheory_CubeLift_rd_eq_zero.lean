-- Prove2me | solution 1 for GlobalTheory.CubeLift.rd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:30.356607+00:00
-- url     : https://prove2.me/submissions/d52b79f5-97c8-49ae-94df-9d1186968202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd

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
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution {I : Ideal A} {u : A[X]} : rd I u = 0 ↔ ∀ x, u.coeff x ∈ I := by
  rw [← coeff_inj, Finsupp.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]
end GlobalTheory.CubeLift
