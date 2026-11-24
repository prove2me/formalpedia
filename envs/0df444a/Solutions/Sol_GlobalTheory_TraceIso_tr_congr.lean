-- Prove2me | solution 1 for GlobalTheory.TraceIso.tr_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:54.677792+00:00
-- url     : https://prove2.me/submissions/5ece3de9-3071-437b-a9bb-b5af9a3f13df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
namespace GlobalTheory.TraceIso
theorem _root_.solution (e : V ≃ₗ[A] W) (a : A) : tr k V a = tr k W a := by
  have h : Algebra.lsmul k k W a = (e.restrictScalars k).conj (Algebra.lsmul k k V a) := by
    ext w
    simp [LinearEquiv.conj_apply]
  rw [tr, tr, h, LinearMap.trace_conj']
end GlobalTheory.TraceIso
