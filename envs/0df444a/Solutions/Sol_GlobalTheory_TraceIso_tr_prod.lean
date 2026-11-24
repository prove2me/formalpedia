-- Prove2me | solution 1 for GlobalTheory.TraceIso.tr_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:56.285288+00:00
-- url     : https://prove2.me/submissions/c7b5628b-c27b-44ec-8fde-2f8358fad337

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
theorem _root_.solution [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    tr k (V × W) a = tr k V a + tr k W a := by
  have h : Algebra.lsmul k k (V × W) a = (Algebra.lsmul k k V a).prodMap (Algebra.lsmul k k W a) := by
    ext <;> simp
  rw [tr, h, LinearMap.trace_prodMap']
  rfl
end GlobalTheory.TraceIso
