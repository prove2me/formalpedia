-- Prove2me | solution 1 for GlobalTheory.UnitLemma.OrthoSelfDual.herm_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:09.017599+00:00
-- url     : https://prove2.me/submissions/1eb7dc09-2fc3-4663-9fde-c46868efd493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanSelfDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrthoSelfDual
namespace GlobalTheory.UnitLemma.OrthoSelfDual
theorem _root_.solution {K : UQ} (B : InvAlg K) (x : B.A) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A)
    (h : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (y : B.A) (j : Fin n) :
    B.herm x y (e j) = e.repr y j := by

  have hlin : hermLeft B x (e j) = e.coord j := by
    refine e.ext fun i => ?_
    rw [Module.Basis.coord_apply, e.repr_self, Finsupp.single_apply]
    exact h i j
  have := LinearMap.congr_fun hlin y
  rw [Module.Basis.coord_apply] at this
  exact this
end GlobalTheory.UnitLemma.OrthoSelfDual
