-- Prove2me | solution 1 for GlobalTheory.RealWeil.dRho_single_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:16.452193+00:00
-- url     : https://prove2.me/submissions/58a25a85-4015-4a45-865e-e1a91b79fc6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Theorems.Thm_GlobalTheory_RealWeil_dRho_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (k : l) (f : Sch l) (x : EuclideanSpace ℝ l) :
    dRho (Pi.single (Sum.inr k) 1) f x = 2 * π * I * x k * f x := by
  have h1 : pPart (Pi.single (Sum.inr k) 1 : l ⊕ l → ℝ) = 0 := by
    ext i
    simp [pPart]
  have h2 : qPart (Pi.single (Sum.inr k) 1 : l ⊕ l → ℝ) = EuclideanSpace.single k 1 := by
    ext i
    simp [qPart, Pi.single_apply]
  simp [dRho_apply, h1, h2, EuclideanSpace.inner_single_left]
end GlobalTheory.RealWeil
