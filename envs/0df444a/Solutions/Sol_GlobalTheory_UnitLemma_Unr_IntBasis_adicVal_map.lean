-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:00.450748+00:00
-- url     : https://prove2.me/submissions/a6d5639a-d945-471d-880a-d2a3faf9ed1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis
open IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr.IntBasis
theorem _root_.solution (h : IsUnrExt K K' d φ) (x : K.E) : adicVal K' (φ x) = adicVal K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hφ : φ x ≠ 0 := (map_ne_zero φ).2 hx
  have h1 := h.2.2.1 x
  unfold val at h1
  have h2 := neg_inj.1 h1
  have a1 : adicVal K' (φ x) ≠ 0 := (Valuation.ne_zero_iff _).2 hφ
  have a2 : adicVal K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [← WithZero.exp_log a1, ← WithZero.exp_log a2]
  exact congrArg WithZero.exp h2
end GlobalTheory.UnitLemma.Unr.IntBasis
