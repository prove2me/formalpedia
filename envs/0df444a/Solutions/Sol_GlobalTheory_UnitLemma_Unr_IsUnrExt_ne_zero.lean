-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.IsUnrExt.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:46.375806+00:00
-- url     : https://prove2.me/submissions/e4d1ed48-333a-43d8-ad28-3ceff307d618

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceIntOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
namespace IsUnrExt
theorem _root_.solution {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : d ≠ 0 := by
  intro hd
  have h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1 := by
    rw [K'.card_res, hU.1, hd, pow_zero, one_pow]
  have h2 := Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)
  omega
end IsUnrExt
end GlobalTheory.UnitLemma.Unr
