-- Prove2me | solution 1 for GlobalTheory.LocSplit.val_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:44.585511+00:00
-- url     : https://prove2.me/submissions/0dd7d81f-ffed-4999-a719-74b9fd5d3b57

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
namespace GlobalTheory.LocSplit
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (g : R)
    (h1 : g ∈ w.asIdeal) (h2 : g ∉ w.asIdeal ^ 2) : w.intValuation g = WithZero.exp (-1 : ℤ) := by
  have a1 := (w.intValuation_le_pow_iff_mem g 1).2 (by simpa using h1)
  have a2 := mt (w.intValuation_le_pow_iff_mem g 2).1 h2
  have h0 : w.intValuation g ≠ 0 := fun h => a2 (by rw [h]; exact zero_le)
  rw [← WithZero.exp_log h0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  rw [WithZero.exp_inj]
  push_cast at a1 a2
  omega
end GlobalTheory.LocSplit
