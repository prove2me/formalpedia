-- Prove2me | solution 1 for GlobalTheory.SgLoc.PtAlg.mat_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:25.505996+00:00
-- url     : https://prove2.me/submissions/c3e10138-1a67-464e-bbc0-ed6d0665409e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Theorems.Thm_GlobalTheory_SgLoc_PtAlg_ptEntryL_append

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.PtAlg
variable {E : Type} [CommRing E]
namespace GlobalTheory.SgLoc.PtAlg
theorem _root_.solution {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) (a b : Fin (m + s)) :
    (h.snoc t s).mat a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then h.mat ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else if m ≤ (a : ℕ) ∧ m ≤ (b : ℕ) ∧ (a : ℕ) + b + 1 = 2 * m + s then (t : E) else 0 := by
  show ptEntryL (h.blocks ++ [(t, s)]) a b = _
  rw [ptEntryL_append h.blocks t s m h.size]
  split_ifs <;> rfl
end GlobalTheory.SgLoc.PtAlg
