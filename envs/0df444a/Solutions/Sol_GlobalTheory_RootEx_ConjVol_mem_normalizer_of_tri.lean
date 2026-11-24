-- Prove2me | solution 1 for GlobalTheory.RootEx.ConjVol.mem_normalizer_of_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:52.615214+00:00
-- url     : https://prove2.me/submissions/593e19bc-a62d-4bf5-9ebe-49671e71a038

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Theorems.Thm_GlobalTheory_RootEx_ConjVol_conj_mem_of_tri
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
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ConjVol
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.ConjVol
theorem _root_.solution {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g.val.BlockTriangular (lev p))
    (hg' : (g⁻¹).val.BlockTriangular (lev p)) :
    g ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun u => ⟨conj_mem_of_tri hg hg', fun h => ?_⟩
  have := conj_mem_of_tri hg' (by rwa [inv_inv]) h
  simpa [mul_assoc] using this
end GlobalTheory.RootEx.ConjVol
