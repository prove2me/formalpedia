-- Prove2me | solution 1 for GlobalTheory.RootEx.ConjVol.embX_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:17.883035+00:00
-- url     : https://prove2.me/submissions/bdebe3e3-4d78-4c01-af16-2456c64cf415

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Theorems.Thm_GlobalTheory_RootEx_ConjVol_mem_normalizer_of_tri
import Theorems.Thm_GlobalTheory_RootEx_ConjVol_embX_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ConjVol
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.ConjVol
theorem _root_.solution (p : ℕ) (x : GL n k) :
    embX c x ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) :=
  mem_normalizer_of_tri (embX_tri p x) (by rw [← map_inv]; exact embX_tri p _)
end GlobalTheory.RootEx.ConjVol
