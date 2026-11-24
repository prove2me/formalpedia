-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.mem_rowR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:48:28.295011+00:00
-- url     : https://prove2.me/submissions/15dde7d8-eec3-45bf-abfb-7779559680cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution (hs : 1 ≤ G.s) {j c : ℕ} (hj : j < G.m) (h : topRank G j + c = G.rank (G.m, j))
    {g : GL (Fin (G.rank (G.m, j))) k} (hg : frameGL h g ∈ symR k _ c) : g ∈ rowR hs hj := by
  have hc : c = G.m - 1 - j := by
    have := topRank_add hs j
    omega
  subst hc
  exact hg
end GlobalTheory.FunObj.OneCosetProof
