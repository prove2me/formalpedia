-- Prove2me | solution 1 for GlobalTheory.LatClass.mem_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:34:48.810327+00:00
-- url     : https://prove2.me/submissions/68dcb694-3696-443b-bc77-a7828d53cf20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_mem_nf
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NormalRepresentationLattice_nfBasis_one
import Theorems.Thm_GlobalTheory_StepData_mem_latOf_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LatClass
theorem _root_.solution {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (normalBasis ϖ e z) ↔
      (∀ r, y (.inl r) - y (.inr 0) * z r ∈ 𝒪[k]) ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by
  rw [← nfBasis_one, mem_nf, mem_latOf_one]
end GlobalTheory.LatClass
