-- Prove2me | solution 1 for GlobalTheory.LatClass.col_mem_nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:43:41.884805+00:00
-- url     : https://prove2.me/submissions/41afebd4-e1ec-4b9c-ab6e-7bbb14d6864d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_zero_mem_pow
import Theorems.Thm_GlobalTheory_LatClass_mem_nf

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
theorem _root_.solution {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} (i : Fin (c + 1)) {s : k}
    (hs : s ∈ powInt ϖ (e i)) :
    (Sum.elim (fun r => if i = 0 then s * z r else 0) (Pi.single i s) : n ⊕ Fin (c + 1) → k) ∈
      latOf (nfBasis ϖ g e z) := by
  refine mem_nf.2 ⟨?_, fun l => ?_⟩
  · convert zero_mem (latOf g) using 1
    ext r
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  · rw [Sum.elim_inr, Pi.single_apply]
    split_ifs with h
    · rwa [h]
    · exact zero_mem_pow
end GlobalTheory.LatClass
