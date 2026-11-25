-- Prove2me | solution 1 for GlobalTheory.LatClass.embX_mul_nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:56:28.088541+00:00
-- url     : https://prove2.me/submissions/7efadc0e-eeec-4289-b1c6-a9514c0b1446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NormalRepresentationLattice_nfBasis_val
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val


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
omit [ValuativeRel k]
namespace GlobalTheory.LatClass
theorem _root_.solution (x g : GL n k) (e : Fin c → ℤ) (z : n → k) :
    embX c x * nfBasis ϖ g e z = nfBasis ϖ (x * g) e (x.val *ᵥ z) := by
  ext1
  rw [Units.val_mul, nfBasis_val, nfBasis_val, Radical.embX_val, fromBlocks_multiply]
  ext (r | r) (s | s)
  · simp
  · by_cases h : s.val = 0 <;> simp [h, Matrix.mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  · simp
  · simp
end GlobalTheory.LatClass
