-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.val_mul_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:21.320819+00:00
-- url     : https://prove2.me/submissions/9497d8b5-eece-40bf-9be5-e85915630698

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.CompanionTheory.IwContract
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) F} {r s : ValueGroupWithZero F}
    (hA : ∀ i j, valuation F (A i j) ≤ r) (hB : ∀ i j, valuation F (B i j) ≤ s) (i j : Fin n) :
    valuation F ((A * B) i j) ≤ r * s := by
  rw [Matrix.mul_apply]
  refine (valuation F).map_sum_le fun k _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_mul' (hA i k) (hB k j)
end GlobalTheory.CompanionTheory.IwContract
