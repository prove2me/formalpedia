-- Prove2me | solution 1 for GlobalTheory.PairOp.isAdj_dia
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:49.842136+00:00
-- url     : https://prove2.me/submissions/890cfec3-70e6-4471-8dae-2c641fb68f09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
namespace GlobalTheory.PairOp
theorem _root_.solution (c : 𝓀[k]ˣ) : IsAdj (n := n) (dia c) (dia c⁻¹) := by
  intro φ φ' _ _
  unfold cntIp
  simp only [dia_apply]
  conv_rhs => rw [← finsum_comp_equiv (MulAction.toPerm c : Equiv.Perm (Pair k n))]
  simp [MulAction.toPerm_apply]
end GlobalTheory.PairOp
