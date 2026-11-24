-- Prove2me | solution 1 for GlobalTheory.PairOp.keepsFinite_dia
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:36.703591+00:00
-- url     : https://prove2.me/submissions/f7a429fd-3a4e-4dc1-b81a-32a2778cb5d2

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
theorem _root_.solution (c : 𝓀[k]ˣ) : KeepsFinite (n := n) (dia c) := by
  intro φ hφ
  have e : Function.support (dia c φ) = (fun P => c • P) ⁻¹' Function.support φ := by
    ext P
    simp
  rw [e]
  exact hφ.preimage (MulAction.injective c).injOn
end GlobalTheory.PairOp
