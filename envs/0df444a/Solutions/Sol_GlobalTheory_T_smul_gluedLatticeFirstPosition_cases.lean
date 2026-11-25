-- Prove2me | solution 1 for GlobalTheory.T.smul_gluedLatticeFirstPosition_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:26:52.613443+00:00
-- url     : https://prove2.me/submissions/ae459890-0a07-4d8f-82be-9c4450eedd32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCases
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCasesStatement
import Theorems.Thm_GlobalTheory_GluedOrbit_smul_gluedS_cases


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k), (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec → (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) → (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨ h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨ ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  first | exact @GlobalTheory.GluedOrbit.smul_gluedS_cases | exact GlobalTheory.GluedOrbit.smul_gluedS_cases | (intros; apply GlobalTheory.GluedOrbit.smul_gluedS_cases <;> assumption)
end _root_.GlobalTheory.T
