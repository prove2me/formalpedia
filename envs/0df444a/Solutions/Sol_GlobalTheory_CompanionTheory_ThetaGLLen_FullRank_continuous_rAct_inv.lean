-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.continuous_rAct_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:15.278303+00:00
-- url     : https://prove2.me/submissions/8ca49647-8d8c-4d15-84a1-d2004b893ddc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution (κ : ℕ) :
    Continuous fun p : GL a k × RankIn k a c {κ} => rAct {κ} p.2 p.1⁻¹ := by
  refine Continuous.subtype_mk (f := fun p : GL a k × RankIn k a c {κ} => act p.2.1 (p.1⁻¹, 1)) ?_ _
  exact (continuous_const.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul
    (Units.continuous_coe_inv.comp continuous_fst)
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
