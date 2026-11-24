-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.isQuotInt_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:22:12.681806+00:00
-- url     : https://prove2.me/submissions/ec5020a0-4524-465d-9d8f-25c9cab63078

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
variable {ν : Measure k} {μX : Measure (GL n k)} {μG : Measure (GL (n ⊕ Fin c) k)}
  {J : Subgroup (GL (n ⊕ Fin c) k)} {bas : GL (n ⊕ Fin c) k} {ψ : AddChar k Circle} {μ : kˣ →* ℂˣ}
  {lam : J →* ℂˣ} {κ : ℝ}
namespace GlobalTheory.CollapseCompare
theorem _root_.solution {Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)}
    (H : CollapsesWith ν μX μG J bas ψ μ lam Φ κ) (z : ℂ) : IsQuotInt ν μX μG 1 (fun _ => 0) z ↔ z = 0 := by
  have := H ℂ ℂ ℂ 1 1 1 (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) 0
    ⟨fun φ g _ v => by simp, fun g φ v => by simp⟩ 0 (fun g h φ Ψ => by simp) 0 0 (fun κ => by simp) z
  rw [show integrand ψ ν μ Φ (1 : Representation ℂ _ ℂ) (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) (0 : ℂ →ₗ[ℂ] _ →ₗ[ℂ] ℂ) 0 0 =
    fun _ => 0 from funext fun h => by simp [integrand]] at this
  simpa using this
end GlobalTheory.CollapseCompare
