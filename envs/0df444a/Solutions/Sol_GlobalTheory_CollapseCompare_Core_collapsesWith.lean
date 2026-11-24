-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.Core.collapsesWith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:21:13.560849+00:00
-- url     : https://prove2.me/submissions/2fb95119-e60f-4662-a33e-355224d01a70

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

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
namespace Core
theorem _root_.solution {Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)}
    (H : Core ν μX μG J bas ψ μ lam Φ.1 κ) : CollapsesWith ν μX μG J bas ψ μ lam Φ κ := by
  intro P' P A _ _ _ _ _ _ π' π σ _ _ _ b hb θ hθ φ F hF z
  refine H P' P A π σ θ b (fun γ φ Ψ Ψ' e => ?_) hb φ F hF _ (fun h Ψ e => ?_) _ rfl z
  · have := hθ 1 γ φ Ψ
    rw [map_one, Module.End.one_apply] at this
    rw [← this]
    exact congrArg _ (Subtype.ext e)
  · rw [show Ψ = flatS ψ ν μ Φ h from Subtype.ext e]; rfl
end Core
end GlobalTheory.CollapseCompare
