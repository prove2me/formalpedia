-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:52:40.448378+00:00
-- url     : https://prove2.me/submissions/0a14f5ba-6183-46c3-a7d8-c6bd74b4538b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorOpenCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_CharPerp_isOpen_perp
import Theorems.Thm_GlobalTheory_CompanionTheory_CharPerp_isCompact_perp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharPerp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharPerp
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) →
    IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧
      IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo
  exact ⟨isOpen_perp ψ hψ A hAc, isCompact_perp ψ hψ h1 A hAo⟩
end GlobalTheory.CompanionTheory.CharPerp
