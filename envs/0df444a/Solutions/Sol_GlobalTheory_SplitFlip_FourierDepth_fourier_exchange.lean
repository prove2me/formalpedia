-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.fourier_exchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:00.939229+00:00
-- url     : https://prove2.me/submissions/b22e102a-dc2c-4fde-8608-36bcaccef6d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_hasDepth_fourierSum
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_isNatDatum_invFourierSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise
noncomputable section
namespace GlobalTheory.SplitFlip.FourierDepth
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) :
    (∀ Φ : Matrix A D k → ℂ, IsNatDatum ϖ e Φ → HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ)) ∧
      ∀ Ψ : Matrix A D k → ℂ, HasDepth ϖ e (blockLat ϖ e P) Ψ → IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) :=
  ⟨fun _ h => hasDepth_fourierSum hϖ hψ e P h, fun _ h => isNatDatum_invFourierSum hϖ hψ e P h⟩
end GlobalTheory.SplitFlip.FourierDepth
