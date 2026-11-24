-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CsStages.jhMult_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:33.630019+00:00
-- url     : https://prove2.me/submissions/aef4166a-ea2b-4e19-82e7-adeb60ab376a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JhMultMulLeOfSteps
import Theorems.Thm_GlobalTheory_JHMult_occurs_add
import Theorems.Thm_GlobalTheory_JHMult_occurs_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CsStages
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
namespace GlobalTheory.CompanionTheory.CsStages
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) :
    jhMult σ ρ₁ + jhMult σ ρ₂ ≤ jhMult σ ρ := by
  refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
  rw [← Nat.cast_add]
  exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl
end GlobalTheory.CompanionTheory.CsStages
