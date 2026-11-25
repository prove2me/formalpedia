-- Prove2me | solution 1 for GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:39.466261+00:00
-- url     : https://prove2.me/submissions/84c95acf-bb16-410a-893f-facdda5d52ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitianStatement
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_exists_osc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧ (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧ ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f → (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) → Ω g f = dP s (m g) • f := by
  first | exact @GlobalTheory.RealWeil.UnitaryOsc.exists_osc | exact GlobalTheory.RealWeil.UnitaryOsc.exists_osc | (intros; apply GlobalTheory.RealWeil.UnitaryOsc.exists_osc <;> assumption)
end _root_.GlobalTheory.T
