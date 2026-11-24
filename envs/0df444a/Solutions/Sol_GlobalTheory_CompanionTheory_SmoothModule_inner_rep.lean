-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.inner_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:24.650033+00:00
-- url     : https://prove2.me/submissions/b34f63ab-fedf-4e5a-a85a-055a29958752

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
namespace GlobalTheory.CompanionTheory.SmoothModule
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (v w : H) :
    ⟪σ g v, σ g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  (⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map v w
end GlobalTheory.CompanionTheory.SmoothModule
