-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmBracket.smBracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:52.646854+00:00
-- url     : https://prove2.me/submissions/c51e2699-a609-467b-aaee-f633d529cf41

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExt
import Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_lie_bracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_ds_bracket
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_Formalism_REAL_exp_indefinite_unitary_holds
import Theorems.Thm_Formalism_REAL_indefinite_unitary_mul_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmBracket
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace GlobalTheory.CompanionTheory.SmBracket
theorem _root_.solution : CompanionTheory.D.DSIC.SmBracket := by
  intro n ε H _ _ σ hσ X Y hX hY v hv
  have h : RepOn (UJset ε) σ :=
    ⟨by simp [UJset, PI.UpqRep.inUJ], fun a ha b hb => Formalism.REAL.indefinite_unitary_mul_mem ε ha hb, hσ.1.1, hσ.1.2⟩
  have hex : ∀ Z, inG ε Z → ∀ t, ex Z t ∈ UJset ε := fun Z hZ t => Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t
  exact ds_bracket h (hex X hX) (hex Y hY) (hex _ (lie_bracket hX hY)) hv
end GlobalTheory.CompanionTheory.SmBracket
