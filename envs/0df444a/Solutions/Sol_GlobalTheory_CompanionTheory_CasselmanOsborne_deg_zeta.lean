-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.deg_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:13:48.139921+00:00
-- url     : https://prove2.me/submissions/6e7f5d97-1390-4fc2-b2be-d7e6f8c9d2f9

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_zeta
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_deg_Fop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution (hG : GFacts) {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (u : ℂ) {x : Ch ε V}
    (hx : Deg j x) : Deg j (zeta ε (Fop ε E) u x) := by
  have := pres_zeta (R := (degSub ε V j).prod ⊤) ε (Fop ε E) (Fop ε E)
    (fun c d _ x y hxy => ⟨deg_Fop hG E c d hxy.1, trivial⟩) u x x ⟨hx, trivial⟩
  exact this.1
end GlobalTheory.CompanionTheory.CasselmanOsborne
