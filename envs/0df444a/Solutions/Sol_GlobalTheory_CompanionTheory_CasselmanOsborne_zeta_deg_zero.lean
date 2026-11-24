-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.zeta_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:13:51.796129+00:00
-- url     : https://prove2.me/submissions/e511330a-2e4a-4b89-a349-04627105da45

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_zeta
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_deg_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_Gop_deg_zero
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (u : ℂ) {x : Ch ε V}
    (hx : Deg 0 x) : zeta ε (Fop ε E) u x ∅ = zeta ε E u (x ∅) := by
  have := pres_zeta (R := (degSub ε V 0).prod ⊤ ⊓ (LinearMap.proj (R := ℂ) (φ := fun _ => V) ∅).graph)
    ε (Fop ε E) E (fun c d _ x y hxy => by
      have h1 : Deg 0 x := hxy.1.1
      have h2 : y = x ∅ := by simpa using hxy.2
      have h3 : Fop ε E c d x = lift ε (E c d) x := by simp [Fop, Gop_deg_zero c d h1]
      refine ⟨⟨?_, trivial⟩, ?_⟩
      · rw [h3]; exact deg_lift _ h1
      · simp [h3, h2]) u x (x ∅) ⟨⟨hx, trivial⟩, by simp⟩
  have h := this.2
  simpa using Eq.symm h
end GlobalTheory.CompanionTheory.CasselmanOsborne
