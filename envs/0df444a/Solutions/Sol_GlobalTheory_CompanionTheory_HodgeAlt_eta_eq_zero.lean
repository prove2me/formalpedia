-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.eta_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:44.662803+00:00
-- url     : https://prove2.me/submissions/c5ca46ed-82af-4f34-b9f5-578021d48303

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_of_dTot1
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (hc : Closed1 F = ⊤) (hs : Function.Surjective (toO F)) (e : Tot1 F) (w : W0 F 2)
    (h : dTot1 F e = ((0 : C2 F), (0 : A1 F), w)) : w = 0 := by
  obtain ⟨β, h1, h2⟩ := exists_of_dTot1 hs e 0 w h
  have hβ : β ∈ Glob1 F := fun T T' φ ↦ by
    have := h1 T T' φ
    exact sub_eq_zero.1 this.symm
  have hcl : (⟨β, hβ⟩ : Glob1 F) ∈ Closed1 F := hc ▸ Submodule.mem_top
  funext T
  rw [h2 T]
  exact hcl T
end GlobalTheory.CompanionTheory.HodgeAlt
