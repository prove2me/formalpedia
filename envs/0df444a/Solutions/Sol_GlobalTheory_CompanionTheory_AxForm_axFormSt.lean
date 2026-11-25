-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.axFormSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:33:59.011999+00:00
-- url     : https://prove2.me/submissions/d1ee29f4-b361-4e27-a4c4-2e0310de7c8b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_vanish_at
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_smooth_sq
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_AbelianSchemeGerms_isAbelianScheme_tensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution : CotSt → SteinSt → ParSt → AxFormSt := by
  intro _ _ hP R _ A _ g hA hs c h1 h2
  have hPar := (hP R (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_sq A g hs)).1
  by_contra hc
  have hI : (R ∙ c).annihilator ≠ ⊤ := fun h ↦ hc (by
    have := (Submodule.mem_annihilator_span_singleton c 1).1 (h ▸ Submodule.mem_top)
    simpa using this)
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨r, hr, hrc⟩ := vanish_at A hPar c h1 h2 p
  exact hr (hle ((Submodule.mem_annihilator_span_singleton c r).2 hrc))
end GlobalTheory.CompanionTheory.AxForm
