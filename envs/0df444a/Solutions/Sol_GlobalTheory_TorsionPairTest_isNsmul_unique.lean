-- Prove2me | solution 1 for GlobalTheory.TorsionPairTest.isNsmul_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:09.21795+00:00
-- url     : https://prove2.me/submissions/2aa64424-26cd-4a6f-9a46-3178cdde2ebc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty
import Theorems.Thm_GlobalTheory_TorsionPairTest_ext_val
import Theorems.Thm_GlobalTheory_TorsionPairTest_isAdd_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionPairTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
namespace GlobalTheory.TorsionPairTest
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} {k : ℕ} {g a a' : GtPt D T} (h : GtPt.IsNsmul k g a)
    (h' : GtPt.IsNsmul k g a') : a = a' := by
  obtain ⟨u, u0, us, rfl⟩ := h
  obtain ⟨v, v0, vs, rfl⟩ := h'
  have : ∀ i, u i = v i := fun i => by
    induction i using Fin.induction with
    | zero => exact ext_val (u0.1.trans v0.1.symm) fun χ _ _ hJ =>
        (Geo.Tor.val_corr hJ (u0.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (v0.2 χ) (𝟙 _)).symm
    | succ i ih => exact isAdd_unique (us i) (ih ▸ vs i)
  exact this _
end GlobalTheory.TorsionPairTest
