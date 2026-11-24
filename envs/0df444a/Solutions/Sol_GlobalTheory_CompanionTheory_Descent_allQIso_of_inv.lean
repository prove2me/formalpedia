-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.allQIso_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:01.193247+00:00
-- url     : https://prove2.me/submissions/2c25a031-7aa5-4e4e-9058-4d13eb52eca4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_d
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
variable {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution (hCx : CxSt) (m : CoefMap (RingHom.id R) F G) (m' : CoefMap (RingHom.id R) G F)
    (h : ∀ i z, pulln m' i (pulln m i z) = z) (h' : ∀ i z, pulln m i (pulln m' i z) = z) : AllQIso m := by
  refine ⟨⟨fun x _ ⟨y, hy⟩ ↦ ⟨0, ?_⟩, fun z hz ↦ ⟨pulln m' 0 z, 0, ?_, ?_⟩⟩, fun n ↦
    ⟨fun x _ ⟨y, hy⟩ ↦ ⟨pulln m' n y, ?_⟩, fun z hz ↦ ⟨pulln m' (n + 1) z, 0, ?_, ?_⟩⟩⟩
  · have : pulln m 0 x = 0 := by simpa using hy.symm
    have k := h 0 x
    rw [this, map_zero] at k
    simpa using k
  · rw [← pull_d hCx, hz, map_zero]
  · simp [h']
  · rw [← pull_d hCx, hy, h]
  · rw [← pull_d hCx, hz, map_zero]
  · simp [h']
end GlobalTheory.CompanionTheory.Descent
