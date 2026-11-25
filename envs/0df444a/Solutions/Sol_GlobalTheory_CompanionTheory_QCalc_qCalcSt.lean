-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QCalc.qCalcSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:44.423112+00:00
-- url     : https://prove2.me/submissions/18247d7d-d248-46a9-9f07-be040db15340

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QIsoAtRight
import Theorems.Thm_GlobalTheory_CompanionTheory_QCalc_qIsoAt_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_QCalc_qIsoAt_right
import Theorems.Thm_GlobalTheory_CompanionTheory_QCalc_qIsoAt_left
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QCalc
namespace GlobalTheory.CompanionTheory.QCalc
theorem _root_.solution : CxSt → QCalcSt := by
  intro hCx R _ C _ F D E _ _ G H m n k hk
  have cm : ∀ i x, pulln m (i + 1) (dn F i x) = dn G i (pulln m i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R C F).2 D G m i) x
  have cn : ∀ i x, pulln n (i + 1) (dn G i x) = dn H i (pulln n i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R D G).2 E H n i) x
  have zf : ∀ x : R, pulln m 0 ((0 : R →ₗ[R] Cn F 0) x) =
      (0 : R →ₗ[R] Cn G 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  have zg : ∀ x : R, pulln n 0 ((0 : R →ₗ[R] Cn G 0) x) =
      (0 : R →ₗ[R] Cn H 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  refine ⟨fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · exact qIsoAt_comp (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_comp (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_right zf (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_right (cm i) (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_left (cm 0) zg (cn 0) (hk 0) h₁.1 h₂.1
  · exact qIsoAt_left (cm (i + 1)) (cn i) (cn (i + 1)) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
end GlobalTheory.CompanionTheory.QCalc
