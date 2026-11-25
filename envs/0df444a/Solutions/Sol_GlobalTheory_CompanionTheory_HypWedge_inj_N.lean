-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.inj_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:26.383811+00:00
-- url     : https://prove2.me/submissions/9c0de31b-4f31-4a7f-ba63-29f8eccc55b3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_key_D
import Theorems.Thm_GlobalTheory_CatCoh_commAlgFunctorCocyclesOne_eq_ker
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (hs : Function.Surjective (toO F)) (hcl : Closed1 F = ⊤) (c : Tot1 F) (w : W0 F 2)
    (hc : dTot1 F c = (0, 0, w)) : w = 0 := by
  have hz : d1 F c.1 = 0 := congrArg Prod.fst hc
  have hf : c.1 ∈ Z1 F := by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hz
  obtain ⟨β, hβ, hβc⟩ := key_D hs c.1 hf
  let g0 : Glob1 F := ⟨c.2 - β, fun T T' φ ↦ by
    have h : c.2 T' - p1 F φ (c.2 T) - D R _ (c.1 T T' φ) = 0 :=
      congrArg (fun y : Tot2 F ↦ y.2.1 T T' φ) hc
    rw [hβ] at h
    simp only [Pi.sub_apply, map_sub]
    rw [← sub_eq_zero, ← h]
    abel⟩
  have hg0 : g0 ∈ Closed1 F := hcl ▸ Submodule.mem_top
  funext T
  have h : dOne R _ (c.2 T) = w T := congrArg (fun y : Tot2 F ↦ y.2.2 T) hc
  have h2 : dOne R _ (c.2 T - β T) = 0 := hg0 T
  rw [map_sub, hβc, sub_zero, h] at h2
  exact h2
end GlobalTheory.CompanionTheory.HypWedge
