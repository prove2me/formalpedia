-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.Nc_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:37.376281+00:00
-- url     : https://prove2.me/submissions/37ead6e5-c286-4a09-9967-474eaa4e1854

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_grpScheme_square_hom_ext_fst_snd
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_Nc_apply
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
theorem _root_.solution (hcl : Closed1 F = ⊤) (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (x : ⋀[R]^2 (Glob1 F)) : (Nc hcl x).1 = (0, 0, nu x) := by
  have e : (cechDeRhamTotalCocyclesTwo F).subtype ∘ₗ Nc hcl =
      LinearMap.inr R _ _ ∘ₗ LinearMap.inr R _ _ ∘ₗ nu := by
    refine grpScheme_square_hom_ext_fst_snd fun a b ↦ ?_
    simp only [LinearMap.comp_apply, Nc_apply, Submodule.subtype_apply, LinearMap.inr_apply]
    refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
    · simp [coe_cupZZ, cupTot_apply, cl_coe]
    · simp [coe_cupZZ, cupTot_a, cl_coe]
    · simp [coe_cupZZ, cupTot_η, cl_coe, hnu]
  exact LinearMap.congr_fun e x
end GlobalTheory.CompanionTheory.HypWedge
