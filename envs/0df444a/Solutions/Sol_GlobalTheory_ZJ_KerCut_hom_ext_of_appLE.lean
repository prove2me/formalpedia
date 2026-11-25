-- Prove2me | solution 1 for GlobalTheory.ZJ.KerCut.hom_ext_of_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:22.509862+00:00
-- url     : https://prove2.me/submissions/e8796d52-c0fa-4ee3-80d4-a8cf25e23cba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfTorusBased
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitChartsTorusExtensionOverFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TorusCutByInvariantRatiosField
import Theorems.Thm_GlobalTheory_FunDescent_res_bijective
import Theorems.Thm_GlobalTheory_FunDescent_res_comp_appTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.KerCut
namespace GlobalTheory.ZJ.KerCut
theorem _root_.solution {X Y : Scheme.{0}} (V : X.Opens) (hV : IsAffineOpen V) (f g : Y ⟶ X)
    (hf : ⊤ ≤ f ⁻¹ᵁ V) (hg : ⊤ ≤ g ⁻¹ᵁ V) (e : f.appLE V ⊤ hf = g.appLE V ⊤ hg) : f = g := by
  have : IsAffine V.toScheme := hV
  have r : ∀ (f : Y ⟶ X), ⊤ ≤ f ⁻¹ᵁ V → ∃ f' : Y ⟶ V.toScheme, f = f' ≫ V.ι := by
    intro f hf
    refine ⟨IsOpenImmersion.lift V.ι f ?_, (IsOpenImmersion.lift_fac _ _ _).symm⟩
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hf (show y ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨f', ef⟩ := r f hf
  obtain ⟨g', eg⟩ := r g hg
  rw [← GlobalTheory.FunDescent.res_comp_appTop V f' f ef, ← GlobalTheory.FunDescent.res_comp_appTop V g' g eg] at e
  have : f' = g' := by
    apply ext_of_isAffine
    ext x
    obtain ⟨y, rfl⟩ := (GlobalTheory.FunDescent.res_bijective V).2 x
    exact congrArg (fun ψ => ψ.hom y) e
  rw [ef, eg, this]
end GlobalTheory.ZJ.KerCut
