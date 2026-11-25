-- Prove2me | solution 1 for GlobalTheory.Diag.isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:11:53.597951+00:00
-- url     : https://prove2.me/submissions/077563a4-7b42-46f6-b51b-3314b9bc1c90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory GlobalTheory.Diag
variable (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
omit [Module.Free ℤ X] [Module.Finite ℤ X]
namespace GlobalTheory.Diag
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (splitTorus S' X) (splitTorus S X) f
      ((baseChangeIso f X).inv.left ≫ pullback.fst (splitTorus S X).hom f) := by
  obtain ⟨h₁, h₂⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback (splitTorus S X) f
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · have : IsIso (baseChangeIso f X).inv.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (baseChangeIso f X).inv))
    have h : IsPullback (baseChangeIso f X).inv.left (splitTorus S' X).hom
        ((Over.pullback f).obj (splitTorus S X)).hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
    simpa using h.paste_horiz h₁
  · rw [h₂ T (x ≫ (baseChangeIso f X).inv) (y ≫ (baseChangeIso f X).inv) x₀ y₀
      (by rw [hx, Over.comp_left, Category.assoc]) (by rw [hy, Over.comp_left, Category.assoc]),
      ← MonObj.mul_comp, Over.comp_left, Category.assoc]
end GlobalTheory.Diag
