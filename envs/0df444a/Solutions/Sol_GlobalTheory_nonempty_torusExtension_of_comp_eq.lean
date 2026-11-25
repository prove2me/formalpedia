-- Prove2me | solution 1 for GlobalTheory.nonempty_torusExtension_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:57:15.70525+00:00
-- url     : https://prove2.me/submissions/13362d01-182c-4e4b-b1d7-5f4447a5db61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteDvrTorusExtensionSpecialFibre
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
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {S S₁ S₂ : Scheme.{0}} {a : S₁ ⟶ S}
    {b : Spec (CommRingCat.of K) ⟶ S₁} {c : S₂ ⟶ S} {d : Spec (CommRingCat.of K) ⟶ S₂} (e : b ≫ a = d ≫ c)
    (G : Over S) [GrpObj G] (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback d).obj ((Over.pullback c).obj G))) := by
  obtain ⟨T⟩ := h
  haveI : IsMonHom (pullCompIso b a G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso b a G).inv)
  have h₁ : Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G)) := ⟨torusExtOfIso (pullCompIso b a G).symm T⟩
  rw [e] at h₁
  obtain ⟨T₁⟩ := h₁
  exact ⟨torusExtOfIso (pullCompIso d c G) T₁⟩
end GlobalTheory
