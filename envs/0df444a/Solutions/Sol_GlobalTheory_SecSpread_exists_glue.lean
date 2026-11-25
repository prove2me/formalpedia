-- Prove2me | solution 1 for GlobalTheory.SecSpread.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:44:22.631401+00:00
-- url     : https://prove2.me/submissions/0198f9c2-c88f-4cd5-836e-dc36a601b493

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_GlobalTheory_SecSpread_ext_generic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
namespace GlobalTheory.SecSpread
theorem _root_.solution (H : IsPullback φ π p (spMap (algebraMap R K))) [Flat p] (W : X.Opens)
    (t : ∀ z : X', X'.presheaf.stalk z)
    (h : ∀ x ∈ W, ∃ (U : X.Opens) (_ : U ≤ W) (_ : x ∈ U) (a : Γ(X, U)), ∀ z, φ z ∈ U → gs φ z U a = t z) :
    ∃ θ : Γ(X, W), ∀ z, φ z ∈ W → gs φ z W θ = t z := by
  choose U hU hx a ha using fun x : W => h x.1 x.2
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' U W (fun i => homOfLE (hU i))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) a (fun i j => ext_generic H (W := U i ⊓ U j) fun z hz =>
      (gs_res φ z inf_le_left hz _).trans (((ha i z hz.1).trans (ha j z hz.2).symm).trans
        (gs_res φ z inf_le_right hz _).symm))
  refine ⟨s, fun z hz => ?_⟩
  exact (gs_res φ z (hU ⟨_, hz⟩) (hx _) s).symm.trans
    ((congrArg (gs φ z _) (hs ⟨_, hz⟩)).trans (ha _ z (hx _)))
end GlobalTheory.SecSpread
