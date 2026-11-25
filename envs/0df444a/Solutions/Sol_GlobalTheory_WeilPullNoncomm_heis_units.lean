-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.heis_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:38.197928+00:00
-- url     : https://prove2.me/submissions/5d87a2f3-7de1-4e36-a75d-fde3938beab2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
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
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]
namespace GlobalTheory.WeilPullNoncomm
theorem _root_.solution (S : Scheme.{0}) [IsAffine S] [IsReduced S] (u : Γ((heisObj S).left, ⊤)ˣ) :
    ∃ a : Γ(S, ⊤)ˣ, u = pullU (heisObj S).hom ⊤ a := by
  let e := AffineSpace.isoOfIsAffine (Fin 3) S
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  let ψ := (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 3) Γ(S, ⊤)))).inv ≫ e.hom.appTop
  have hψ : ψ = CommRingCat.ofHom (MvPolynomial.eval₂Hom ((𝔸(Fin 3; S) ↘ S).appTop).hom (AffineSpace.coord S)) := by
    show _ ≫ (AffineSpace.isoOfIsAffine (Fin 3) S).hom.appTop = _
    rw [AffineSpace.isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]
  let E := (asIso ψ).commRingCatIsoToRingEquiv
  obtain ⟨a, ha, h⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 (u.isUnit.map E.symm)
  refine ⟨ha.unit, Units.ext ?_⟩
  refine (E.apply_symm_apply _).symm.trans ((congrArg E h).trans ?_)
  show ψ.hom (MvPolynomial.C a) = _
  rw [hψ]
  exact MvPolynomial.eval₂Hom_C _ _ _
end GlobalTheory.WeilPullNoncomm
