-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_pts_and_iterate_mul_eq_one_of_extendsToPlace_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/49537790-6028-5ab5-b664-d6325d2f67bd

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Theorems.Thm_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_pts_and_iterate_mul_eq_one_of_extendsToPlace_of_nsmul_eq_zero

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldBar JH qExpFunctionFieldC jqModC JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP XHDRLevel.R XHDRModelAtP"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "LevelData mk pts g pts_add separated G L"
namespace NsmulOneBody
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

theorem comp_iterate_mul_one_eq_comp_one {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {T T' : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    {J : Type*} [AddGroup J] (pts : J → SchemeHomOver t' f)
    (pts_add : ∀ x y : J, pts (x + y) = L.mul t' (pts x) (pts y))
    (σ : SchemeHomOver t f) (x : J) (hσ : ψ ≫ σ.1 = (pts x).1) (m : ℕ) (hm : m • x = 0) :
    ψ ≫ ((fun τ : SchemeHomOver t f => L.mul t τ σ)^[m] (L.one t)).1 = ψ ≫ (L.one t).1 := by
  letI : Group (SchemeHomOver t f) := L.pointGroup t
  letI : Group (SchemeHomOver t' f) := L.pointGroup t'
  let φ : SchemeHomOver t f →* SchemeHomOver t' f :=
    MonoidHom.mk' (GoodReductionJacobian.schemeHomOverComp ψ hψ) (L.mul_natural t t' ψ hψ)
  let π : Multiplicative J →* SchemeHomOver t' f :=
    MonoidHom.mk' (fun z => pts z.toAdd) (fun a b => pts_add a.toAdd b.toAdd)
  have hit : ∀ n : ℕ, (fun τ : SchemeHomOver t f => L.mul t τ σ)^[n] (L.one t) = σ ^ n := by
    intro n
    induction n with
    | zero => exact (pow_zero σ).symm
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ]
        rfl
  have hφσ : φ σ = π (Multiplicative.ofAdd x) := by
    apply Subtype.ext
    exact hσ
  have key : φ (σ ^ m) = φ 1 := by
    rw [map_pow, hφσ, ← map_pow, ← ofAdd_nsmul, hm, ofAdd_zero, map_one, map_one]
  have hval := congrArg Subtype.val key
  rw [← hit] at hval
  exact hval

end ModularCurve.JHNeronObjectAtP.NsmulOneBody

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_pts_and_iterate_mul_eq_one_of_extendsToPlace_of_nsmul_eq_zero.ModularCurve in

theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))

    (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hext : ExtendsToPlace Pl (Spec.map (CommRingCat.ofHom ρ)) (O.pts (AlgebraicCurve.Pic0.mk Dv)))
    (m : ℕ) (hm : m • AlgebraicCurve.Pic0.mk Dv = 0) :
    ∃ σ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g,
      barPt Pl ≫ σ.1 = (O.pts (AlgebraicCurve.Pic0.mk Dv)).1 ∧
      (fun τ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g =>
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ τ σ)^[m] ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _ := by
  obtain ⟨σ, hσ⟩ := hext
  refine ⟨σ, hσ.symm, ?_⟩
  haveI : IsSeparated O.g := O.separated
  have hψ : barPt Pl ≫ Spec.map (CommRingCat.ofHom ρ) = genPt p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have hgen := ModularCurve.JHNeronObjectAtP.NsmulOneBody.comp_iterate_mul_one_eq_comp_one
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD)
    (Spec.map (CommRingCat.ofHom ρ)) (genPt p) (barPt Pl) hψ (fun z : JH M H => O.pts z) hpts_law σ
    (AlgebraicCurve.Pic0.mk Dv) hσ.symm m hm
  apply Subtype.ext
  refine AlgebraicGeometry.IsSeparated.eq_of_spec_map_subtype_comp_eq O.g Pl _ _ hgen ?_
  exact (((fun τ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g =>
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ τ σ)^[m]
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _)).2).trans
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _).2.symm

end S_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_pts_and_iterate_mul_eq_one_of_extendsToPlace_of_nsmul_eq_zero
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_pts_and_iterate_mul_eq_one_of_extendsToPlace_of_nsmul_eq_zero (solution)
