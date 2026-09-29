-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.pts_ofAlgAut_smul_eq_pts_comp_of_classifies_rigidify_pullback_curveChange_of_abelJacobi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/21bd04d2-3dff-5a70-98a2-480ec0164ee5

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_pts_ofAlgAut_smul_eq_pts_comp_of_classifies_rigidify_pullback_curveChange_of_abelJacobi
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups

theorem ptsCompat_standin_additive {J : Type*} [AddCommGroup J] (P : J → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hneg : ∀ x, P x → P (-x)) :
    ∃ S : AddSubgroup J, ∀ x, x ∈ S ↔ P x := by
  refine ⟨{ carrier := {x | P x}, add_mem' := fun {a b} ha hb => hadd a b ha hb, zero_mem' := h0, neg_mem' := fun {a} ha => hneg a ha }, fun x => Iff.rfl⟩

universe u

theorem PTSGEN_pullback_ofPoint_iso_of_graph_comp_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)]
    (cσ : pullback c t ⟶ pullback c t) [IsIso cσ] (ψ : T ⟶ T) [IsIso ψ]
    (y y' : T ⟶ C) (hy : y ≫ c = t) (hy' : y' ≫ c = t)
    (h : graphOver c y' hy' ≫ cσ = ψ ≫ graphOver c y hy) :
    Nonempty ((Scheme.Modules.pullback cσ).obj (RelEffCartierDiv.ofPoint c y hy).lineBundle ≅
        (RelEffCartierDiv.ofPoint c y' hy').lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback cσ).obj (RelEffCartierDiv.ofPoint c y hy).idealModule ≅
        (RelEffCartierDiv.ofPoint c y' hy').idealModule) := by
  have hp : (inv ψ ≫ graphOver c y' hy') ≫ cσ = graphOver c y hy := by
    rw [Category.assoc, h, IsIso.inv_hom_id_assoc]
  have hI : (graphOver c y hy).ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) _ (graphOver_snd c y hy)
  have hI' : (graphOver c y' hy').ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) _ (graphOver_snd c y' hy')
  have hI'' : (inv ψ ≫ graphOver c y' hy').ker.IsInvertible := by
    rw [Scheme.Hom.ker_comp_of_isIso]; exact hI'
  have key := AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    cσ (graphOver c y hy) (inv ψ ≫ graphOver c y' hy') hp hI hI'' 1
  rw [pow_one, pow_one, Scheme.Hom.ker_comp_of_isIso] at key
  exact key

theorem ptsCompat_generator
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsepQ : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})

    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))

    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)

    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule))

    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)

    (hpts_law : ∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (hAJ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (φ : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hφ : φ.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hφθ : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ φ.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (N : SchemeHomOver (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase)
    (hN₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange φ.hom hφ t)).obj (hD.poincare.pullbackAlong a).L)))
    (hN₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N))
    (hN₃ : (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).zeroSection ≫ N.1 = (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).zeroSection)
    (y s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hs : s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      Finsupp.single (𝔛.Meta.pointEquivPlace y) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1) :
    (O.pts (SemilinearAut.ofAlgAut θ • Pic0.mk Dv)).1 = (O.pts (Pic0.mk Dv)).1 ≫ N.1 := by
  classical

  haveI : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := hsepQ
  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD
  let S := SchemeHomOver (genPt p) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase
  letI : Mul S := ⟨Lw.mul (genPt p)⟩
  letI : One S := ⟨Lw.one (genPt p)⟩
  letI : Inv S := ⟨Lw.inv (genPt p)⟩
  letI grp : Group S := Group.ofLeftAxioms (fun a b c => Lw.mul_assoc (genPt p) a b c) (fun a => Lw.one_mul (genPt p) a)
    (fun a => Lw.inv_mul_cancel (genPt p) a)
  have hmul_def : ∀ a b : S, a * b = Lw.mul (genPt p) a b := fun _ _ => rfl
  let Nm : S →* S := MonoidHom.mk' (fun a => NeronModelInfra.schemeHomOverComp a N) (fun a b => hN₂ (genPt p) a b)
  have hNm : ∀ a : S, (Nm a).1 = a.1 ≫ N.1 := fun _ => rfl
  have hpts_mul : ∀ x y : JH M H, (O.pts (x + y) : S) = (O.pts x : S) * (O.pts y : S) := fun x y => hpts_law x y
  have hpts0 : (O.pts 0 : S) = 1 := by
    have h := hpts_mul 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hptsneg : ∀ x : JH M H, (O.pts (-x) : S) = (O.pts x : S)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hpts_mul, neg_add_cancel, hpts0])
  have hptssub : ∀ x y : JH M H, (O.pts (x - y) : S) = (O.pts x : S) * (O.pts y : S)⁻¹ := fun x y => by
    rw [sub_eq_add_neg, hpts_mul, hptsneg]

  let bar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → SchemeHomOver (genPt p) (toBase p (ΓM M H) hj) :=
    fun b => ⟨b.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p), by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, b.2,
        Category.id_comp]⟩
  let AJ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → S :=
    fun b => ⟨b.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, ← Category.assoc, b.2, Category.id_comp]⟩
  have hφinv : φ.inv ≫ (toBase p (ΓM M H) hj) = (toBase p (ΓM M H) hj) := by rw [Iso.inv_comp_eq]; exact hφ.symm
  let τ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} :=
    fun b => ⟨pullback.lift ((bar b).1 ≫ φ.inv) (𝟙 _) (by rw [Category.assoc, hφinv, (bar b).2, Category.id_comp]) ≫ inv 𝔛.eeta, by
      rw [Category.assoc, ← 𝔛.heeta, IsIso.inv_hom_id_assoc, pullback.lift_snd]⟩
  have hτbar : ∀ b, (bar (τ b)).1 = (bar b).1 ≫ φ.inv := by
    intro b
    show (pullback.lift ((bar b).1 ≫ φ.inv) (𝟙 _) _ ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  have hplτ : ∀ b, 𝔛.Meta.pointEquivPlace (τ b) = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace b := by
    intro b
    apply hφθ b (τ b)
    show (bar (τ b)).1 ≫ φ.hom = (bar b).1
    rw [hτbar, Category.assoc, Iso.inv_hom_id, Category.comp_id]

  let cσ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (genPt p) := curveChange φ.hom hφ (genPt p)
  have hΦP : ∀ z : S, Nonempty ((hD.poincare.pullbackAlong (Nm z)).L ≅ (Scheme.Modules.pullback cσ).obj (hD.poincare.pullbackAlong z).L) := by
    intro z
    obtain ⟨e2⟩ := hN₁ (genPt p) z
    obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field (ε := 𝔛.εinf) (genPt p)
      (L := (Scheme.Modules.pullback cσ).obj (hD.poincare.pullbackAlong z).L) ((hD.poincare.pullbackAlong z).isInvertible.pullback _)
    exact ⟨e2 ≪≫ e3⟩

  have hsndi : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd (toBase p (ΓM M H) hj) (genPt p) := by rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]
  haveI hsmQ : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) := by
    rw [← hsndi]; exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (inv 𝔛.eeta ≫ 𝔛.Meta.toBase))
  haveI := 𝔛.isProper
  haveI : IsSeparated (toBase p (ΓM M H) hj) := inferInstance
  haveI hcσiso : IsIso cσ := by
    show IsIso (curveChange φ.hom hφ (genPt p))
    unfold curveChange
    infer_instance

  have hgraph : ∀ b, graphOver (toBase p (ΓM M H) hj) (bar (τ b)).1 (bar (τ b)).2 ≫ cσ = 𝟙 _ ≫ graphOver (toBase p (ΓM M H) hj) (bar b).1 (bar b).2 := by
    intro b
    rw [Category.id_comp]
    apply pullback.hom_ext
    · show (graphOver (toBase p (ΓM M H) hj) (bar (τ b)).1 (bar (τ b)).2 ≫ curveChange φ.hom hφ (genPt p)) ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = graphOver (toBase p (ΓM M H) hj) (bar b).1 (bar b).2 ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p)
      simp only [graphOver, curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [hτbar, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · show (graphOver (toBase p (ΓM M H) hj) (bar (τ b)).1 (bar (τ b)).2 ≫ curveChange φ.hom hφ (genPt p)) ≫ pullback.snd (toBase p (ΓM M H) hj) (genPt p) = graphOver (toBase p (ΓM M H) hj) (bar b).1 (bar b).2 ≫ pullback.snd (toBase p (ΓM M H) hj) (genPt p)
      simp only [graphOver, curveChange, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

  have hOσ : ∀ b, Nonempty ((Scheme.Modules.pullback cσ).obj (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (bar b).1 (bar b).2).lineBundle ≅
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (bar (τ b)).1 (bar (τ b)).2).lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback cσ).obj (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (bar b).1 (bar b).2).idealModule ≅
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (bar (τ b)).1 (bar (τ b)).2).idealModule) := fun b =>
    PTSGEN_pullback_ofPoint_iso_of_graph_comp_eq (toBase p (ΓM M H) hj) (genPt p) cσ (𝟙 _) (bar b).1 (bar (τ b)).1 (bar b).2 (bar (τ b)).2 (hgraph b)

  have hI1 : ∀ b, Nonempty ((hD.poincare.pullbackAlong (AJ b)).L ≅
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (bar b).1 (bar b).2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ((genPt p) ≫ 𝔛.εinf.1)
          ((Category.assoc _ _ _).trans ((congrArg ((genPt p) ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _)))).idealModule) := by
    intro b
    exact ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
      p M H hpM hj 𝔛 (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)) hD hDQ ajQ kQ ajbar hpoinc hajcl hkQ₁ hkQ₂ hajbar b (bar b) rfl (AJ b) rfl

  have hkey2 : ∀ b b', Nm (AJ b) * AJ (τ b') = AJ (τ b) * Nm (AJ b') := by
    intro b b'
    apply hD.ext_of_iso (genPt p)
    obtain ⟨m1⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD
      (T := Over.mk (genPt p)) (schemeHomOverToOverHom (Nm (AJ b))) (schemeHomOverToOverHom (AJ (τ b')))
    obtain ⟨m2⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD
      (T := Over.mk (genPt p)) (schemeHomOverToOverHom (AJ (τ b))) (schemeHomOverToOverHom (Nm (AJ b')))
    obtain ⟨t1⟩ := hΦP (AJ b)
    obtain ⟨t2⟩ := hΦP (AJ b')
    obtain ⟨i1⟩ := hI1 b
    obtain ⟨i2⟩ := hI1 b'
    obtain ⟨i3⟩ := hI1 (τ b)
    obtain ⟨i4⟩ := hI1 (τ b')
    obtain ⟨o1⟩ := (hOσ b).1
    obtain ⟨o2⟩ := (hOσ b').1
    let Ob := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (bar (τ b)).1 (bar (τ b)).2).lineBundle
    let Ob' := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (bar (τ b')).1 (bar (τ b')).2).lineBundle
    let Iε := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ((genPt p) ≫ 𝔛.εinf.1)
          ((Category.assoc _ _ _).trans ((congrArg ((genPt p) ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _)))).idealModule
    let Iw := (Scheme.Modules.pullback cσ).obj Iε
    have eθb : (hD.poincare.pullbackAlong (Nm (AJ b))).L ≅ Ob ⊗ Iw :=
      t1 ≪≫ (Scheme.Modules.pullback cσ).mapIso i1 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o1 ⊗ᵢ Iso.refl _)
    have eθb' : (hD.poincare.pullbackAlong (Nm (AJ b'))).L ≅ Ob' ⊗ Iw :=
      t2 ≪≫ (Scheme.Modules.pullback cσ).mapIso i2 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o2 ⊗ᵢ Iso.refl _)
    have eL : (hD.poincare.pullbackAlong (Nm (AJ b) * AJ (τ b'))).L ≅ (Ob ⊗ Iw) ⊗ (Ob' ⊗ Iε) :=
      m1 ≪≫ (eθb ⊗ᵢ i4)
    have eR : (hD.poincare.pullbackAlong (AJ (τ b) * Nm (AJ b'))).L ≅ (Ob ⊗ Iε) ⊗ (Ob' ⊗ Iw) :=
      m2 ≪≫ (i3 ⊗ᵢ eθb')
    exact ⟨eL ≪≫ Scheme.Modules.tensorTensorTensorComm Ob Iw Ob' Iε ≪≫ (Iso.refl _ ⊗ᵢ β_ Iw Iε) ≪≫
      (Scheme.Modules.tensorTensorTensorComm Ob Iε Ob' Iw).symm ≪≫ eR.symm⟩

  have hAJs : AJ s = 1 := by
    obtain ⟨D0, hD0, hgp0⟩ := hAJ s s hs
    have h00 : Pic0.mk D0 = 0 := by
      have : D0 = 0 := Subtype.ext (by rw [hD0, sub_self]; rfl)
      rw [this]; rfl
    have : (O.pts (Pic0.mk D0) : S) = AJ s := Subtype.ext hgp0
    rw [← this, h00, hpts0]

  have hkey : ∀ b, Nm (AJ b) = AJ (τ b) * (AJ (τ s))⁻¹ := by
    intro b
    have hk := hkey2 b s
    rw [hAJs, map_one, mul_one] at hk
    rw [← hk, mul_inv_cancel_right]

  obtain ⟨Dv', hDv', hgp⟩ := hAJ y s hs
  obtain rfl : Dv = Dv' := Subtype.ext (hDv.trans hDv'.symm)
  obtain ⟨D1, hD1, hgp1⟩ := hAJ (τ y) s hs
  obtain ⟨D2, hD2, hgp2⟩ := hAJ (τ s) s hs
  have hA0 : (O.pts (Pic0.mk Dv) : S) = AJ y := Subtype.ext hgp
  have hA1 : (O.pts (Pic0.mk D1) : S) = AJ (τ y) := Subtype.ext hgp1
  have hA2 : (O.pts (Pic0.mk D2) : S) = AJ (τ s) := Subtype.ext hgp2

  have hsm : SemilinearAut.ofAlgAut θ • Pic0.mk Dv = Pic0.mk D1 - Pic0.mk D2 := by
    rw [AlgebraicCurve.SemilinearAut.pic0_smul_mk]
    have hcoe : AlgebraicCurve.SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut θ) Dv = D1 - D2 := by
      apply Subtype.ext
      rw [AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom, AddSubgroupClass.coe_sub, hD1, hD2, hDv, smul_sub,
        AlgebraicCurve.SemilinearAut.smul_single, AlgebraicCurve.SemilinearAut.smul_single, hplτ, hplτ]
      abel
    rw [hcoe]
    exact QuotientAddGroup.mk_sub _ D1 D2
  have hfin : (O.pts (SemilinearAut.ofAlgAut θ • Pic0.mk Dv) : S) = Nm (O.pts (Pic0.mk Dv)) := by
    rw [hsm, hptssub, hA1, hA2, hA0, hkey]
  exact congrArg Subtype.val hfin

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsepQ : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})

    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))

    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)

    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule))

    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)

    (hpts_law : ∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (hAJ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (φ : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hφ : φ.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hφθ : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ φ.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (N : SchemeHomOver (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase)
    (hN₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange φ.hom hφ t)).obj (hD.poincare.pullbackAlong a).L)))
    (hN₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N))
    (hN₃ : (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).zeroSection ≫ N.1 = (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).zeroSection) :
    ∀ x : JH M H, (O.pts (SemilinearAut.ofAlgAut θ • x)).1 = (O.pts x).1 ≫ N.1 := by
  classical

  let P : JH M H → Prop := fun x => (O.pts (SemilinearAut.ofAlgAut θ • x)).1 = (O.pts x).1 ≫ N.1

  let gens : Set (JH M H) := {x | ∃ (y s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ∧
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace y) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧ x = Pic0.mk Dv}
  have hgen : ∀ x ∈ gens, P x := by
    rintro _ ⟨y, s, hs, Dv, hDv, rfl⟩
    exact ptsCompat_generator p M H hpM hpM2 hHp hj 𝔛 A hA Λ O hD hDQ hsepQ ajQ kQ ajbar εbar hpoinc hajε hajcl hkQ₁ hkQ₂ hajbar hajbar_over hεbar hεbar_aj hpts_law hAJ φ hφ θ hφθ N hN₁ hN₂ hN₃ y s hs Dv hDv

  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD
  let S := SchemeHomOver (genPt p) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase
  letI : Mul S := ⟨Lw.mul (genPt p)⟩
  letI : One S := ⟨Lw.one (genPt p)⟩
  letI : Inv S := ⟨Lw.inv (genPt p)⟩
  letI grp : Group S := Group.ofLeftAxioms (fun a b c => Lw.mul_assoc (genPt p) a b c) (fun a => Lw.one_mul (genPt p) a)
    (fun a => Lw.inv_mul_cancel (genPt p) a)
  have hmul_def : ∀ a b : S, a * b = Lw.mul (genPt p) a b := fun _ _ => rfl
  let Nm : S →* S := MonoidHom.mk' (fun a => NeronModelInfra.schemeHomOverComp a N) (fun a b => hN₂ (genPt p) a b)
  have hNm : ∀ a : S, (Nm a).1 = a.1 ≫ N.1 := fun _ => rfl
  have hpts_mul : ∀ x y : JH M H, (O.pts (x + y) : S) = (O.pts x : S) * (O.pts y : S) := fun x y => hpts_law x y
  have hpts0 : (O.pts 0 : S) = 1 := by
    have h := hpts_mul 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hptsneg : ∀ x : JH M H, (O.pts (-x) : S) = (O.pts x : S)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hpts_mul, neg_add_cancel, hpts0])

  have hP_iff : ∀ x, P x ↔ (O.pts (SemilinearAut.ofAlgAut θ • x) : S) = Nm (O.pts x) := fun x =>
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hsm0 : SemilinearAut.ofAlgAut θ • (0 : JH M H) = 0 := smul_zero (M := ↥(AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) (A := JH M H) _
  have hsmadd : ∀ x y : JH M H, SemilinearAut.ofAlgAut θ • (x + y) = SemilinearAut.ofAlgAut θ • x + SemilinearAut.ofAlgAut θ • y :=
    fun x y => smul_add (M := ↥(AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) (A := JH M H) _ x y
  have hsmneg : ∀ x : JH M H, SemilinearAut.ofAlgAut θ • (-x) = -(SemilinearAut.ofAlgAut θ • x) := fun x => smul_neg (M := ↥(AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) (A := JH M H) _ x
  have h0 : P 0 := by
    rw [hP_iff, hsm0, hpts0, map_one]
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    intro x y hx hy
    rw [hP_iff] at hx hy ⊢
    rw [hsmadd, hpts_mul, hx, hy, ← map_mul, ← hpts_mul]
  have hneg : ∀ x, P x → P (-x) := by
    intro x hx
    rw [hP_iff] at hx ⊢
    rw [hsmneg, hptsneg, hx, ← map_inv, ← hptsneg]

  have htop : AddSubgroup.closure gens = ⊤ := by

    have h1 : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 := fun v =>
      ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (ΓM M H)
        (ModularCurve.translation_mem_GammaH M H) (xHFunctionField M H) rfl v
    rw [eq_top_iff]
    intro x _
    refine AddSubgroup.closure_mono ?_ (AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single h1 (𝔛.Meta.pointEquivPlace εbar) x)
    rintro _ ⟨V, hV, rfl⟩
    refine ⟨𝔛.Meta.pointEquivPlace.symm V, εbar, hεbar, ⟨_, hV⟩, ?_, rfl⟩
    simp only [Equiv.apply_symm_apply]
  obtain ⟨S, hS⟩ := ptsCompat_standin_additive P h0 hadd hneg
  have hle : AddSubgroup.closure gens ≤ S := (AddSubgroup.closure_le S).mpr (fun x hx => (hS x).mpr (hgen x hx))
  intro x
  have hx : x ∈ S := hle (htop ▸ AddSubgroup.mem_top x)
  exact (hS x).mp hx

end S_ModularCurve_JHNeronObjectAtP_pts_ofAlgAut_smul_eq_pts_comp_of_classifies_rigidify_pullback_curveChange_of_abelJacobi
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_pts_ofAlgAut_smul_eq_pts_comp_of_classifies_rigidify_pullback_curveChange_of_abelJacobi (solution)
