-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_hom_mul_and_pts_diamondHBar_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/efd97365-36d6-5d4a-9ff1-1aab5ccd7764

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_curveChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
import Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_diamondHBar_eq_comp
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups

namespace DiaHomBody

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) : Divisor.degZero (K := K) (F := F) :=
  ⟨Finsupp.single P 1 - Finsupp.single Q₀ 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp⟩

@[scoped simp] theorem coe_gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) :
    (gen hdeg Q₀ P : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q₀ 1 := rfl

theorem closure_range_mk_gen_eq_top (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F) :
    AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) = ⊤ := by
  classical
  set S := AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) with hS

  let θ : Divisor K F →+ Divisor K F :=
    AddMonoidHom.id _ - (zmultiplesHom (Divisor K F) (Finsupp.single Q₀ 1)).comp Divisor.degree
  have hθ : ∀ E : Divisor K F, θ E = E - Divisor.degree E • Finsupp.single Q₀ 1 := fun E => by
    simp [θ]
  have hθmem : ∀ E : Divisor K F, θ E ∈ Divisor.degZero (K := K) (F := F) := by
    intro E
    rw [Divisor.mem_degZero, hθ, map_sub, map_zsmul, Divisor.degree_single, hdeg]
    simp
  let ψ : Divisor K F →+ Pic0 K F := (QuotientAddGroup.mk' _).comp (θ.codRestrict _ hθmem)
  have hψ : ∀ E : Divisor K F, ψ E = Pic0.mk ⟨θ E, hθmem E⟩ := fun E => rfl
  have hψS : ∀ E : Divisor K F, ψ E ∈ S := by
    intro E
    induction E using Finsupp.induction with
    | zero => rw [map_zero]; exact S.zero_mem
    | single_add a b f _ _ ih =>
      rw [map_add]
      refine S.add_mem ?_ ih
      have h1 : ψ (Finsupp.single a 1) = Pic0.mk (gen hdeg Q₀ a) := by
        rw [hψ]; congr 1; apply Subtype.ext
        simp only [coe_gen, hθ, Divisor.degree_single, hdeg, Nat.cast_one, mul_one, one_smul]
      have hb : Finsupp.single a b = b • Finsupp.single a (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hb, map_zsmul, h1]
      exact S.zsmul_mem (AddSubgroup.subset_closure ⟨a, rfl⟩) b
  rw [eq_top_iff]
  rintro c -
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  have hD : Pic0.mk D = ψ (D : Divisor K F) := by
    rw [hψ]; congr 1; apply Subtype.ext
    simp only [hθ, (Divisor.mem_degZero.mp D.2), zero_smul, sub_zero]
  rw [hD]; exact hψS _

theorem addMonoidHom_ext_of_gen {G : Type*} [AddGroup G] (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F)
    {f g : Pic0 K F →+ G} (h : ∀ P : Place K F, f (Pic0.mk (gen hdeg Q₀ P)) = g (Pic0.mk (gen hdeg Q₀ P))) :
    f = g :=
  AddMonoidHom.eq_of_eqOn_dense (closure_range_mk_gen_eq_top hdeg Q₀) (by rintro _ ⟨P, rfl⟩; exact h P)

theorem gen_sub_gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P P' : Place K F) :
    gen hdeg Q₀ P - gen hdeg Q₀ P' = gen hdeg P' P :=
  Subtype.ext (by rw [AddSubgroupClass.coe_sub, coe_gen, coe_gen, coe_gen, sub_sub_sub_cancel_right])

end Generic

theorem deg_eq_one_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : v.deg = 1 := by
  have hle : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
    intro A hA
    rw [CongruenceSubgroup.Gamma1_mem] at hA
    obtain ⟨-, h11, h10⟩ := hA
    have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
    have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
      apply Units.ext
      rw [CohCarrier.val_gamma0Units, Units.val_one]
      exact h11
    rw [this]; exact one_mem _
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ)
    (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H) (xHFunctionField M H) rfl v

set_option maxHeartbeats 3200000 in

theorem core (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)
    (ω : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hω : ω.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    {DX : Scheme.{0}} (dD : DX ⟶ Spec (CommRingCat.of (R p)))
    (mulD : SchemeHomOver (genPt p) dD → SchemeHomOver (genPt p) dD → SchemeHomOver (genPt p) dD)
    (ajbar : 𝔛.Meta.C ⟶ DX) (hajbar_over : ajbar ≫ dD = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (pts : JH M H ≃ SchemeHomOver (genPt p) dD)
    (hpts_add : ∀ x y : JH M H, pts (x + y) = mulD (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) (↥(xHFunctionFieldBar M H))) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (σ : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (d : SchemeHomOver dD dD)
    (hdhom : ∀ x y : SchemeHomOver (genPt p) dD,
      schemeHomOverComp (mulD x y) d = mulD (schemeHomOverComp x d) (schemeHomOverComp y d))

    (hplace : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ ω.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) →
      𝔛.Meta.pointEquivPlace y' = σ • 𝔛.Meta.pointEquivPlace y)

    (hone : ∀ (y y' ε' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ ω.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) →
      ε'.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ ω.hom = εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) →
      ∀ (a b c : SchemeHomOver (genPt p) dD),
        a.1 = (y.1 ≫ ajbar) ≫ d.1 → b.1 = ε'.1 ≫ ajbar → c.1 = y'.1 ≫ ajbar → mulD a b = c) :
    ∀ X : JH M H, (pts (σ • X)).1 = (pts X).1 ≫ d.1 := by
  classical
  haveI := 𝔛.eeta_iso

  have hinv : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd (toBase p (ΓM M H) hj) (genPt p) := by
    rw [IsIso.inv_comp_eq, 𝔛.heeta]
  have hwinv : ω.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
    rw [Iso.inv_comp_eq, hω]
  let under : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} := fun y =>
    ⟨pullback.lift (y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ ω.inv)
        (y.1 ≫ 𝔛.eeta ≫ pullback.snd (toBase p (ΓM M H) hj) (genPt p))
        (by simp only [Category.assoc, hwinv]; rw [pullback.condition]) ≫ inv 𝔛.eeta, by
      rw [Category.assoc, hinv, pullback.lift_snd, 𝔛.heeta, y.2]⟩
  have hunder : ∀ y, (under y).1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ ω.hom =
      y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) := by
    intro y; simp only [under, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id]

  let Φ : JH M H → JH M H := fun X => pts.symm (schemeHomOverComp (pts X) d)
  have hΦ : ∀ X, pts (Φ X) = schemeHomOverComp (pts X) d := fun X => pts.apply_symm_apply _
  have hΦadd : ∀ X Y, Φ (X + Y) = Φ X + Φ Y := by
    intro X Y; apply pts.injective
    rw [hpts_add, hΦ, hΦ, hΦ, hpts_add, hdhom]
  let Φh : JH M H →+ JH M H := AddMonoidHom.mk' Φ hΦadd
  suffices hfun : DistribMulAction.toAddMonoidHom (JH M H) σ = Φh by
    intro X
    have h1 : σ • X = Φ X := DFunLike.congr_fun hfun X
    rw [h1]; show (pts (Φ X)).1 = _; rw [hΦ]; rfl

  have hdeg := deg_eq_one_xHFunctionFieldBar M H
  refine addMonoidHom_ext_of_gen hdeg (𝔛.Meta.pointEquivPlace εbar) fun P => ?_
  obtain ⟨y, hPy⟩ := 𝔛.Meta.pointEquivPlace.surjective P
  subst hPy
  set y' := under y with hy'
  set ε' := under εbar with hε'

  obtain ⟨Dy, hDy, hptsDy⟩ := hpts_aj y εbar hεbar
  obtain ⟨Dy', hDy', hptsDy'⟩ := hpts_aj y' εbar hεbar
  obtain ⟨Dε', hDε', hptsDε'⟩ := hpts_aj ε' εbar hεbar
  have hgen : gen hdeg (𝔛.Meta.pointEquivPlace εbar) (𝔛.Meta.pointEquivPlace y) = Dy := Subtype.ext (by rw [coe_gen, hDy])

  have hsmul : σ • Pic0.mk (gen hdeg (𝔛.Meta.pointEquivPlace εbar) (𝔛.Meta.pointEquivPlace y)) = Pic0.mk (Dy' - Dε') := by
    rw [SemilinearAut.pic0_smul_mk]
    congr 1
    apply Subtype.ext
    rw [SemilinearAut.coe_degZeroSMulHom, coe_gen, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single,
      ← hplace y y' (hunder y), ← hplace εbar ε' (hunder εbar), AddSubgroupClass.coe_sub, hDy', hDε',
      sub_sub_sub_cancel_right]

  let a : SchemeHomOver (genPt p) dD :=
    schemeHomOverComp (⟨y.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, reassoc_of% y.2]⟩ : SchemeHomOver (genPt p) dD) d
  have hmul : mulD a (pts (Pic0.mk Dε')) = pts (Pic0.mk Dy') :=
    hone y y' ε' (hunder y) (hunder εbar) a _ _ rfl hptsDε' hptsDy'

  have hkey : pts (Pic0.mk (Dy' - Dε')) = a := by
    have h1 : pts (Pic0.mk (Dy' - Dε') + Pic0.mk Dε') = pts (pts.symm a + Pic0.mk Dε') := by
      rw [← Pic0.mk_add, sub_add_cancel, hpts_add, Equiv.apply_symm_apply, hmul]
    have h2 := add_right_cancel (pts.injective h1)
    rw [h2, Equiv.apply_symm_apply]

  show σ • Pic0.mk _ = Φ _
  apply pts.injective
  rw [hΦ, hsmul, hkey]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, hgen, hptsDy]

set_option maxHeartbeats 3200000 in

theorem onePoint
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)
    (ω : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hω : ω.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)
    (φ : SchemeHomOver D.toBase D.toBase)
    (hφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a φ)).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
          ((Scheme.Modules.pullback (curveChange ω.hom hω t)).obj (hD.poincare.pullbackAlong a).L)))
    (y y' ε' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hy' : y'.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ ω.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hε' : ε'.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ ω.hom = εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (a b c : SchemeHomOver (genPt p) D.toBase)
    (ha : a.1 = (y.1 ≫ ajbar) ≫ φ.1) (hb : b.1 = ε'.1 ≫ ajbar) (hc : c.1 = y'.1 ≫ ajbar) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul (genPt p) a b = c := by
  haveI : IsSeparated (toBase p (ΓM M H) hj) := inferInstance
  haveI : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := by
    unfold baseChange; infer_instance

  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) := by
    haveI := 𝔛.eeta_iso
    have e : pullback.snd (toBase p (ΓM M H) hj) (genPt p) = inv 𝔛.eeta ≫ 𝔛.Meta.toBase := by
      rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]
    rw [e]; exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  let bar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} →
      SchemeHomOver (genPt p) (toBase p (ΓM M H) hj) := fun z =>
    ⟨z.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p), by
      simp only [Category.assoc, pullback.condition]; rw [reassoc_of% 𝔛.heeta, reassoc_of% z.2]⟩
  have hbar : ∀ z, (bar z).1 = z.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) := fun z => rfl
  have hy'bar : (bar y').1 ≫ ω.hom = (bar y).1 := by
    rw [hbar, hbar]; simp only [Category.assoc]; exact hy'
  have hε'bar : (bar ε').1 ≫ ω.hom = genPt p ≫ 𝔛.εinf.1 := by
    rw [hbar]; simp only [Category.assoc]; rw [hε', hεbar]

  let a' : SchemeHomOver (genPt p) D.toBase := ⟨y.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, reassoc_of% y.2]⟩
  have haa' : a = NeronModelInfra.schemeHomOverComp a' φ := Subtype.ext (by rw [ha]; rfl)

  have ha' := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    p M H hpM hj 𝔛 D hD hDQ ajQ kQ ajbar hPQ hajQ hkQ₁ hkQ₂ hajbar y (bar y) rfl a' rfl
  have hb' := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    p M H hpM hj 𝔛 D hD hDQ ajQ kQ ajbar hPQ hajQ hkQ₁ hkQ₂ hajbar ε' (bar ε') rfl b hb
  have hc' := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    p M H hpM hj 𝔛 D hD hDQ ajQ kQ ajbar hPQ hajQ hkQ₁ hkQ₂ hajbar y' (bar y') rfl c hc
  rw [haa']
  exact RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
    hD hD ω.hom hω φ (fun t a => hφ t a) (genPt p) (bar y) (bar y') (bar ε') hy'bar hε'bar a' ha' b c hb' hc'

end DiaHomBody
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_diamondHBar_eq_comp.DiaHomBody"

open DiaHomBody in
set_option maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    (d : (ZMod M)ˣ) :
    ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JH M H, (pts (diamondHBar M H d x)).1 = (pts x).1 ≫ φ.1 := by
  haveI := 𝔛.eeta_iso

  have hdinv : (𝔛.dia d).symm.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, 𝔛.dia_over]

  obtain ⟨φ, hpin, hhom, -⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_pullback_curveChange
      (ε := 𝔛.εinf) (ε' := 𝔛.εinf) (𝔛.dia d).symm.hom hdinv hD hD
  refine ⟨φ, fun s x y => hhom s x y, ?_⟩

  intro x
  rw [diamondHBar_apply]
  refine core p M H hpM hj 𝔛 (𝔛.dia d).symm hdinv D.toBase
    (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ x y)
    ajbar hajbar_over εbar pts hpts_add hpts_aj hεbar
    (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) φ (fun x y => hhom (genPt p) x y) ?_ ?_ x
  ·
    intro y y' h
    refine 𝔛.dia_generic d y y' ?_
    have h' := congrArg (· ≫ (𝔛.dia d).hom) h
    simpa only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id] using h'
  ·
    intro y y' ε' hy' hε' a b c ha hb hc
    exact onePoint p M H hpM hj 𝔛 (𝔛.dia d).symm hdinv D hD hDQ hPQ ajQ hajQε hajQ kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over
      εbar hεbar hεbar_aj φ (fun t a => hpin t a) y y' ε' hy' hε' a b c ha hb hc

end S_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_diamondHBar_eq_comp
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_diamondHBar_eq_comp (solution)
