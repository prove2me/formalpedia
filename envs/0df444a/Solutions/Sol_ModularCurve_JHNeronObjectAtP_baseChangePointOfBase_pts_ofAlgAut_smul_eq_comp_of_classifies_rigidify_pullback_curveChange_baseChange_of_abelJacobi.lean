-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.baseChangePointOfBase_pts_ofAlgAut_smul_eq_comp_of_classifies_rigidify_pullback_curveChange_baseChange_of_abelJacobi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a2f07a34-80fa-508b-a284-4aea5d1f3c7f

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

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_baseChangePointOfBase_pts_ofAlgAut_smul_eq_comp_of_classifies_rigidify_pullback_curveChange_baseChange_of_abelJacobi
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups

theorem ptsCompatA_standin_additive {J : Type*} [AddCommGroup J] (P : J → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hneg : ∀ x, P x → P (-x)) :
    ∃ S : AddSubgroup J, ∀ x, x ∈ S ↔ P x := by
  refine ⟨{ carrier := {x | P x}, add_mem' := fun {a b} ha hb => hadd a b ha hb, zero_mem' := h0, neg_mem' := fun {a} ha => hneg a ha }, fun x => Iff.rfl⟩

universe u

theorem PTSGENA_pullback_ofPoint_iso_of_graph_comp_eq
    {R R' : Type u} [CommRing R] [CommRing R'] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c] (c' : C' ⟶ Spec (CommRingCat.of R')) [IsSeparated c']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T ⟶ Spec (CommRingCat.of R'))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)] [SmoothOfRelativeDimension 1 (pullback.snd c' t')]
    (ι : pullback c' t' ⟶ pullback c t) [IsIso ι]
    (y : T ⟶ C) (y' : T ⟶ C') (hy : y ≫ c = t) (hy' : y' ≫ c' = t')
    (h : graphOver c' y' hy' ≫ ι = graphOver c y hy) :
    Nonempty ((Scheme.Modules.pullback ι).obj (RelEffCartierDiv.ofPoint c y hy).lineBundle ≅
        (RelEffCartierDiv.ofPoint c' y' hy').lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback ι).obj (RelEffCartierDiv.ofPoint c y hy).idealModule ≅
        (RelEffCartierDiv.ofPoint c' y' hy').idealModule) := by
  have hI : (graphOver c y hy).ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) _ (graphOver_snd c y hy)
  have hI' : (graphOver c' y' hy').ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' t') _ (graphOver_snd c' y' hy')
  have key := AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    ι (graphOver c y hy) (graphOver c' y' hy') h hI hI' 1
  rw [pow_one, pow_one] at key
  exact key

namespace PTSGENA_BaseChange

open AlgebraicGeometry.RelPicard.BaseChange

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']

noncomputable def ofR_pullbackAlong_iso {T T'' : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {t'' : T'' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t'' t')
    (X : RigidifiedLineBundle c ε (t' ≫ specMap R R')) :
    ((ofR c ε R' X).pullbackAlong ψ).L ≅ (ofR c ε R' (X.pullbackAlong (overR R' ψ))).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd (baseChange R c R') ψ) (κ c R' t').hom).app X.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_κ_hom c R' ψ)).app X.L ≪≫
    ((Scheme.Modules.pullbackComp (κ c R' t'').hom (baseChangeSnd c (overR R' ψ))).app X.L).symm

omit [Algebra R R'] in
noncomputable def pullbackAlong_pullbackAlong_iso {X₀ X₁ X₂ : Scheme.{u}} {x₀ : X₀ ⟶ Spec (CommRingCat.of R)}
    {x₁ : X₁ ⟶ Spec (CommRingCat.of R)} {x₂ : X₂ ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε x₀) (φ : SchemeHomOver x₁ x₀) (ψ : SchemeHomOver x₂ x₁) :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

noncomputable def transportIso {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (e : h'.poincare.L ≅ (ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (z : SchemeHomOver t' (D.baseChange R').toBase) :
    (toR c ε R' (h'.poincare.pullbackAlong z)).L ≅
      (h.poincare.pullbackAlong (RelativeGroupLaw.baseChangePointToBase (specMap R R') z)).L :=
  ((Scheme.Modules.pullback (κ c R' t').inv).mapIso
      ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') z)).mapIso e ≪≫ ofR_pullbackAlong_iso c ε R' z _) ≪≫
    toR_ofR_iso c ε R' _ ≪≫
    pullbackAlong_pullbackAlong_iso c ε h.poincare _ _ : _)

end PTSGENA_BaseChange

noncomputable def PTSGENA_pullbackAlong_castOver_iso {R : Type} [CommRing R] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {X₀ T : Scheme.{0}} {x₀ : X₀ ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε x₀) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (hι : ι = ι') (w : SchemeHomOver ι x₀) :
    (M.pullbackAlong (castOver hι w)).L ≅
      (Scheme.Modules.pullback (pullback.congrHom rfl hι).inv).obj (M.pullbackAlong w).L := by
  subst hι
  exact ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    (Scheme.Modules.pullbackCongr (by apply pullback.hom_ext <;> simp [pullback.congrHom])).app _

set_option maxHeartbeats 1600000 in
theorem ptsCompatA_generator
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hL : O.L = RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD)

    [Algebra (R p) ↥A]
    (hDA : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A))
    (hpoincA : Nonempty (hDA.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ↥A
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ↥A), pullback.condition⟩)).L))

    (hLA : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥A)) (x y : SchemeHomOver t' ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t' x y =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).baseChange (specMap (R p) ↥A)).mul t' x y)
    (kA : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hkA₁ : kA ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkA₂ : kA ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ barPt A)
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

    (φ : pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ≅ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hφ : φ.hom ≫ baseChange (R p) (toBase p (ΓM M H) hj) ↥A = baseChange (R p) (toBase p (ΓM M H) hj) ↥A)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hφθ : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ kA ≫ φ.hom = y.1 ≫ 𝔛.eeta ≫ kA →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hbar : genPt p = barPt A ≫ specMap (R p) ↥A)

    (N : SchemeHomOver ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase)
    (hN₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A)) (a : SchemeHomOver t ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        Nonempty ((hDA.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) t (sectionBaseChange ↥A 𝔛.εinf)) (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) t)
            ((Scheme.Modules.pullback (curveChange φ.hom hφ t)).obj (hDA.poincare.pullbackAlong a).L)))
    (hN₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A)) (x y : SchemeHomOver t ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N))
    (hN₃ : ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).zeroSection ≫ N.1 = ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).zeroSection)
    (y s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hs : s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      Finsupp.single (𝔛.Meta.pointEquivPlace y) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1) :
    (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts (SemilinearAut.ofAlgAut θ • Pic0.mk Dv)))).1 =
      (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts (Pic0.mk Dv)))).1 ≫ N.1 := by
  classical
  haveI : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := hsepQ
  haveI := 𝔛.isProper
  haveI : IsSeparated (toBase p (ΓM M H) hj) := inferInstance
  haveI : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) := inferInstance

  let LwA := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA
  let S := SchemeHomOver (barPt A) ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase
  letI : Mul S := ⟨LwA.mul (barPt A)⟩
  letI : One S := ⟨LwA.one (barPt A)⟩
  letI : Inv S := ⟨LwA.inv (barPt A)⟩
  letI grp : Group S := Group.ofLeftAxioms (fun a b c => LwA.mul_assoc (barPt A) a b c) (fun a => LwA.one_mul (barPt A) a)
    (fun a => LwA.inv_mul_cancel (barPt A) a)
  let Nm : S →* S := MonoidHom.mk' (fun a => NeronModelInfra.schemeHomOverComp a N) (fun a b => hN₂ (barPt A) a b)

  let liftA : SchemeHomOver (genPt p) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase → S :=
    fun z => RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar z)
  let ptsA : JH M H → S := fun x => liftA (O.pts x)
  have hcast_mul : ∀ {ι ι' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (R p))} (h : ι = ι')
      (a b : SchemeHomOver ι (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase),
      castOver h ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).mul ι a b) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).mul ι' (castOver h a) (castOver h b) := by
    rintro ι _ rfl a b
    rfl
  have hpts_mul : ∀ x y : JH M H, ptsA (x + y) = ptsA x * ptsA y := by
    intro x y
    show RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts (x + y))) =
      LwA.mul (barPt A) (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts x)))
        (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts y)))
    rw [hLA, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase,
      RelativeGroupLaw.baseChangePointToBase_ofBase, ← hcast_mul, ← hpts_law]
  have hpts0 : ptsA 0 = 1 := by
    have h := hpts_mul 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hptsneg : ∀ x : JH M H, ptsA (-x) = (ptsA x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hpts_mul, neg_add_cancel, hpts0])
  have hptssub : ∀ x y : JH M H, ptsA (x - y) = ptsA x * (ptsA y)⁻¹ := fun x y => by
    rw [sub_eq_add_neg, hpts_mul, hptsneg]

  let bar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → SchemeHomOver (genPt p) (toBase p (ΓM M H) hj) :=
    fun b => ⟨b.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p), by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, b.2,
        Category.id_comp]⟩
  let barA : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → SchemeHomOver (barPt A) (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) :=
    fun b => ⟨b.1 ≫ 𝔛.eeta ≫ kA, by
      show (b.1 ≫ 𝔛.eeta ≫ kA) ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = barPt A
      rw [Category.assoc, Category.assoc, hkA₂, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, b.2, Category.id_comp]⟩
  let AJ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → SchemeHomOver (genPt p) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase :=
    fun b => ⟨b.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, ← Category.assoc, b.2, Category.id_comp]⟩
  let AJA : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → S := fun b => liftA (AJ b)
  have hφinv : φ.inv ≫ (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) = (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) := by rw [Iso.inv_comp_eq]; exact hφ.symm
  have hφinv' : ∀ {Z : Scheme.{0}} (f : Spec (CommRingCat.of ↥A) ⟶ Z), φ.inv ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ≫ f = pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ≫ f :=
    fun f => by simpa only [Category.assoc] using congrArg (· ≫ f) hφinv
  have hbarA2 : ∀ b, (barA b).1 ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = (barPt A) := fun b => (barA b).2
  have hbarA2' : ∀ b {Z : Scheme.{0}} (f : Spec (CommRingCat.of ↥A) ⟶ Z), (barA b).1 ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ≫ f = (barPt A) ≫ f :=
    fun b Z f => by simpa only [Category.assoc] using congrArg (· ≫ f) (hbarA2 b)
  have hτcompat : ∀ b, ((barA b).1 ≫ φ.inv ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A)) ≫ (toBase p (ΓM M H) hj) = 𝟙 _ ≫ genPt p := by
    intro b
    simp only [Category.assoc, pullback.condition]
    rw [hφinv', hbarA2', ← hbar, Category.id_comp]
  let τ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} :=
    fun b => ⟨pullback.lift ((barA b).1 ≫ φ.inv ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A)) (𝟙 _) (hτcompat b) ≫ inv 𝔛.eeta, by
      rw [Category.assoc, ← 𝔛.heeta, IsIso.inv_hom_id_assoc, pullback.lift_snd]⟩

  have hτlift : ∀ b, pullback.lift ((barA b).1 ≫ φ.inv ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A)) (𝟙 _) (hτcompat b) ≫ kA = (barA b).1 ≫ φ.inv := by
    intro b
    apply pullback.hom_ext
    · simp only [Category.assoc, hkA₁, pullback.lift_fst]
    · simp only [Category.assoc, hkA₂, pullback.lift_snd_assoc, Category.id_comp]
      symm
      show ((barA b).1 ≫ φ.inv) ≫ (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) = barPt A
      rw [Category.assoc, hφinv]
      exact hbarA2 b
  have hτlift' : ∀ b {Z : Scheme.{0}} (f : pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ⟶ Z),
      pullback.lift ((barA b).1 ≫ φ.inv ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A)) (𝟙 _) (hτcompat b) ≫ kA ≫ f = (barA b).1 ≫ φ.inv ≫ f := by
    intro b Z f
    simpa only [Category.assoc] using congrArg (· ≫ f) (hτlift b)

  have hτφ : ∀ b, (τ b).1 ≫ 𝔛.eeta ≫ kA ≫ φ.hom = b.1 ≫ 𝔛.eeta ≫ kA := by
    intro b
    show (pullback.lift ((barA b).1 ≫ φ.inv ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A)) (𝟙 _) (hτcompat b) ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ kA ≫ φ.hom = _
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hτlift' b, Iso.inv_hom_id, Category.comp_id]
  have hplτ : ∀ b, 𝔛.Meta.pointEquivPlace (τ b) = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace b := by
    intro b
    apply hφθ b (τ b)
    simpa only [Category.assoc] using hτφ b

  let cσ : pullback (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A) ⟶ pullback (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A) := curveChange φ.hom hφ (barPt A)
  have hΦP : ∀ z : S, Nonempty ((hDA.poincare.pullbackAlong (Nm z)).L ≅ (Scheme.Modules.pullback cσ).obj (hDA.poincare.pullbackAlong z).L) := by
    intro z
    obtain ⟨e2⟩ := hN₁ (barPt A) z
    obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field (ε := (sectionBaseChange ↥A 𝔛.εinf)) (barPt A)
      (L := (Scheme.Modules.pullback cσ).obj (hDA.poincare.pullbackAlong z).L) ((hDA.poincare.pullbackAlong z).isInvertible.pullback _)
    exact ⟨e2 ≪≫ e3⟩

  have hsndi : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd (toBase p (ΓM M H) hj) (genPt p) := by rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]
  haveI hsmQ : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) := by
    rw [← hsndi]; exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (inv 𝔛.eeta ≫ 𝔛.Meta.toBase))
  have hsm' : ∀ {t : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (R p))} (ht : genPt p = t),
      SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) t) := by
    rintro t rfl; exact hsmQ
  haveI hsmQ' : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) ((barPt A) ≫ (specMap (R p) ↥A))) := hsm' hbar
  haveI hsmA : SmoothOfRelativeDimension 1 (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A)) := by
    rw [← AlgebraicGeometry.RelPicard.BaseChange.κ_hom_snd (toBase p (ΓM M H) hj) ↥A (barPt A)]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((AlgebraicGeometry.RelPicard.BaseChange.κ (toBase p (ΓM M H) hj) ↥A (barPt A)).hom ≫ pullback.snd (toBase p (ΓM M H) hj) ((barPt A) ≫ (specMap (R p) ↥A))))
  let ι : pullback (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A) ⟶ pullback (toBase p (ΓM M H) hj) (genPt p) :=
    (AlgebraicGeometry.RelPicard.BaseChange.κ (toBase p (ΓM M H) hj) ↥A (barPt A)).hom ≫ (pullback.congrHom rfl hbar).inv
  haveI hιiso : IsIso ι := IsIso.comp_isIso
  have hιfst : ι ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A) ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A) := by
    simp only [ι, Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id,
      AlgebraicGeometry.RelPicard.BaseChange.κ_hom_fst]
  have hιsnd : ι ≫ pullback.snd (toBase p (ΓM M H) hj) (genPt p) = pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A) := by
    simp only [ι, Category.assoc, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id,
      AlgebraicGeometry.RelPicard.BaseChange.κ_hom_snd]
  haveI hcσiso : IsIso cσ := by
    show IsIso (curveChange φ.hom hφ (barPt A))
    unfold curveChange
    infer_instance

  have hgraph : ∀ b, graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA (τ b)).1 (barA (τ b)).2 ≫ cσ = graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA b).1 (barA b).2 := by
    intro b
    apply pullback.hom_ext
    · show (graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA (τ b)).1 (barA (τ b)).2 ≫ curveChange φ.hom hφ (barPt A)) ≫ pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A) = graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA b).1 (barA b).2 ≫ pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A)
      simp only [graphOver, curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      first
        | simpa only [Category.assoc] using hτφ b
        | (simpa only [Category.assoc] using (hτφ b :)) | (simpa [Function.comp_def] using hτφ b) | exact hτφ b | (have h__ := hτφ b; (try simp only [Category.assoc] at h__); (try simp only [Category.assoc]); exact h__)
    · show (graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA (τ b)).1 (barA (τ b)).2 ≫ curveChange φ.hom hφ (barPt A)) ≫ pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A) = graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA b).1 (barA b).2 ≫ pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A)
      simp only [graphOver, curveChange, Category.assoc, pullback.lift_snd, Category.comp_id]
  have hOσ : ∀ b, Nonempty ((Scheme.Modules.pullback cσ).obj (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA b).1 (barA b).2).lineBundle ≅
      (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA (τ b)).1 (barA (τ b)).2).lineBundle) := fun b =>
    (PTSGENA_pullback_ofPoint_iso_of_graph_comp_eq (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barPt A) (barPt A) cσ (barA b).1 (barA (τ b)).1 (barA b).2 (barA (τ b)).2 (hgraph b)).1

  have hιgraph : ∀ b, graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA b).1 (barA b).2 ≫ ι = graphOver (toBase p (ΓM M H) hj) (bar b).1 (bar b).2 := by
    intro b
    apply pullback.hom_ext
    · rw [Category.assoc, hιfst, graphOver, graphOver, pullback.lift_fst_assoc, pullback.lift_fst]
      show (b.1 ≫ 𝔛.eeta ≫ kA) ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = b.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p)
      rw [Category.assoc, Category.assoc, hkA₁]
    · rw [Category.assoc, hιsnd, graphOver, graphOver, pullback.lift_snd, pullback.lift_snd]
  have hεA_over : ((barPt A) ≫ (sectionBaseChange ↥A 𝔛.εinf).1) ≫ (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) = (barPt A) :=
    (Category.assoc _ _ _).trans ((congrArg ((barPt A) ≫ ·) (sectionBaseChange ↥A 𝔛.εinf).2).trans (Category.comp_id _))
  have hε_over : (genPt p ≫ 𝔛.εinf.1) ≫ (toBase p (ΓM M H) hj) = genPt p :=
    (Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _))
  have hιgraphε : graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) ((barPt A) ≫ (sectionBaseChange ↥A 𝔛.εinf).1) hεA_over ≫ ι = graphOver (toBase p (ΓM M H) hj) (genPt p ≫ 𝔛.εinf.1) hε_over := by
    apply pullback.hom_ext
    · rw [Category.assoc, hιfst, graphOver, graphOver, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc,
        sectionBaseChange_coe_fst, ← Category.assoc, ← hbar]
    · rw [Category.assoc, hιsnd, graphOver, graphOver, pullback.lift_snd, pullback.lift_snd]

  let IεA := (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) ((barPt A) ≫ (sectionBaseChange ↥A 𝔛.εinf).1) hεA_over).idealModule
  have hI1 : ∀ b, Nonempty ((hDA.poincare.pullbackAlong (AJA b)).L ≅
      (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA b).1 (barA b).2).lineBundle ⊗ IεA) := by
    intro b
    obtain ⟨i0⟩ := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
      p M H hpM hj 𝔛 (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)) hD hDQ ajQ kQ ajbar hpoinc hajcl hkQ₁ hkQ₂ hajbar b (bar b) rfl (AJ b) rfl
    obtain ⟨o1⟩ := (PTSGENA_pullback_ofPoint_iso_of_graph_comp_eq (toBase p (ΓM M H) hj) (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (genPt p) (barPt A) ι (bar b).1 (barA b).1 (bar b).2 (barA b).2 (hιgraph b)).1
    obtain ⟨o2⟩ := (PTSGENA_pullback_ofPoint_iso_of_graph_comp_eq (toBase p (ΓM M H) hj) (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (genPt p) (barPt A) ι _ _ hε_over hεA_over hιgraphε).2
    have htb : RelativeGroupLaw.baseChangePointToBase (specMap (R p) ↥A) (AJA b) = castOver hbar (AJ b) :=
      RelativeGroupLaw.baseChangePointToBase_ofBase _ _
    have e1 : (hDA.poincare.pullbackAlong (AJA b)).L ≅
        (Scheme.Modules.pullback (AlgebraicGeometry.RelPicard.BaseChange.κ (toBase p (ΓM M H) hj) ↥A (barPt A)).hom).obj
          (AlgebraicGeometry.RelPicard.BaseChange.toR (toBase p (ΓM M H) hj) 𝔛.εinf ↥A (hDA.poincare.pullbackAlong (AJA b))).L :=
      (AlgebraicGeometry.RelPicard.BaseChange.ofR_toR_iso (toBase p (ΓM M H) hj) 𝔛.εinf ↥A _).symm
    have e2 : (AlgebraicGeometry.RelPicard.BaseChange.toR (toBase p (ΓM M H) hj) 𝔛.εinf ↥A (hDA.poincare.pullbackAlong (AJA b))).L ≅
        (hD.poincare.pullbackAlong (castOver hbar (AJ b))).L :=
      PTSGENA_BaseChange.transportIso (toBase p (ΓM M H) hj) 𝔛.εinf ↥A hD hDA hpoincA.some (AJA b) ≪≫
        eqToIso (congrArg (fun z => (hD.poincare.pullbackAlong z).L) htb)
    have e3 : (hD.poincare.pullbackAlong (castOver hbar (AJ b))).L ≅
        (Scheme.Modules.pullback (pullback.congrHom rfl hbar).inv).obj (hD.poincare.pullbackAlong (AJ b)).L :=
      PTSGENA_pullbackAlong_castOver_iso (toBase p (ΓM M H) hj) 𝔛.εinf hD.poincare hbar (AJ b)
    have e4 : (Scheme.Modules.pullback (AlgebraicGeometry.RelPicard.BaseChange.κ (toBase p (ΓM M H) hj) ↥A (barPt A)).hom).obj
          ((Scheme.Modules.pullback (pullback.congrHom rfl hbar).inv).obj (hD.poincare.pullbackAlong (AJ b)).L) ≅
        (Scheme.Modules.pullback ι).obj (hD.poincare.pullbackAlong (AJ b)).L :=
      (Scheme.Modules.pullbackComp (AlgebraicGeometry.RelPicard.BaseChange.κ (toBase p (ΓM M H) hj) ↥A (barPt A)).hom (pullback.congrHom rfl hbar).inv).app _
    exact ⟨e1 ≪≫ (Scheme.Modules.pullback _).mapIso (e2 ≪≫ e3) ≪≫ e4 ≪≫
      (Scheme.Modules.pullback ι).mapIso i0 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o1 ⊗ᵢ o2)⟩

  have hkey2 : ∀ b b', Nm (AJA b) * AJA (τ b') = AJA (τ b) * Nm (AJA b') := by
    intro b b'
    apply hDA.ext_of_iso (barPt A)
    obtain ⟨m1⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA
      (T := Over.mk (barPt A)) (schemeHomOverToOverHom (Nm (AJA b))) (schemeHomOverToOverHom (AJA (τ b')))
    obtain ⟨m2⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA
      (T := Over.mk (barPt A)) (schemeHomOverToOverHom (AJA (τ b))) (schemeHomOverToOverHom (Nm (AJA b')))
    obtain ⟨t1⟩ := hΦP (AJA b)
    obtain ⟨t2⟩ := hΦP (AJA b')
    obtain ⟨i1⟩ := hI1 b
    obtain ⟨i2⟩ := hI1 b'
    obtain ⟨i3⟩ := hI1 (τ b)
    obtain ⟨i4⟩ := hI1 (τ b')
    obtain ⟨o1⟩ := hOσ b
    obtain ⟨o2⟩ := hOσ b'
    let Ob := (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA (τ b)).1 (barA (τ b)).2).lineBundle
    let Ob' := (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (barA (τ b')).1 (barA (τ b')).2).lineBundle
    let Iw := (Scheme.Modules.pullback cσ).obj IεA
    have eθb : (hDA.poincare.pullbackAlong (Nm (AJA b))).L ≅ Ob ⊗ Iw :=
      t1 ≪≫ (Scheme.Modules.pullback cσ).mapIso i1 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o1 ⊗ᵢ Iso.refl _)
    have eθb' : (hDA.poincare.pullbackAlong (Nm (AJA b'))).L ≅ Ob' ⊗ Iw :=
      t2 ≪≫ (Scheme.Modules.pullback cσ).mapIso i2 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o2 ⊗ᵢ Iso.refl _)
    have eL : (hDA.poincare.pullbackAlong (Nm (AJA b) * AJA (τ b'))).L ≅ (Ob ⊗ Iw) ⊗ (Ob' ⊗ IεA) :=
      m1 ≪≫ (eθb ⊗ᵢ i4)
    have eR : (hDA.poincare.pullbackAlong (AJA (τ b) * Nm (AJA b'))).L ≅ (Ob ⊗ IεA) ⊗ (Ob' ⊗ Iw) :=
      m2 ≪≫ (i3 ⊗ᵢ eθb')
    exact ⟨eL ≪≫ Scheme.Modules.tensorTensorTensorComm Ob Iw Ob' IεA ≪≫ (Iso.refl _ ⊗ᵢ β_ Iw IεA) ≪≫
      (Scheme.Modules.tensorTensorTensorComm Ob IεA Ob' Iw).symm ≪≫ eR.symm⟩

  have hAJs : AJA s = 1 := by
    obtain ⟨D0, hD0, hgp0⟩ := hAJ s s hs
    have h00 : Pic0.mk D0 = 0 := by
      have : D0 = 0 := Subtype.ext (by rw [hD0, sub_self]; rfl)
      rw [this]; rfl
    have : ptsA (Pic0.mk D0) = AJA s := by
      show liftA (O.pts (Pic0.mk D0)) = liftA (AJ s)
      rw [show O.pts (Pic0.mk D0) = AJ s from Subtype.ext hgp0]
    rw [← this, h00, hpts0]
  have hkey : ∀ b, Nm (AJA b) = AJA (τ b) * (AJA (τ s))⁻¹ := by
    intro b
    have hk := hkey2 b s
    rw [hAJs, map_one, mul_one] at hk
    rw [← hk, mul_inv_cancel_right]

  obtain ⟨Dv', hDv', hgp⟩ := hAJ y s hs
  obtain rfl : Dv = Dv' := Subtype.ext (hDv.trans hDv'.symm)
  obtain ⟨D1, hD1, hgp1⟩ := hAJ (τ y) s hs
  obtain ⟨D2, hD2, hgp2⟩ := hAJ (τ s) s hs
  have hA0 : ptsA (Pic0.mk Dv) = AJA y := by
    show liftA _ = liftA _; rw [show O.pts (Pic0.mk Dv) = AJ y from Subtype.ext hgp]
  have hA1 : ptsA (Pic0.mk D1) = AJA (τ y) := by
    show liftA _ = liftA _; rw [show O.pts (Pic0.mk D1) = AJ (τ y) from Subtype.ext hgp1]
  have hA2 : ptsA (Pic0.mk D2) = AJA (τ s) := by
    show liftA _ = liftA _; rw [show O.pts (Pic0.mk D2) = AJ (τ s) from Subtype.ext hgp2]
  have hsm : SemilinearAut.ofAlgAut θ • Pic0.mk Dv = Pic0.mk D1 - Pic0.mk D2 := by
    rw [AlgebraicCurve.SemilinearAut.pic0_smul_mk]
    have hcoe : AlgebraicCurve.SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut θ) Dv = D1 - D2 := by
      apply Subtype.ext
      rw [AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom, AddSubgroupClass.coe_sub, hD1, hD2, hDv, smul_sub,
        AlgebraicCurve.SemilinearAut.smul_single, AlgebraicCurve.SemilinearAut.smul_single, hplτ, hplτ]
      abel
    rw [hcoe]
    exact QuotientAddGroup.mk_sub _ D1 D2
  have hfin : ptsA (SemilinearAut.ofAlgAut θ • Pic0.mk Dv) = Nm (ptsA (Pic0.mk Dv)) := by
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

    (hL : O.L = RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD)

    [Algebra (R p) ↥A]
    (hDA : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A))
    (hpoincA : Nonempty (hDA.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ↥A
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ↥A), pullback.condition⟩)).L))

    (hLA : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥A)) (x y : SchemeHomOver t' ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t' x y =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).baseChange (specMap (R p) ↥A)).mul t' x y)
    (kA : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hkA₁ : kA ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkA₂ : kA ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ barPt A)
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

    (φ : pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ≅ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hφ : φ.hom ≫ baseChange (R p) (toBase p (ΓM M H) hj) ↥A = baseChange (R p) (toBase p (ΓM M H) hj) ↥A)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hφθ : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ kA ≫ φ.hom = y.1 ≫ 𝔛.eeta ≫ kA →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hbar : genPt p = barPt A ≫ specMap (R p) ↥A)

    (N : SchemeHomOver ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase)
    (hN₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A)) (a : SchemeHomOver t ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        Nonempty ((hDA.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) t (sectionBaseChange ↥A 𝔛.εinf)) (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) t)
            ((Scheme.Modules.pullback (curveChange φ.hom hφ t)).obj (hDA.poincare.pullbackAlong a).L)))
    (hN₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A)) (x y : SchemeHomOver t ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N))
    (hN₃ : ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).zeroSection ≫ N.1 = ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).zeroSection) :
    ∀ x : JH M H,
      (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts (SemilinearAut.ofAlgAut θ • x)))).1 =
        (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts x))).1 ≫ N.1 := by
  classical

  let ptsA : JH M H → SchemeHomOver (barPt A) ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase := fun x =>
    RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts x))
  let P : JH M H → Prop := fun x => (ptsA (SemilinearAut.ofAlgAut θ • x)).1 = (ptsA x).1 ≫ N.1
  show ∀ x, P x

  let gens : Set (JH M H) := {x | ∃ (y s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ∧
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace y) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧ x = Pic0.mk Dv}
  have hgen : ∀ x ∈ gens, P x := by
    rintro _ ⟨y, s, hs, Dv, hDv, rfl⟩
    exact ptsCompatA_generator p M H hpM hpM2 hHp hj 𝔛 A hA Λ O hD hL hDA hpoincA hLA kA hkA₁ hkA₂ hDQ hsepQ ajQ kQ ajbar εbar hpoinc hajε hajcl hkQ₁ hkQ₂ hajbar hajbar_over hεbar hεbar_aj hpts_law hAJ φ hφ θ hφθ hbar N hN₁ hN₂ hN₃ y s hs Dv hDv

  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD
  let LwA := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA)
  let S := SchemeHomOver (barPt A) ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase
  letI : Mul S := ⟨LwA.mul (barPt A)⟩
  letI : One S := ⟨LwA.one (barPt A)⟩
  letI : Inv S := ⟨LwA.inv (barPt A)⟩
  letI grp : Group S := Group.ofLeftAxioms (fun a b c => LwA.mul_assoc (barPt A) a b c) (fun a => LwA.one_mul (barPt A) a)
    (fun a => LwA.inv_mul_cancel (barPt A) a)
  let Nm : S →* S := MonoidHom.mk' (fun a => NeronModelInfra.schemeHomOverComp a N) (fun a b => hN₂ (barPt A) a b)

  have hcast_mul : ∀ {ι ι' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (R p))} (h : ι = ι')
      (a b : SchemeHomOver ι (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).toBase),
      castOver h (Lw.mul ι a b) = Lw.mul ι' (castOver h a) (castOver h b) := by
    rintro ι _ rfl a b
    rfl
  have hpts_mul : ∀ x y : JH M H, (ptsA (x + y) : S) = (ptsA x : S) * (ptsA y : S) := by
    intro x y
    show RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts (x + y))) =
      LwA.mul (barPt A) (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts x)))
        (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts y)))
    rw [hLA, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase,
      RelativeGroupLaw.baseChangePointToBase_ofBase, ← hcast_mul, ← hpts_law]
  have hpts0 : (ptsA 0 : S) = 1 := by
    have h := hpts_mul 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hptsneg : ∀ x : JH M H, (ptsA (-x) : S) = (ptsA x : S)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hpts_mul, neg_add_cancel, hpts0])
  have hP_iff : ∀ x, P x ↔ (ptsA (SemilinearAut.ofAlgAut θ • x) : S) = Nm (ptsA x) := fun x =>
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
  obtain ⟨Sg, hS⟩ := ptsCompatA_standin_additive P h0 hadd hneg
  have hle : AddSubgroup.closure gens ≤ Sg := (AddSubgroup.closure_le Sg).mpr (fun x hx => (hS x).mpr (hgen x hx))
  intro x
  exact (hS x).mp (hle (htop ▸ AddSubgroup.mem_top x))

end S_ModularCurve_JHNeronObjectAtP_baseChangePointOfBase_pts_ofAlgAut_smul_eq_comp_of_classifies_rigidify_pullback_curveChange_baseChange_of_abelJacobi
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_baseChangePointOfBase_pts_ofAlgAut_smul_eq_comp_of_classifies_rigidify_pullback_curveChange_baseChange_of_abelJacobi (solution)
