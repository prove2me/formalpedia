-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.degPts_eq_zero_of_mem_toricPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1cb3dcf0-6c6c-544e-be8d-41362bceb61e

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_schemeHomOverComp_torusFibre_degeneracyHom_eq_one
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq_levelData
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_pow_baseChange_levelData
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_abelianSchemePropertyBundle
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_degPts_eq_zero_of_mem_toricPts
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve~H1 IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP"

open scoped MatrixGroups

noncomputable section

namespace TorKerK

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

theorem toFibrePt_coe_fst {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (w : SchemeHomOver ι f) : (toFibrePt w).1 ≫ pullback.fst f ι = w.1 := by
  unfold toFibrePt
  rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  rfl

theorem ptsSp_add_iff_aux (a b : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f) :
    ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt a) (toFibrePt b)) = Λ.L.mul _ a b := by
  apply Subtype.ext
  change (RelativeGroupLaw.baseChangePointToBase _ ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt a) (toFibrePt b))).1 = _
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase]

  have ha : RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) (toFibrePt a) = overId a := by
    unfold toFibrePt; rw [RelativeGroupLaw.baseChangePointToBase_ofBase]
  have hb : RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) (toFibrePt b) = overId b := by
    unfold toFibrePt; rw [RelativeGroupLaw.baseChangePointToBase_ofBase]
  rw [ha, hb]

  have key : ∀ (t t' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ base p) (h : t = t') (x y : SchemeHomOver t Λ.f),
      (Λ.L.mul t x y).1 = (Λ.L.mul t' ⟨x.1, x.2.trans h⟩ ⟨y.1, y.2.trans h⟩).1 := by
    rintro t _ rfl x y; rfl
  exact key _ _ (Category.id_comp _) (overId a) (overId b)

theorem comp_mul_fibreRestrictAlong {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
    (φ : SchemeHomOver O.g Λ.f)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
        Λ.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) :
    NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) (fibreRestrictAlong Λ.σA Λ.f O.g φ) =
      (Λ.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong Λ.σA Λ.f O.g φ))
        (NeronModelInfra.schemeHomOverComp y (fibreRestrictAlong Λ.σA Λ.f O.g φ)) := by
  apply (RelativeGroupLaw.baseChangePointEquiv Λ.σA s).injective
  change RelativeGroupLaw.baseChangePointToBase Λ.σA _ = RelativeGroupLaw.baseChangePointToBase Λ.σA _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChange_mul,
    RelativeGroupLaw.baseChangePointToBase_ofBase, hφ, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase,
    RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]

theorem comp_one (m : ℕ) (z : SchemeHomOver (barPt A) (muStr ↥A O.toricRank m)) :
    NeronModelInfra.schemeHomOverComp z ((Λ.L.baseChange Λ.σA).one (muStr ↥A O.toricRank m)) =
      (Λ.L.baseChange Λ.σA).one (barPt A) := by
  have h := (Λ.L.baseChange Λ.σA).one_natural (muStr ↥A O.toricRank m) (barPt A) z.1 z.2
  exact (Subtype.ext rfl).trans h

theorem pts_zero (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y)) :
    Λ.pts 0 = Λ.L.one (genPt p) := by
  letI := Λ.L.pointGroup (genPt p)
  have h : Λ.pts 0 * Λ.pts 0 = Λ.pts 0 := by
    change Λ.L.mul _ (Λ.pts 0) (Λ.pts 0) = Λ.pts 0
    rw [← hΛpts_add, add_zero]
  exact mul_left_cancel (h.trans (mul_one _).symm)

theorem muStr_residue {G : Type} [AddCommMonoid G] :
    (algebraMap (ResidueField ↥A) (AddMonoidAlgebra (ResidueField ↥A) G)).comp (IsLocalRing.residue ↥A) =
      (AddMonoidAlgebra.mapRingHom G (IsLocalRing.residue ↥A)).comp (algebraMap ↥A (AddMonoidAlgebra ↥A G)) := by
  refine RingHom.ext fun a => ?_
  change AddMonoidAlgebra.single 0 (IsLocalRing.residue ↥A a) = AddMonoidAlgebra.mapRingHom G (IsLocalRing.residue ↥A) (AddMonoidAlgebra.single 0 a)
  rw [AddMonoidAlgebra.mapRingHom_single]

theorem muToTorus_torusStr_resPt (m : ℕ) :
    muToTorus (ResidueField ↥A) O.toricRank m ≫ torusStr (ResidueField ↥A) O.toricRank ≫ resPt A =
      muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ muStr ↥A O.toricRank m := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  rw [← RingHom.comp_assoc, ← muStr_residue]
  refine RingHom.ext fun a => ?_
  change AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) _ (AddMonoidAlgebra.single 0 (IsLocalRing.residue ↥A a)) =
    AddMonoidAlgebra.single 0 (IsLocalRing.residue ↥A a)
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, map_zero]

end TorKerK

end

open TorKerK in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (n : ℕ) (x : JH M H) (hx : x ∈ O.toricPts (p ^ n)) (i : Fin 2) :
    O.degPts i x = 0 := by
  classical
  have hm : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

  haveI hloc := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  haveI : IsLocalRing (baseRing p) := IsLocalization.AtPrime.isLocalRing (baseRing p) (Ideal.span {(p : ℤ)})
  haveI : IsNoetherianRing (baseRing p) :=
    IsLocalization.isNoetherianRing (Ideal.span {(p : ℤ)}).primeCompl (baseRing p) inferInstance
  have hΛcomm : ∀ {T : Scheme.{0}} (t : T ⟶ base p) (x y : SchemeHomOver t Λ.f), Λ.L.mul t x y = Λ.L.mul t y x :=
    fun t x y => (GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_abelianSchemePropertyBundle hΛ Λ.L) t x y
  have hadd : ∀ u v : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (u + v) = Λ.L.mul _ (Λ.ptsSp u) (Λ.ptsSp v) := fun u v => by
    rw [hΛptsSp_add, ptsSp_add_iff_aux]
  have hΛm := ModularCurve.JHNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_pow_baseChange_levelData
    p M H hpM hpM2 A hA Λ hΛ hΛcomm hadd n

  obtain ⟨-, -, hmem, -⟩ :=
    ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard p M H hpM A hA Λ O (p ^ n) hm
  obtain ⟨χ, rfl⟩ := (hmem x).mp hx

  set u : SchemeHomOver (muStr ↥A O.toricRank (p ^ n)) (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f) :=
    NeronModelInfra.schemeHomOverComp (O.toricLift (p ^ n) hm) (fibreRestrictAlong Λ.σA Λ.f O.g (O.degeneracyHom i)) with hu_def
  set v : SchemeHomOver (muStr ↥A O.toricRank (p ^ n)) (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f) :=
    (Λ.L.baseChange Λ.σA).one (muStr ↥A O.toricRank (p ^ n)) with hv_def
  have hu : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank (p ^ n) (χ * χ').ofConv) u =
        (Λ.L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank (p ^ n) χ.ofConv) u)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank (p ^ n) χ'.ofConv) u) := by
    intro χ χ'
    rw [hu_def, ← NeronModelInfra.schemeHomOverComp_assoc, O.toricLift_mul, comp_mul_fibreRestrictAlong O _ _ (O.degeneracyHom_mul i),
      NeronModelInfra.schemeHomOverComp_assoc, NeronModelInfra.schemeHomOverComp_assoc]
  have hv : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank (p ^ n) (χ * χ').ofConv) v =
        (Λ.L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank (p ^ n) χ.ofConv) v)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank (p ^ n) χ'.ofConv) v) := by
    intro χ χ'
    rw [hv_def, comp_one O, comp_one O, comp_one O, (Λ.L.baseChange Λ.σA).one_mul]

  have hKb := ModularCurve.JHNeronObjectAtP.schemeHomOverComp_torusFibre_degeneracyHom_eq_one
    p M H hpM hpM2 A hA Λ O hΛ hΛptsSp_add i
  have huv : muBaseChange (IsLocalRing.residue ↥A) O.toricRank (p ^ n) ≫ u.1 =
      muBaseChange (IsLocalRing.residue ↥A) O.toricRank (p ^ n) ≫ v.1 := by
    have key : ∀ (t t' : muScheme (ResidueField ↥A) O.toricRank (p ^ n) ⟶ base p), t = t' → (Λ.L.one t).1 = (Λ.L.one t').1 := by
      rintro t _ rfl; rfl
    apply pullback.hom_ext
    ·
      rw [hu_def, hv_def, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, Category.assoc, Category.assoc,
        fibreRestrictAlong_coe_comp_fst, ← Category.assoc (O.toricLift (p ^ n) hm).1, ← Category.assoc, O.toricLift_special (p ^ n) hm,
        Category.assoc, Category.assoc]

      have e1 : O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ (O.degeneracyHom i).1 =
          (Λ.L.one (torusStr (ResidueField ↥A) O.toricRank ≫ resPt A ≫ Λ.σA)).1 := by
        have := congrArg Subtype.val hKb
        rw [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc] at this
        exact this
      rw [e1, RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      have e2 := congrArg Subtype.val (Λ.L.one_natural (torusStr (ResidueField ↥A) O.toricRank ≫ resPt A ≫ Λ.σA) _
        (muToTorus (ResidueField ↥A) O.toricRank (p ^ n)) rfl)
      have e3 := congrArg Subtype.val (Λ.L.one_natural (muStr ↥A O.toricRank (p ^ n) ≫ Λ.σA) _
        (muBaseChange (IsLocalRing.residue ↥A) O.toricRank (p ^ n)) rfl)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at e2 e3
      rw [e2, e3]
      refine key _ _ ?_
      rw [reassoc_of% (muToTorus_torusStr_resPt O (p ^ n))]
    · rw [hu_def, hv_def, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, Category.assoc,
        (fibreRestrictAlong Λ.σA Λ.f O.g (O.degeneracyHom i)).2, (O.toricLift (p ^ n) hm).2, Category.assoc]
      exact congrArg (muBaseChange (IsLocalRing.residue ↥A) O.toricRank (p ^ n) ≫ ·) (((Λ.L.baseChange Λ.σA).one _).2).symm
  have hrig := ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq_levelData p M H hpM A hA Λ hΛ hΛcomm O (p ^ n) hm hΛm
    u v hu hv huv

  apply Λ.pts.injective
  rw [pts_zero hΛpts_add]
  apply Subtype.ext
  rw [O.degeneracyHom_pts]
  have ept : (O.pts (O.toricPoint (p ^ n) hm χ)).1 =
      ((muPt A O.toricRank (p ^ n) χ).1 ≫ (O.toricLift (p ^ n) hm).1) ≫ pullback.fst O.g Λ.σA := by
    change (O.pts (O.pts.symm _)).1 = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hχu : NeronModelInfra.schemeHomOverComp (muPt A O.toricRank (p ^ n) χ) u = (Λ.L.baseChange Λ.σA).one (barPt A) := by
    rw [hrig]; exact comp_one O _ _
  have hχu1 := congrArg Subtype.val hχu
  rw [hu_def, NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChange_one,
    RelativeGroupLaw.baseChangePointOfBase_coe] at hχu1
  have h1 := congrArg (· ≫ pullback.fst Λ.f Λ.σA) hχu1
  simp only [Category.assoc, fibreRestrictAlong_coe_comp_fst, pullback.lift_fst] at h1
  rw [ept, Category.assoc, Category.assoc, h1]
  have key : ∀ (t t' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ base p), t = t' → (Λ.L.one t).1 = (Λ.L.one t').1 := by
    rintro t _ rfl; rfl
  exact key _ _ Λ.hσA

end S_ModularCurve_JHNeronObjectAtP_degPts_eq_zero_of_mem_toricPts
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_degPts_eq_zero_of_mem_toricPts (solution)
