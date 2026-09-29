-- Prove2me | solution 1 for ModularCurve.exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3c43a4d4-5504-5bc2-8d62-0561fecc7577

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicGeometry_isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime
import Theorems.Thm_AlgebraicGeometry_exists_closedFibre_testCurves_of_integralPoints_through
import Theorems.Thm_NeronModelInfra_exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
import Theorems.Thm_NeronModelInfra_exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw
import Theorems.Thm_ModularCurve_exists_integralPoints_through_of_torsion_over_p
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard

namespace AsmRoot

set_option maxHeartbeats 1600000 in

theorem exists_comparison_and_avatar
    (R : Type) [CommRing R] [Algebra R ℚ]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ))
    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))) :
    ∃ (θ : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
        pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
      (φK : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
        pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))),
      θ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) =
        pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫
          pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) ∧
      θ ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) =
        pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ∧
      φK ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) =
        pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ∧
      φK ≫ θ = θ ≫ φη.1 := by

  have hι : Spec.map (CommRingCat.ofHom (algebraMap R ℚ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) := by
    have hring : (algebraMap R ℚ).comp (algebraMap ℤ R) = algebraMap ℤ ℚ := Subsingleton.elim _ _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]

  let θ : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst g _) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hι])
  have hθ₁ : θ ≫ pullback.fst g _ = pullback.fst _ _ ≫ pullback.fst g _ := pullback.lift_fst _ _ _
  have hθ₂ : θ ≫ pullback.snd g _ = pullback.snd _ _ := pullback.lift_snd _ _ _

  let ψ : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ⟶
      pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) :=
    pullback.lift
      (pullback.lift (pullback.fst g _) (pullback.snd g _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))
        (by rw [pullback.condition, Category.assoc, hι]))
      (pullback.snd g _) (by rw [pullback.lift_snd])
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hθ₁, Category.id_comp, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hθ₂, Category.id_comp, pullback.lift_snd]
  have hθψ : θ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, hθ₁, Category.id_comp]
      · rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, ← Category.assoc, hθ₂,
          Category.id_comp, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, hθ₂, Category.id_comp]
  refine ⟨θ, θ ≫ φη.1 ≫ ψ, hθ₁, hθ₂, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, φη.2, hθ₂]
  · rw [Category.assoc, Category.assoc, hψθ, Category.comp_id]

set_option maxHeartbeats 1600000 in

theorem exists_lift_genericFibre {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ))
    (a : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ G)
    (ha : a ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) :
    ∃ z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))),
      z ≫ pullback.fst g _ = a ∧
      z ≫ pullback.snd g _ = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
  have hι : Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) := by
    have hring : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap ℤ ℚ) =
        algebraMap ℤ (AlgebraicClosure ℚ) := Subsingleton.elim _ _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  exact ⟨pullback.lift a _ (by rw [ha, hι]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end AsmRoot

set_option maxHeartbeats 1600000 in
theorem AsmRoot.Int_exists_natPrime_eq_span_of_isMaximal (𝔪 : Ideal ℤ) [h𝔪 : 𝔪.IsMaximal] :
    ∃ q : ℕ, q.Prime ∧ 𝔪 = Ideal.span {(q : ℤ)} := by
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal 𝔪).principal
  have hg' : 𝔪 = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hbot : 𝔪 = ⊥ := by rw [hg']; simp
    have h2 : Ideal.span {(2 : ℤ)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]; decide
    have := h𝔪.eq_of_le h2 (by rw [hbot]; exact bot_le)
    have hmem : (2 : ℤ) ∈ 𝔪 := by rw [this]; exact Ideal.mem_span_singleton_self 2
    rw [hbot] at hmem
    exact two_ne_zero ((Submodule.mem_bot ℤ).mp hmem)
  have hprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ h𝔪.isPrime)
  exact ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hprime, by rw [Int.span_natAbs]; exact hg'⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)

    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hconn : GeometricallyConnected D.toBase)

    (hcomm : (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).IsCommutative)
    (hlft : LocallyOfFiniteType D.toBase)
    (hpre : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (D.toBase.base ⁻¹' {s}))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))

    (hnflat : ∀ n : ℕ, 0 < n → Flat
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul n))
    (hnsurj : ∀ n : ℕ, 0 < n → Surjective
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul n))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hvi : ∀ m : ℕ, ¬ p ∣ m →
      {x : JZero p | x ∈ jZeroTorsion p m ∧
          ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) D.toBase,
            (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1}
        = (jZeroToricTorsion p A m : Set (JZero p)))
    (hptors : ∀ ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ D.P,
      ζ ≫ D.toBase = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) →
      ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧
        ζ ≫ (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul m =
          ζ ≫ D.toBase ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).one (𝟙 _)).1)

    (hR1 : ∀ {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      {G H : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of R)) (h : H ⟶ Spec (CommRingCat.of R))
      [IsIntegral G] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (η : G) (_hη : g.base η = IsLocalRing.closedPoint R)
      (_hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x)
      [IsDiscreteValuationRing (G.presheaf.stalk η)]
      (φK : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (hφK : φK ≫ pullback.snd h _ = pullback.snd g _)
      (Dset : Set G) (_hD : ∀ z ∈ Dset, g.base z = IsLocalRing.closedPoint R) (_hDη : η ∈ closure Dset)
      (_hpts : ∀ z ∈ Dset, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
      (c : Spec (CommRingCat.of A) ⟶ pullback g h),
      (c ≫ pullback.fst g h).base (IsLocalRing.closedPoint A) = z ∧
      c.base ⟨⊥, Ideal.isPrime_bot⟩ ∈ Set.range
      (pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).base),
      ∃ (V : G.Opens) (v : (V : Scheme.{0}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧ (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧ η ∈ V ∧
      ∃ hle : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⊆ Set.range V.ι.base,
      IsOpenImmersion.lift V.ι (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hle ≫ v =
      φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))

    (hC1 : letI := heckeModuleBar p
      ∀ t : HeckeAlg,
      ∃ φη : SchemeHomOver
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
            (x y : SchemeHomOver s (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))),
          NeronModelInfra.schemeHomOverComp
              (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                  (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s x y) φη =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη)) ∧
        (∀ (x : JZero p)
            (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
              pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
          z ≫ pullback.fst D.toBase _ = (pts x).1 → zt ≫ pullback.fst D.toBase _ = (pts (t • x)).1 → zt = z ≫ φη.1))

    (hC2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ p →
      ∀ φη : SchemeHomOver
          (pullback.snd D.toBase (specGenericFibreInclusion ℤ ℚ))
          (pullback.snd D.toBase (specGenericFibreInclusion ℤ ℚ)),
      ∃ gA : pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ⟶ D.P,
        gA ≫ D.toBase = pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ≫ D.toBase ∧
        ∀ j : pullback D.toBase (specGenericFibreInclusion ℤ ℚ) ⟶
              pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))),
          j ≫ pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) =
            pullback.fst D.toBase (specGenericFibreInclusion ℤ ℚ) →
          j ≫ gA = φη.1 ≫ pullback.fst D.toBase (specGenericFibreInclusion ℤ ℚ)) :

    letI := heckeModuleBar p
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by
  intro t
  letI := heckeModuleBar p

  obtain ⟨φη, hφadd, hφpts⟩ := hC1 t

  set L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD with hLdef
  let R : Type := ↥(GaloisRep.ratLocalizedAt p)
  haveI : IsDiscreteValuationRing R := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p (Fact.out)
  haveI hIFR : IsFractionRing R ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI hpPrime : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
  haveI : IsLocalization.AtPrime R (Ideal.span {(p : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (Fact.out : p.Prime)
  haveI : Smooth D.toBase := hsm
  haveI : IsSeparated D.toBase := hsep
  haveI : QuasiCompact D.toBase := hqc
  haveI : LocallyOfFiniteType D.toBase := hlft
  haveI : Flat D.toBase := inferInstance

  obtain ⟨hInt, η, hη, hirr, hgen, hDVR⟩ :=
    AlgebraicGeometry.isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime p R D.toBase
      hpre (L.one (𝟙 _)).1 (L.one (𝟙 _)).2
  haveI := hInt
  haveI := hDVR

  obtain ⟨θ, φK, hθ₁, hθ₂, hφK, hφ⟩ := AsmRoot.exists_comparison_and_avatar R D.toBase φη

  have hlfp : ∀ n : ℕ, 0 < n → LocallyOfFinitePresentation (L.schemeNsmul n) := by
    intro n _
    haveI : IsLocallyNoetherian D.P := LocallyOfFiniteType.isLocallyNoetherian D.toBase
    haveI : LocallyOfFiniteType (L.schemeNsmul n) := by
      have : LocallyOfFiniteType (L.schemeNsmul n ≫ D.toBase) := by rw [L.schemeNsmul_over n]; infer_instance
      exact locallyOfFiniteType_of_comp (L.schemeNsmul n) D.toBase
    exact (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  have hsupply : ∀ ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ D.P,
      ζ ≫ D.toBase = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) →
      ∃ (s e : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) D.toBase)
        (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
        s.1.base (IsLocalRing.closedPoint ↥A) = ζ.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) ∧
        z ≫ pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 ∧
        zt ≫ pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = Spec.map (CommRingCat.ofHom A.subtype) ≫ e.1 ∧
        zt = z ≫ φη.1 := by
    intro ζ hζ
    obtain ⟨x, s, e, hsζ, hxs, hxe⟩ :=
      ModularCurve.exists_integralPoints_through_of_torsion_over_p p D.toBase L hcomm hnflat hlfp pts pts_add A hA
        hvi hptors t ζ hζ

    obtain ⟨z, hz, -⟩ := AsmRoot.exists_lift_genericFibre D.toBase (pts x).1 (pts x).2
    obtain ⟨zt, hzt, -⟩ := AsmRoot.exists_lift_genericFibre D.toBase (pts (t • x)).1 (pts (t • x)).2
    exact ⟨s, e, z, zt, hsζ, hz.trans hxs, hzt.trans hxe, hφpts x z zt hz hzt⟩

  obtain ⟨Dset, hDset, hDη, hpts'⟩ :=
    AlgebraicGeometry.exists_closedFibre_testCurves_of_integralPoints_through p R D.toBase η hη φη φK hφK θ hθ₁ hθ₂ hφ
      A hA hsupply

  obtain ⟨V, v, hv, hVη, hηV, hle, hlift⟩ :=
    hR1 (R := R) ℚ (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) η hη hirr φK hφK Dset hDset hDη hpts'

  obtain ⟨gA, hgA, hj⟩ :=
    NeronModelInfra.exists_extension_pullback_of_opens_extension_of_relativeGroupLaw p R D.toBase L η hη hirr φη φK
      θ hθ₁ hθ₂ hφ V v hv hVη hηV hle hlift

  have h31 : ∀ (𝔪 : Ideal ℤ) [𝔪.IsMaximal], ∃ (A' : Type) (_ : CommRing A') (_ : Algebra ℤ A')
      (_ : IsLocalization.AtPrime A' 𝔪) (_ : Algebra A' ℚ) (_ : IsScalarTower ℤ A' ℚ)
      (gA' : pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ A'))) ⟶ D.P),
      gA' ≫ D.toBase = pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ A'))) ≫ D.toBase ∧
      ∀ j : pullback D.toBase (specGenericFibreInclusion ℤ ℚ) ⟶
          pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ A'))),
        j ≫ pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ A'))) =
          pullback.fst D.toBase (specGenericFibreInclusion ℤ ℚ) →
        j ≫ gA' = φη.1 ≫ pullback.fst D.toBase (specGenericFibreInclusion ℤ ℚ) := by
    intro 𝔪 h𝔪

    obtain ⟨q, hqprime, hq𝔪⟩ : ∃ q : ℕ, q.Prime ∧ 𝔪 = Ideal.span {(q : ℤ)} :=
      AsmRoot.Int_exists_natPrime_eq_span_of_isMaximal 𝔪
    subst hq𝔪
    by_cases hqp : q = p
    · subst hqp
      exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, gA, hgA, hj⟩
    · haveI : Fact q.Prime := ⟨hqprime⟩
      have hqnp : ¬ q ∣ p := fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hqprime Fact.out).mp hd)
      obtain ⟨gA', hgA', hj'⟩ := hC2 q hqnp φη
      haveI : (Ideal.span {(q : ℤ)}).IsPrime := inferInstance
      refine ⟨↥(GaloisRep.ratLocalizedAt q), inferInstance, inferInstance, ?_, inferInstance, inferInstance, gA', hgA', hj'⟩
      exact GaloisRep.isLocalization_ratLocalizedAt hqprime

  obtain ⟨φ, -, hφhom, hφab⟩ :=
    NeronModelInfra.exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw D.toBase L φη
      (fun s x y => hφadd s x y) (ι' := JZero p) (fun x => (pts x).1) (fun x => (pts (t • x)).1)
      (fun x z zt hz hzt => hφpts x z zt hz hzt) (fun x => (pts x).2) (fun x => (pts (t • x)).2) h31
  exact ⟨φ, fun s x y => hφhom s x y, fun x => hφab x⟩

end S_ModularCurve_exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic
end P2MW
export P2MW.S_ModularCurve_exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic (solution)
