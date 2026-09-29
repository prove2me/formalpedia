-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.genOpH_U_smul_eq_cyclotomicCharacter_toZModPow_smul_of_mem_toricPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/706a00db-cf74-5a6f-884e-1fbfb5dc7733

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
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_genOpH_mem_toricPts
import Theorems.Thm_AlgebraicCurve_GluedPic0_nodeUnit_eq_zero_iff_of_constantsAreBase
import Theorems.Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_genOpH_U_smul_eq_cyclotomicCharacter_toZModPow_smul_of_mem_toricPts
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

noncomputable section

namespace A4Tor

open ModularCurve.JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

theorem nodeShift_fst_snd (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (σN : ↥O.ssFinset ≃ ↥O.ssFinset) (hσN : ∀ n : ↥O.ssFinset, (σN n).1.2 = n.1.1) (t : ↥O.ssFinset) :
    ((σN t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
        Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 ∧
    ((σN t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
        Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 := by
  have hnode : ∀ n : ↥O.ssFinset,
      (n : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p n.1.2 := fun n =>
    (mem_ssNodePairsQExp_iff _).mp ((O.mem_ssFinset_iff _).mp n.2) |>.2
  refine ⟨?_, ?_⟩
  · rw [hnode (σN t), hσN]
  · rw [hσN, ← hnode t]

theorem tate_of_levelwise (O : JHNeronObjectAtP p M H hpM A hA Λ) (S : Set ℕ) (g : CohCarrier.Gen M S)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Tt : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (hTt : ∀ x : TateModule ℓ (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.toricPts (ℓ ^ n))
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hlev : ∀ (n : ℕ) (y : JH M H), y ∈ O.toricPts (ℓ ^ n) →
      φ • y ∈ O.toricPts (ℓ ^ n) ∧ genOpH M H S g (φ • y) = (p : ℤ) • y ∧ φ • (genOpH M H S g y) = (p : ℤ) • y) :
    ∀ x ∈ Tt,
      JH.tateGaloisRep M H ℓ φ x ∈ Tt ∧
      tateGenOpH M H S ℓ g (JH.tateGaloisRep M H ℓ φ x) = (p : ℤ_[ℓ]) • x ∧
      JH.tateGaloisRep M H ℓ φ (tateGenOpH M H S ℓ g x) = (p : ℤ_[ℓ]) • x := by
  intro x hx
  rw [hTt] at hx
  have hp : ∀ n : ℕ, (((p : ℤ_[ℓ]) • x : TateModule ℓ (JH M H)) : ℕ → JH M H) n = (p : ℤ) • (x : ℕ → JH M H) n := by
    intro n
    rw [TateModule.smul_apply]
    refine TateModule.natCast_smul_eq_of_zmod_eq (TateModule.torsion x n) ?_
    rw [← TateModule.toZModPow_eq_appr, map_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rw [hTt]
    intro n
    exact (hlev n _ (hx n)).1
  · refine Subtype.ext (funext fun n => ?_)
    rw [hp n]
    exact (hlev n _ (hx n)).2.1
  · refine Subtype.ext (funext fun n => ?_)
    rw [hp n]
    exact (hlev n _ (hx n)).2.2

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem ext_unique_aux {X : Scheme.{0}} {f : X ⟶ base p} [IsSeparated f]
    (P Q : SchemeHomOver Λ.σA f) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA f) := by
    show IsSeparated (pullback.snd f Λ.σA); infer_instance
  have key : toFibrePt P = toFibrePt Q := by
    refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := ↥A) (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) (gY := 𝟙 (Spec (CommRingCat.of ↥A)))
      (gX := RelativeGroupLaw.baseChangeStr Λ.σA f) (toFibrePt P) (toFibrePt Q) ?_
    intro z
    have hz : z.1 = barPt A := by first | exact z.2 | simpa [barPt] using z.2
    rw [hz]
    show barPt A ≫ pullback.lift P.1 (𝟙 _) _ = barPt A ≫ pullback.lift Q.1 (𝟙 _) _
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h
    · simp only [Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have h1 : P.1 = (toFibrePt P).1 ≫ pullback.fst f Λ.σA := by
    show P.1 = pullback.lift P.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  have h2 : Q.1 = (toFibrePt Q).1 ≫ pullback.fst f Λ.σA := by
    show Q.1 = pullback.lift Q.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  rw [h1, h2, key]

theorem ext_unique (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (P Q : SchemeHomOver Λ.σA O.g) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated O.g := O.separated
  exact ext_unique_aux P Q h

def decAut (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) : ↥A →+* ↥A :=
  MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) ↥A ⟨σ, hσ⟩

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem subtype_comp_decAut (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    A.subtype.comp (decAut σ hσ) = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype :=
  RingHom.ext fun _ => rfl

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_comp_barPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A =
      barPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) := by
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, subtype_comp_decAut]

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_comp_genPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  rw [genPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext s
  show σ (algebraMap (baseRing p) (AlgebraicClosure ℚ) s) = algebraMap (baseRing p) (AlgebraicClosure ℚ) s
  rw [IsScalarTower.algebraMap_apply (baseRing p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_decAut_comp_σA (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA = Λ.σA := by
  have h : barPt A ≫ (Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA) = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, ← specMap_comp_barPt, Category.assoc, Λ.hσA, specMap_comp_genPt]
  set a := Spec.preimage (Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA) with ha
  set b := Spec.preimage Λ.σA with hb
  have ha' : Spec.map a = Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA := Spec.map_preimage _
  have hb' : Spec.map b = Λ.σA := Spec.map_preimage _
  rw [← ha', ← hb'] at h ⊢
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  haveI : Mono (CommRingCat.ofHom A.subtype) := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  rw [cancel_mono] at h2
  rw [h2]

def smulPt (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) (s : SchemeHomOver Λ.σA O.g) : SchemeHomOver Λ.σA O.g :=
  ⟨Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ s.1, by rw [Category.assoc, s.2, specMap_decAut_comp_σA]⟩

theorem pts_smul_eq (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) {x : JH M H} {s : SchemeHomOver Λ.σA O.g} (hs : (O.pts x).1 = barPt A ≫ s.1) :
    (O.pts (σ • x)).1 = barPt A ≫ (smulPt O hσ s).1 := by
  show _ = barPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ s.1
  rw [O.pts_galois, hs, ← Category.assoc, specMap_comp_barPt, Category.assoc]

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
private theorem _root_.A4Tor.exists_algHom_valuationSubring_of_muCoord {t m : ℕ} (hm : 0 < m)
    (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    ∃ χA : muCoord ↥A t m →ₐ[↥A] ↥A, χ = (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA := by
  classical

  have hroot : ∀ g : Fin t → ZMod m, (χ (AddMonoidAlgebra.single g 1)) ^ m = 1 := by
    intro g
    rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
    have hg : m • g = 0 := by
      funext i
      show m • g i = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hg]
    exact map_one χ
  have hmem : ∀ g : Fin t → ZMod m, χ (AddMonoidAlgebra.single g 1) ∈ A := by
    intro g
    have hint : IsIntegral ↥A (χ (AddMonoidAlgebra.single g 1)) := by
      refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hroot g, sub_self]
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint
    rw [← hy]
    exact y.2

  let φ : Multiplicative (Fin t → ZMod m) →* ↥A :=
    { toFun := fun g => ⟨χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1), hmem _⟩
      map_one' := Subtype.ext (by
        show χ (AddMonoidAlgebra.single (0 : Fin t → ZMod m) 1) = 1
        exact map_one χ)
      map_mul' := fun g h => Subtype.ext (by
        show χ (AddMonoidAlgebra.single (Multiplicative.toAdd (g * h)) 1) =
          χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1) * χ (AddMonoidAlgebra.single (Multiplicative.toAdd h) 1)
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl) }
  refine ⟨AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod m) φ, ?_⟩
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, AddMonoidAlgebra.lift_single, one_smul]
  rfl

p2m_export "A4Tor" "exists_algHom_valuationSubring_of_muCoord"

theorem exists_toricSection (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (χA : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    ∃ s : SchemeHomOver Λ.σA O.g,
      (O.pts (O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA))).1 = barPt A ≫ s.1 ∧
      (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s).1 =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χA.toRingHom)) ≫ (O.toricLift m hm).1 ≫
          pullback.fst O.g Λ.σA := by
  have hbase : Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ muStr ↥A O.toricRank m = 𝟙 _ := by
    rw [muStr, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χA.toRingHom.comp (algebraMap ↥A (muCoord ↥A O.toricRank m)) = RingHom.id ↥A := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  refine ⟨⟨Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (O.toricLift m hm).1]
    have h2 : (O.toricLift m hm).1 ≫ pullback.snd O.g Λ.σA = muStr ↥A O.toricRank m := (O.toricLift m hm).2
    rw [h2, ← Category.assoc, hbase, Category.id_comp]
  · show (O.pts (O.pts.symm _)).1 = _
    rw [Equiv.apply_symm_apply]
    show ((Spec.map (CommRingCat.ofHom ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).toRingHom) ≫ (O.toricLift m hm).1) ≫
      pullback.fst O.g Λ.σA) = barPt A ≫ Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA
    have h3 : ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).toRingHom = (algebraMap ↥A (AlgebraicClosure ℚ)).comp χA.toRingHom := rfl
    rw [h3, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc]
    rfl
  · show resPt A ≫ Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA = _
    rw [resPt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem ptsSp_symm_eq_nodeUnit_of_coe_eq (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (y : SchemeHomOver (resPt A ≫ Λ.σA) O.g) (wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
    (h : y.1 = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1) :
    O.ptsSp.symm y = GluedPic0.nodeUnit O.ssFinset wb := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext h

end A4Tor

end

namespace A4Tor

open ModularCurve.JHNeronObjectAtP

theorem pow_eq_one_of_coe_eq_rootsOfUnity {A : ValuationSubring (AlgebraicClosure ℚ)} {m : ℕ} (u : ↥A)
    (ζ : ↥(rootsOfUnity m (AlgebraicClosure ℚ)))
    (h : (u : AlgebraicClosure ℚ) = (((ζ : ↥(rootsOfUnity m (AlgebraicClosure ℚ))) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) :
    u ^ m = 1 := by
  apply Subtype.ext
  show ((u ^ m : ↥A) : AlgebraicClosure ℚ) = 1
  rw [SubmonoidClass.coe_pow, h, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity m _).mp ζ.2, Units.val_one]

theorem mem_valuationSubring_of_pow_eq_one (A : ValuationSubring (AlgebraicClosure ℚ)) {m : ℕ} (hm : 0 < m)
    {t : AlgebraicClosure ℚ} (ht : t ^ m = 1) : t ∈ A := by
  have hint : IsIntegral ↥A t := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, ht, sub_self]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint
  rw [← hy]
  exact y.2

private theorem _root_.A4Tor.hasEnoughRootsOfUnity_algebraicClosure (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (AlgebraicClosure ℚ) n := by
  refine ⟨?_, rootsOfUnity.isCyclic _ _⟩
  have hdeg : (Polynomial.cyclotomic n (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

p2m_export "A4Tor" "hasEnoughRootsOfUnity_algebraicClosure"
end A4Tor

namespace A4Tor

theorem apply_eq_nsmul_apply_of_coe {X L : Type*} [AddZeroClass X] [CommMonoid L] {m : ℕ}
    (f g : X →+ Additive ↥(rootsOfUnity m L)) (a : X) (p : ℕ) (u₁ u₂ : L)
    (hu₁ : u₁ = ((Additive.toMul (f a) : ↥(rootsOfUnity m L)) : Lˣ))
    (hu₂ : u₂ = ((Additive.toMul (g a) : ↥(rootsOfUnity m L)) : Lˣ))
    (hu : u₁ = u₂ ^ p) :
    f a = (p • g) a := by
  rw [AddMonoidHom.nsmul_apply]
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  apply Subtype.ext
  rw [SubgroupClass.coe_pow]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ← hu₁, ← hu₂, hu]

theorem eq_zsmul_of_subtype_eq_nsmul {G : Type*} [AddCommGroup G] (S : AddSubgroup G) (z y : G) (hz : z ∈ S) (hy : y ∈ S)
    (p : ℕ) (h : (⟨z, hz⟩ : ↥S) = p • ⟨y, hy⟩) : z = (p : ℤ) • y := by
  have h' := congrArg Subtype.val h
  rw [natCast_zsmul]
  simpa only [AddSubmonoidClass.coe_nsmul] using h'

end A4Tor

namespace ATPSkel

open ModularCurve.JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

omit [IsAlgClosed (ResidueField ↥A)] in

private theorem _root_.ATPSkel.exists_algHom_valuationSubring_of_muCoord {t m : ℕ} (hm : 0 < m)
    (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    ∃ χA : muCoord ↥A t m →ₐ[↥A] ↥A, χ = (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA := by
  classical
  have hroot : ∀ g : Fin t → ZMod m, (χ (AddMonoidAlgebra.single g 1)) ^ m = 1 := by
    intro g
    rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
    have hg : m • g = 0 := by
      funext i
      show m • g i = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hg]
    exact map_one χ
  have hmem : ∀ g : Fin t → ZMod m, χ (AddMonoidAlgebra.single g 1) ∈ A := by
    intro g
    have hint : IsIntegral ↥A (χ (AddMonoidAlgebra.single g 1)) := by
      refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hroot g, sub_self]
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint
    rw [← hy]
    exact y.2
  let φ : Multiplicative (Fin t → ZMod m) →* ↥A :=
    { toFun := fun g => ⟨χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1), hmem _⟩
      map_one' := Subtype.ext (by
        show χ (AddMonoidAlgebra.single (0 : Fin t → ZMod m) 1) = 1
        exact map_one χ)
      map_mul' := fun g h => Subtype.ext (by
        show χ (AddMonoidAlgebra.single (Multiplicative.toAdd (g * h)) 1) =
          χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1) * χ (AddMonoidAlgebra.single (Multiplicative.toAdd h) 1)
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl) }
  refine ⟨AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod m) φ, ?_⟩
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, AddMonoidAlgebra.lift_single, one_smul]
  rfl

p2m_export "ATPSkel" "exists_algHom_valuationSubring_of_muCoord"
omit [Fact p.Prime] in
theorem specMap_comp_genPt' (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  rw [genPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext s
  show σ (algebraMap (baseRing p) (AlgebraicClosure ℚ) s) = algebraMap (baseRing p) (AlgebraicClosure ℚ) s
  rw [IsScalarTower.algebraMap_apply (baseRing p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

omit [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in

theorem specMap_decRestrict_comp_σA (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (dE : ↥A ≃+* ↥A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hdE : ∀ a : ↥A, ((dE a : ↥A) : AlgebraicClosure ℚ) = σ a) :
    Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA = Λ.σA := by
  have hsub : A.subtype.comp dE.toRingHom = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype :=
    RingHom.ext fun a => hdE a
  have hbar : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A =
      barPt A ≫ Spec.map (CommRingCat.ofHom dE.toRingHom) := by
    rw [barPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hsub]
  have h : barPt A ≫ (Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA) = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, ← hbar, Category.assoc, Λ.hσA, specMap_comp_genPt']
  set a := Spec.preimage (Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA) with ha
  set b := Spec.preimage Λ.σA with hb
  have ha' : Spec.map a = Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA := Spec.map_preimage _
  have hb' : Spec.map b = Λ.σA := Spec.map_preimage _
  rw [← ha', ← hb'] at h ⊢
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  haveI : Mono (CommRingCat.ofHom A.subtype) := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  rw [cancel_mono] at h2
  rw [h2]

section conv
variable {S' : Type} [CommRing S'] {L' : Type} [CommRing L'] [Algebra S' L'] {G' : Type} [AddMonoid G']

theorem convMul_apply_single (c c' : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (v : G') :
    (c * c') (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem convOne_apply_single (v : G') :
    (1 : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]

theorem convPow_apply_single (c : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (n : ℕ) (v : G') :
    (c ^ n) (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_single]
  | succ n ih => rw [pow_succ, pow_succ, convMul_apply_single, ih]

end conv

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in

private theorem _root_.ATPSkel.hasEnoughRootsOfUnity_algebraicClosure (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (AlgebraicClosure ℚ) n := by
  refine ⟨?_, rootsOfUnity.isCyclic _ _⟩
  have hdeg : (Polynomial.cyclotomic n (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

p2m_export "ATPSkel" "hasEnoughRootsOfUnity_algebraicClosure"

theorem tate_of_levelwise' (O : JHNeronObjectAtP p M H hpM A hA Λ) (S : Set ℕ) (g : CohCarrier.Gen M S)
    (Tt : Submodule ℤ_[p] (TateModule p (JH M H)))
    (hTt : ∀ x : TateModule p (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj p (JH M H) n x ∈ O.toricPts (p ^ n))
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℤ_[p])
    (hlev : ∀ (n : ℕ) (y : JH M H), y ∈ O.toricPts (p ^ n) →
      φ • y ∈ O.toricPts (p ^ n) ∧ genOpH M H S g (φ • y) = ((a.appr n : ℕ) : ℤ) • y ∧
        φ • (genOpH M H S g y) = ((a.appr n : ℕ) : ℤ) • y) :
    ∀ x ∈ Tt,
      JH.tateGaloisRep M H p φ x ∈ Tt ∧
      tateGenOpH M H S p g (JH.tateGaloisRep M H p φ x) = a • x ∧
      JH.tateGaloisRep M H p φ (tateGenOpH M H S p g x) = a • x := by
  intro x hx
  rw [hTt] at hx
  refine ⟨?_, ?_, ?_⟩
  · rw [hTt]
    intro n
    exact (hlev n _ (hx n)).1
  · refine Subtype.ext (funext fun n => ?_)
    rw [TateModule.smul_apply]
    exact (hlev n _ (hx n)).2.1
  · refine Subtype.ext (funext fun n => ?_)
    rw [TateModule.smul_apply]
    exact (hlev n _ (hx n)).2.2

end ATPSkel

open ModularCurve.JHNeronObjectAtP
open A4Tor in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (S : Set ℕ) (ℓ : ℕ) [Fact ℓ.Prime]

    (hTOR : ∀ (perm : Equiv.Perm ↥O.ssFinset)
      (hperm : ∀ t : ↥O.ssFinset,
        ((perm t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
            Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
            (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
              Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 ∧
        ((perm t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
            Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
            (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
              Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2)
      (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
      (x : JH M H) (s s' : SchemeHomOver Λ.σA O.g)
      (hs : (O.pts x).1 = barPt A ≫ s.1) (hs' : (O.pts (φ • x)).1 = barPt A ≫ s'.1)
      (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
      (hw : O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.nodeUnit O.ssFinset w),
      O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s') = GluedPic0.nodeUnit O.ssFinset (fun t => p • w (perm.symm t)))

    (σN : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσN : ∀ n : ↥O.ssFinset, (σN n).1.2 = n.1.1)
    (hUPtor : ∀ w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w))
          (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
        GluedPic0.nodeUnit O.ssFinset (w ∘ σN))

    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ) :
    ∀ (k : ℕ) (xt : JH M H), xt ∈ O.toricPts (ℓ ^ k) →
      φ • xt ∈ O.toricPts (ℓ ^ k) ∧
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (φ • xt) =
        (PadicInt.toZModPow k (((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ φ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))).val • xt := by
  classical
  intro k xt hxt
  by_cases hℓ : ℓ = p
  · subst ℓ
    have core : ∀ (n : ℕ) (y : JH M H), y ∈ O.toricPts (p ^ n) →
        φ • y ∈ O.toricPts (p ^ n) ∧
        genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (φ • y) = ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n : ℕ) : ℤ) • y ∧
        φ • (genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) y) = ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n : ℕ) : ℤ) • y := by
      haveI : PerfectField (ResidueField ↥A) := IsAlgClosed.perfectField (ResidueField ↥A)

      have hdE : ∃ dE : ↥A ≃+* ↥A, (∀ a : ↥A, dE a = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • a) :=
        ⟨MulSemiringAction.toRingEquiv _ _ (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)), fun a => rfl⟩
      obtain ⟨dE, hdEa⟩ := hdE
      have hres : (IsLocalRing.residue ↥A).comp dE.toRingHom = (frobenius (ResidueField ↥A) p).comp (IsLocalRing.residue ↥A) := by
        refine RingHom.ext fun a => ?_
        show IsLocalRing.residue ↥A (dE a) = (IsLocalRing.residue ↥A a) ^ p
        rw [hdEa, IsLocalRing.ResidueField.residue_smul]
        exact hφ.smul_residue_eq _
      have hdσ : Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA = Λ.σA :=
        ATPSkel.specMap_decRestrict_comp_σA Λ dE φ (fun a => by rw [hdEa]; rfl)
      have hbase : Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ resPt A ≫ Λ.σA = resPt A ≫ Λ.σA := by
        have h1 : resPt A ≫ Spec.map (CommRingCat.ofHom dE.toRingHom) = Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ resPt A := by
          rw [resPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hres]
        rw [← Category.assoc, ← h1, Category.assoc, hdσ]

      have hΞE : ∃ ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA),
          ΞG ≫ pullback.fst _ _ = pullback.fst _ _ ∧
          ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) := by
        refine ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p))) ?_,
          pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
        rw [pullback.condition, Category.assoc, hbase]
      obtain ⟨ΞG, hΞ₁, hΞ₂⟩ := hΞE

      have hψ : (frobeniusEquiv (ResidueField ↥A) p).toRingHom = frobenius (ResidueField ↥A) p := rfl
      have hLA := ModularCurve.JHNeronObjectAtP.exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
        p M H hpM A hA Λ hΛ O (frobeniusEquiv (ResidueField ↥A) p) ΞG hΞ₁ hΞ₂
      obtain ⟨P₀, hP₀⟩ := hLA

      have hTS := ModularCurve.JHNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
        p M H hpM A hA Λ hΛ O (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)) (fun s x y => O.hecke_mul S _ s x y)
      obtain ⟨M₀, hM₀⟩ := hTS

      have hLB := ModularCurve.JHNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
        p M H hpM A hA Λ O ΞG hΞ₁ hΞ₂ P₀ hP₀ S M₀ hM₀ hTOR σN hσN hUPtor φ hφ hφD
      obtain ⟨hPM, hMP⟩ := hLB

      intro n y hy
      have hm : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

      have hLD := ModularCurve.JHNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
        p M H hpM A hA Λ O ΞG hΞ₁ hΞ₂ P₀ hP₀ φ hφ hφD (p ^ n) hm
      obtain ⟨Pbar, hPbar, hLDχ⟩ := hLD

      have hTM := ModularCurve.JHNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
        p M H hpM A hA Λ hΛ O (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)) (fun s x y => O.hecke_mul S _ s x y) M₀ hM₀ (p ^ n) hm
      obtain ⟨Mbar, hMbar, hTMχ⟩ := hTM

      have hH1 := ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
        p M H hpM A hA Λ O (p ^ n) hm
      obtain ⟨hconv, -, hmem, -⟩ := hH1

      have hPMbar : Pbar.comp Mbar = AddMonoidHom.id _ ∧ Mbar.comp Pbar = AddMonoidHom.id _ := by
        haveI : NeZero (p ^ n) := ⟨hm.ne'⟩
        have hsurj : ∀ v : Fin O.toricRank → ZMod (p ^ n), ∃ z : Fin O.toricRank → ℤ,
            (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod (p ^ n))).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)) z = v :=
          fun v => ⟨fun i => ((v i).cast : ℤ), funext fun i => by
            show (((v i).cast : ℤ) : ZMod (p ^ n)) = v i
            exact ZMod.intCast_zmod_cast (v i)⟩
        have hPbar' := fun z => DFunLike.congr_fun hPbar z
        have hMbar' := fun z => DFunLike.congr_fun hMbar z
        have hPM' := fun z => DFunLike.congr_fun hPM z
        have hMP' := fun z => DFunLike.congr_fun hMP z
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hPbar' hMbar' hPM' hMP'
        constructor
        · refine AddMonoidHom.ext fun v => ?_
          obtain ⟨z, rfl⟩ := hsurj v
          rw [AddMonoidHom.comp_apply, hMbar', hPbar', hPM', AddMonoidHom.id_apply]
        · refine AddMonoidHom.ext fun v => ?_
          obtain ⟨z, rfl⟩ := hsurj v
          rw [AddMonoidHom.comp_apply, hPbar', hMbar', hMP', AddMonoidHom.id_apply]

      have hUtor : ∀ χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ,
          genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (O.toricPoint (p ^ n) hm χ) =
            O.toricPoint (p ^ n) hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := by
        intro χ
        apply O.pts.injective
        apply Subtype.ext
        rw [O.hecke_pts]
        show (O.pts (O.pts.symm _)).1 ≫ _ = (O.pts (O.pts.symm _)).1
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        have h := congrArg (fun w => w.1 ≫ pullback.fst O.g Λ.σA) (hTMχ χ)
        simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst] at h
        show (((muPt A O.toricRank (p ^ n) χ).1 ≫ (O.toricLift (p ^ n) hm).1) ≫ pullback.fst O.g Λ.σA) ≫
            (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)).1 =
          ((muPt A O.toricRank (p ^ n) (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 ≫ (O.toricLift (p ^ n) hm).1) ≫
            pullback.fst O.g Λ.σA
        simpa only [Category.assoc] using h

      have hcyc : ∀ (χ χφ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] ↥A),
          (∀ g : Fin O.toricRank → ZMod (p ^ n),
            χφ (AddMonoidAlgebra.single g 1) = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • χ (AddMonoidAlgebra.single g 1)) →
          χφ = χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
            ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)) := by
        intro χ χφ hχφ
        haveI hEn : ∀ i, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (p ^ i) := fun i =>
          haveI : NeZero (p ^ i) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
          ATPSkel.hasEnoughRootsOfUnity_algebraicClosure _
        refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
        intro g
        rw [hχφ, AlgHom.comp_apply]
        have hmd : AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
            ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)
            (AddMonoidAlgebra.single g (1 : ↥A)) =
            AddMonoidAlgebra.single ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • g) 1 := by
          show AddMonoidAlgebra.mapDomainRingHom ↥A _ (AddMonoidAlgebra.single g 1) = _
          rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
          rfl
        have hsp : AddMonoidAlgebra.single ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • g) (1 : ↥A) =
            (AddMonoidAlgebra.single g (1 : ↥A)) ^ (((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) := by
          rw [AddMonoidAlgebra.single_pow, one_pow]
        rw [hmd, hsp, map_pow]

        set u : ↥A := χ (AddMonoidAlgebra.single g 1) with hu
        have hupow : u ^ (p ^ n) = 1 := by
          rw [hu, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
          have hg : (p ^ n) • g = 0 := by
            funext i
            show (p ^ n) • g i = 0
            rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
          rw [hg]
          exact map_one χ
        apply Subtype.ext
        show φ (u : AlgebraicClosure ℚ) = ((u ^ _ : ↥A) : AlgebraicClosure ℚ)
        rw [SubmonoidClass.coe_pow]
        have hval : ((u : AlgebraicClosure ℚ)) ^ p ^ n = 1 := by
          rw [← SubmonoidClass.coe_pow, hupow]; rfl
        have hspec := cyclotomicCharacter.spec p (L := AlgebraicClosure ℚ) (n := n) φ.toRingEquiv (u : AlgebraicClosure ℚ) hval
        rw [show (φ.toRingEquiv : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (u : AlgebraicClosure ℚ) = φ (u : AlgebraicClosure ℚ) from rfl] at hspec
        rw [hspec]
        congr 1
        show (PadicInt.toZModPow n _).val = _
        rw [TateModule.toZModPow_eq_appr, ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)]

      have hhom : ∀ (c : ℕ) (χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ),
          O.toricPoint (p ^ n) hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _))) =
            ((c : ℕ) : ℤ) • O.toricPoint (p ^ n) hm χ := by
        intro c χ
        have hpow : χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _)) = ((WithConv.toConv χ) ^ c).ofConv := by
          refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
          intro g
          rw [AlgHom.comp_apply]
          have hmd : AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _) (AddMonoidAlgebra.single g (1 : ↥A)) =
              AddMonoidAlgebra.single (c • g) 1 := by
            show AddMonoidAlgebra.mapDomainRingHom ↥A _ (AddMonoidAlgebra.single g 1) = _
            rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
            rfl
          rw [hmd, ← one_pow c, ← AddMonoidAlgebra.single_pow, map_pow, one_pow]
          exact (ATPSkel.convPow_apply_single (WithConv.toConv χ) c g).symm
        rw [hpow]
        have h1 : O.toricPoint (p ^ n) hm (1 : WithConv (muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
          have h := hconv 1 1
          rw [mul_one] at h
          exact left_eq_add.mp h
        have key : ∀ k : ℕ, O.toricPoint (p ^ n) hm ((WithConv.toConv χ) ^ k).ofConv = ((k : ℕ) : ℤ) • O.toricPoint (p ^ n) hm χ := by
          intro k
          induction k with
          | zero => rw [pow_zero, h1, Nat.cast_zero, zero_zsmul]
          | succ k ih =>
            rw [pow_succ, hconv, ih, Nat.cast_succ, add_zsmul, one_zsmul]
        exact key c

      have hcomp : ∀ (χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] ↥A) (f g : (Fin O.toricRank → ZMod (p ^ n)) →+ (Fin O.toricRank → ZMod (p ^ n))),
          ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A f))).comp
              (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A g) =
            (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (f.comp g))) := by
        intro χ f g
        rw [AddMonoidAlgebra.mapDomainAlgHom_comp]
        rfl

      obtain ⟨χ, rfl⟩ := (hmem y).mp hy
      obtain ⟨χA, hχA⟩ := ATPSkel.exists_algHom_valuationSubring_of_muCoord (A := A) hm χ
      subst hχA
      obtain ⟨χφ, hχφ, hφι⟩ := hLDχ χA
      refine ⟨?_, ?_, ?_⟩
      ·
        rw [hφι]
        exact (hmem _).mpr ⟨_, rfl⟩
      ·
        rw [hφι, hUtor, hcomp, hPMbar.1, hcyc χA χφ hχφ, AddMonoidAlgebra.mapDomainAlgHom_id, AlgHom.comp_id]
        exact hhom _ ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)
      ·
        rw [hUtor]
        obtain ⟨χφ', hχφ', hφι'⟩ := hLDχ (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))
        have h3 : ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar) =
            (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := rfl
        rw [h3, hφι', hcyc _ χφ' hχφ']
        have hcm : ((χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
            ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _))).comp
            (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Pbar) =
            χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
              ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)) := by
          have hsw : Mbar.comp ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _) =
              ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _).comp Mbar := by
            refine AddMonoidHom.ext fun v => ?_
            simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, map_nsmul]
          rw [AlgHom.comp_assoc, AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
            ← AddMonoidHom.comp_assoc, hsw, AddMonoidHom.comp_assoc, hPMbar.2, AddMonoidHom.comp_id]
        rw [hcm]
        exact hhom _ ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)

    obtain ⟨h1, h2, -⟩ := core k xt hxt
    refine ⟨h1, ?_⟩
    rw [h2, natCast_zsmul, TateModule.toZModPow_eq_appr, ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)]
  ·

    have hpermσ := fun t => A4Tor.nodeShift_fst_snd O σN hσN t

    haveI hEn : ∀ i, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (ℓ ^ i) := fun i =>
      haveI : NeZero (ℓ ^ i) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
      A4Tor.hasEnoughRootsOfUnity_algebraicClosure _
    have hℓp : ¬ p ∣ ℓ := fun h => hℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
    have hmκ : ∀ n : ℕ, ((ℓ ^ n : ℕ) : ResidueField ↥A) ≠ 0 := fun n => by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ ((CharP.cast_eq_zero_iff (ResidueField ↥A) p ℓ).not.mpr hℓp)
    have hχn : ∀ n : ℕ, PadicInt.toZModPow n (((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ φ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) =
        ((p : ℕ) : ZMod (ℓ ^ n)) := by
      intro n
      obtain ⟨hinjμ, -⟩ := ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
        (AlgebraicClosure ℚ) A (ℓ ^ n) (hmκ n)
      rw [cyclotomicCharacter.toZModPow]
      refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) _ φ.toRingEquiv (c := ((p : ℕ) : ZMod (ℓ ^ n))) ?_).symm
      intro t ht
      have htm : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ ^ n) = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity (ℓ ^ n) t).mp ht, Units.val_one]
      have htA : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A :=
        A4Tor.mem_valuationSubring_of_pow_eq_one A (pow_pos (Fact.out : ℓ.Prime).pos n) htm
      have hta : (⟨_, htA⟩ : ↥A) ^ (ℓ ^ n) = 1 := Subtype.ext (by
        show (((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) ^ (ℓ ^ n) = 1
        exact htm)
      have hφa : ((⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • (⟨_, htA⟩ : ↥A)) = (⟨_, htA⟩ : ↥A) ^ p := by
        refine hinjμ _ _ ?_ ?_ ?_
        · rw [← smul_pow', hta, smul_one]
        · rw [← pow_mul, mul_comm, pow_mul, hta, one_pow]
        · rw [IsLocalRing.ResidueField.residue_smul, map_pow]
          exact hφ.smul_residue_eq _
      have hval : φ ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ p := by
        have h := congrArg Subtype.val hφa
        simp only [SubmonoidClass.coe_pow] at h
        exact h
      show φ ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = (((t ^ ((p : ℕ) : ZMod (ℓ ^ n)).val : (AlgebraicClosure ℚ)ˣ)) : AlgebraicClosure ℚ)
      rw [Units.val_pow_eq_pow_val, ZMod.val_natCast, hval]
      conv_lhs => rw [← Nat.div_add_mod p (ℓ ^ n), pow_add, pow_mul, htm, one_pow, one_mul]

    have core : ∀ (n : ℕ) (y : JH M H), y ∈ O.toricPts (ℓ ^ n) →
        φ • y ∈ O.toricPts (ℓ ^ n) ∧
        genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (φ • y) = (p : ℤ) • y ∧
        φ • (genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) y) = (p : ℤ) • y := by
      intro n y hy

      have hm : 0 < ℓ ^ n := pow_pos (Fact.out : ℓ.Prime).pos n
      have hmp : (ℓ ^ n).Coprime p := Nat.Coprime.pow_left n ((Nat.coprime_primes Fact.out Fact.out).mpr hℓ)

      haveI hCO : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
        AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
          (𝔛.Mfib A hA ρ hρ).toBase (𝔛.Mfib A hA ρ hρ).ffEquiv (𝔛.Mfib A hA ρ hρ).ffEquiv_algebraMap
      have hne : O.ssFinset.Nonempty := Finset.card_pos.mp (by have := O.toricRank_succ_eq_card; omega)
      obtain ⟨s₀, hs₀⟩ := hne
      have hdeg : (s₀.2 : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).deg = 1 := by
        haveI := IsCurveOver.finiteResidue (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)) s₀.2
        exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField s₀.2).mpr
          IsAlgClosed.algebraMap_bijective_of_isIntegral.2
      have hCB : ConstantsAreBase (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
        AlgebraicCurve.constantsAreBase_of_deg_eq_one s₀.2 hdeg
      have hker : ∀ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
          GluedPic0.nodeUnit O.ssFinset wb = 0 → ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c := fun wb h =>
        (AlgebraicCurve.GluedPic0.nodeUnit_eq_zero_iff_of_constantsAreBase hCB _ wb).mp h

      have hTR := ModularCurve.JHNeronObjectAtP.exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit
        p M H hpM A hA Λ O (ℓ ^ n) hm hmp hker
      obtain ⟨e, hpin, -, -⟩ := hTR
      have hH1 := ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
        p M H hpM A hA Λ O (ℓ ^ n) hm
      obtain ⟨-, -, hmem, -⟩ := hH1
      have hH4 := ModularCurve.JHNeronObjectAtP.exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
        p M H hpM A hA Λ O (ℓ ^ n) hm
      obtain ⟨hwbex, -, -⟩ := hH4
      have hH2 := ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
        (AlgebraicClosure ℚ) A (ℓ ^ n) (hmκ n)
      obtain ⟨hinjμ, -⟩ := hH2
      have hU := ModularCurve.JHNeronObjectAtP.genOpH_mem_toricPts p M H hpM A hA Λ hΛ O S (ℓ ^ n) hm
        (CohCarrier.Gen.U p (Fact.out) hpM)

      obtain ⟨χ, rfl⟩ := (hmem y).mp hy
      obtain ⟨χA, hχA⟩ := A4Tor.exists_algHom_valuationSubring_of_muCoord (A := A) hm χ
      subst hχA
      obtain ⟨s, hs, hssp⟩ := A4Tor.exists_toricSection O _ hm χA
      obtain ⟨wb, hwb⟩ := hwbex χA
      have hw : O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.nodeUnit O.ssFinset wb :=
        A4Tor.ptsSp_symm_eq_nodeUnit_of_coe_eq O _ wb (hssp.trans hwb)
      obtain ⟨hyT, hey⟩ := hpin χA wb hwb

      have hcmp : ∀ (z : JH M H), z ∈ O.toricPts (ℓ ^ n) → ∀ (sz : SchemeHomOver Λ.σA O.g),
          (O.pts z).1 = barPt A ≫ sz.1 →
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ sz) = GluedPic0.nodeUnit O.ssFinset (fun t => p • wb t) →
          z = (p : ℤ) • O.toricPoint (ℓ ^ n) hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA) := by
        intro z hz sz hsz hread
        obtain ⟨χz, rfl⟩ := (hmem z).mp hz
        obtain ⟨χzA, hχzA⟩ := A4Tor.exists_algHom_valuationSubring_of_muCoord (A := A) hm χz
        subst hχzA
        obtain ⟨sz', hsz', hsz'sp⟩ := A4Tor.exists_toricSection O _ hm χzA
        have hss : sz' = sz := A4Tor.ext_unique O _ _ (hsz'.symm.trans hsz)
        subst hss
        have hspz : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χzA.toRingHom)) ≫ (O.toricLift (ℓ ^ n) hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (fun t => p • wb t))).1 :=
          hsz'sp.symm.trans (congrArg Subtype.val ((Equiv.symm_apply_eq _).mp hread))
        obtain ⟨hzT, hez⟩ := hpin χzA (fun t => p • wb t) hspz
        have hE : e ⟨_, hzT⟩ = p • e ⟨_, hyT⟩ := by
          refine AddMonoidHom.ext fun a => ?_
          obtain ⟨u₁, hu₁, hru₁⟩ := hez a
          obtain ⟨u₂, hu₂, hru₂⟩ := hey a
          have hpow₁ : u₁ ^ (ℓ ^ n) = 1 := A4Tor.pow_eq_one_of_coe_eq_rootsOfUnity u₁ _ hu₁
          have hpow₂ : (u₂ ^ p) ^ (ℓ ^ n) = 1 := by
            rw [← pow_mul, mul_comm, pow_mul, A4Tor.pow_eq_one_of_coe_eq_rootsOfUnity u₂ _ hu₂, one_pow]
          have hres : IsLocalRing.residue ↥A u₁ = IsLocalRing.residue ↥A (u₂ ^ p) := by
            rw [hru₁, map_pow, hru₂, ← Units.val_pow_eq_pow_val, ← map_pow]
            rfl
          have hu : u₁ = u₂ ^ p := hinjμ u₁ (u₂ ^ p) hpow₁ hpow₂ hres
          exact A4Tor.apply_eq_nsmul_apply_of_coe _ _ a p (u₁ : AlgebraicClosure ℚ) (u₂ : AlgebraicClosure ℚ) hu₁ hu₂
            ((congrArg Subtype.val hu).trans (SubmonoidClass.coe_pow u₂ p))
        exact A4Tor.eq_zsmul_of_subtype_eq_nsmul _ _ _ hzT hyT p (e.injective (hE.trans (map_nsmul e p ⟨_, hyT⟩).symm))

      obtain ⟨χ', hχ'⟩ := O.toricLift_dec (ℓ ^ n) hm φ hφD ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)
      have hφy : φ • O.toricPoint (ℓ ^ n) hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA) ∈ O.toricPts (ℓ ^ n) := by
        have h' : φ • O.toricPoint (ℓ ^ n) hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA) = O.toricPoint (ℓ ^ n) hm χ' := hχ'
        rw [h']
        exact (hmem _).mpr ⟨χ', rfl⟩

      have hsφ := A4Tor.pts_smul_eq O hφD hs
      have hwφ := hTOR σN hpermσ φ hφ hφD _ s (A4Tor.smulPt O hφD s) hs hsφ wb hw

      have hL2 : genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (φ • O.toricPoint (ℓ ^ n) hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)) =
          (p : ℤ) • O.toricPoint (ℓ ^ n) hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA) := by
        refine hcmp _ (hU _ hφy) (NeronModelInfra.schemeHomOverComp (A4Tor.smulPt O hφD s) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) ?_ ?_
        · rw [O.hecke_pts, hsφ, Category.assoc]
          rfl
        · have h1 : NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
                (NeronModelInfra.schemeHomOverComp (A4Tor.smulPt O hφD s) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
              NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (fun t => p • wb (σN.symm t))))
                (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)) :=
            (NeronModelInfra.schemeHomOverComp_assoc _ _ _).symm.trans
              (congrArg (fun u => NeronModelInfra.schemeHomOverComp u (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))
                (O.ptsSp.symm_apply_eq.mp hwφ))
          rw [h1, hUPtor]
          congr 1
          funext t
          show p • wb (σN.symm (σN t)) = p • wb t
          rw [Equiv.symm_apply_apply]

      have hsU : (O.pts (genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (O.toricPoint (ℓ ^ n) hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)))).1 =
          barPt A ≫ (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))).1 := by
        rw [O.hecke_pts, hs, Category.assoc]
        rfl
      have hwU : O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
          (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) = GluedPic0.nodeUnit O.ssFinset (wb ∘ σN) := by
        have h1 : NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
              (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
            NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)) :=
          (NeronModelInfra.schemeHomOverComp_assoc _ _ _).symm.trans
            (congrArg (fun u => NeronModelInfra.schemeHomOverComp u (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))
              (O.ptsSp.symm_apply_eq.mp hw))
        rw [h1, hUPtor]
      have hUy : genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (O.toricPoint (ℓ ^ n) hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)) ∈
          O.toricPts (ℓ ^ n) := hU _ hyT
      have hs' := A4Tor.pts_smul_eq O hφD hsU
      have hw' := hTOR σN hpermσ φ hφ hφD _ (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))
        (A4Tor.smulPt O hφD (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) hsU hs' (wb ∘ σN) hwU
      have hφUy : φ • genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (O.toricPoint (ℓ ^ n) hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)) ∈
          O.toricPts (ℓ ^ n) := by
        obtain ⟨χU, hχU⟩ := (hmem _).mp hUy
        obtain ⟨χU', hχU'⟩ := O.toricLift_dec (ℓ ^ n) hm φ hφD χU
        have h' : φ • O.toricPoint (ℓ ^ n) hm χU = O.toricPoint (ℓ ^ n) hm χU' := hχU'
        rw [← hχU, h']
        exact (hmem _).mpr ⟨χU', rfl⟩
      have hL3 := hcmp _ hφUy (A4Tor.smulPt O hφD (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) hs'
        (hw'.trans (congrArg (GluedPic0.nodeUnit O.ssFinset) (funext fun t => by
          show p • (wb ∘ σN) (σN.symm t) = p • wb t
          rw [Function.comp_apply, Equiv.apply_symm_apply])))
      exact ⟨hφy, hL2, hL3⟩

    obtain ⟨h1, h2, -⟩ := core k xt hxt
    refine ⟨h1, ?_⟩
    rw [h2, hχn k, ZMod.val_natCast]

    have hmk : 0 < ℓ ^ k := pow_pos (Fact.out : ℓ.Prime).pos k
    have hH1k := ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
      p M H hpM A hA Λ O (ℓ ^ k) hmk
    obtain ⟨hconvk, -, hmemk, -⟩ := hH1k
    obtain ⟨χk, rfl⟩ := (hmemk xt).mp hxt
    have htors : (ℓ ^ k) • O.toricPoint (ℓ ^ k) hmk χk = 0 := by
      have h1 : O.toricPoint (ℓ ^ k) hmk (1 : WithConv (muCoord ↥A O.toricRank (ℓ ^ k) →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
        have h := hconvk 1 1
        rw [mul_one] at h
        exact left_eq_add.mp h
      have key : ∀ j : ℕ, O.toricPoint (ℓ ^ k) hmk ((WithConv.toConv χk) ^ j).ofConv = j • O.toricPoint (ℓ ^ k) hmk χk := by
        intro j
        induction j with
        | zero => rw [pow_zero, h1, zero_nsmul]
        | succ j ih => rw [pow_succ, hconvk, ih, succ_nsmul]
      have hone : (WithConv.toConv χk) ^ (ℓ ^ k) = 1 := by
        apply WithConv.ofConv_injective
        refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
        intro g
        rw [ATPSkel.convPow_apply_single]
        show χk (AddMonoidAlgebra.single g 1) ^ (ℓ ^ k) = (1 : WithConv (muCoord ↥A O.toricRank (ℓ ^ k) →ₐ[↥A] AlgebraicClosure ℚ)).ofConv (AddMonoidAlgebra.single g 1)
        rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
        have hg : (ℓ ^ k) • g = 0 := by
          funext i
          show (ℓ ^ k) • g i = 0
          rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rw [hg]
        exact (map_one χk).trans (ATPSkel.convOne_apply_single g).symm
      rw [← key, hone, h1]
    rw [natCast_zsmul]
    have hz : (ℓ ^ k * (p / ℓ ^ k)) • O.toricPoint (ℓ ^ k) hmk χk = 0 := by
      rw [mul_nsmul, htors, smul_zero]
    symm
    calc (p % ℓ ^ k) • O.toricPoint (ℓ ^ k) hmk χk
        = (p % ℓ ^ k) • O.toricPoint (ℓ ^ k) hmk χk + (ℓ ^ k * (p / ℓ ^ k)) • O.toricPoint (ℓ ^ k) hmk χk := by rw [hz, add_zero]
      _ = (p % ℓ ^ k + ℓ ^ k * (p / ℓ ^ k)) • O.toricPoint (ℓ ^ k) hmk χk := (add_nsmul _ _ _).symm
      _ = p • O.toricPoint (ℓ ^ k) hmk χk := by rw [Nat.mod_add_div]

#print axioms solution

end S_ModularCurve_JHNeronObjectAtP_genOpH_U_smul_eq_cyclotomicCharacter_toZModPow_smul_of_mem_toricPts
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_genOpH_U_smul_eq_cyclotomicCharacter_toZModPow_smul_of_mem_toricPts (solution)
