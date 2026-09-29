-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/323cf1af-9e37-59ea-afe2-eaaeacdae8a4

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_isReduced_pullback_abqFibre_one_baseChange_one
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_isAlgClosed
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.SemilinearAut.crossGluingMap_apply AlgebraicCurve.GluedPic0.crossMap_mk AlgebraicCurve.SemilinearAut.coe_crossAdmissibleMap AlgebraicCurve.SemilinearAut.crossPerm_apply"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "ModularCurve.XHDRLevel~ΓN"
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve~H1 AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "genOpH genOpH_dia xHFunctionFieldBar JH qExpFunctionFieldC XHDRModelAtP ssPlacesQExp diamondActionModL infSubgroup mem_ssNodePairsQExp_iff qExpFrobeniusPlaceModL qExpFrobeniusPushforwardModL jqModC JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP JHNeronObjectAtP.isReduced_pullback_abqFibre_one_baseChange_one JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction JHNeronObjectAtP.ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero JHNeronObjectAtP.ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint diamondHBar_apply_eq_self_of_mem qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul qExpArithFrobC baseAut_qExpArithFrobC_apply coeff_qExpArithFrobC_smul image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "ΓN Fbar LevelData ptsSp abqFibre abqFibre_ptsSp ssFinset degeneracyHom_mul mk abqFibre_mul pts hecke g hecke_pts separated degPts G smooth locallyOfFiniteType mem_ssFinset_iff L isReduced_pullback_abqFibre_one_baseChange_one ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint"
namespace H1E104
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

theorem fst_comp_eq_of_points {κ : Type} [Field κ] [IsAlgClosed κ] {G Λ' : Scheme.{0}}
    (sG : G ⟶ Spec (CommRingCat.of κ)) (sΛ : Λ' ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType sG] [IsSeparated sG]
    (a : G ⟶ Λ') (ha : a ≫ sΛ = sG) (e : Spec (CommRingCat.of κ) ⟶ Λ') (he : e ≫ sΛ = 𝟙 _)
    [IsReduced (Limits.pullback a e)]
    (E₁ E₂ : G ⟶ G) (hE₁ : E₁ ≫ sG = sG) (hE₂ : E₂ ≫ sG = sG)
    (h : ∀ y : Spec (CommRingCat.of κ) ⟶ G, y ≫ sG = 𝟙 _ → y ≫ a = e → y ≫ E₁ = y ≫ E₂) :
    pullback.fst a e ≫ E₁ = pullback.fst a e ≫ E₂ := by
  haveI : LocallyOfFiniteType e := by
    have : LocallyOfFiniteType (e ≫ sΛ) := by rw [he]; infer_instance
    exact locallyOfFiniteType_of_comp e sΛ
  haveI : LocallyOfFiniteType (pullback.fst a e ≫ sG) := inferInstance
  have key := AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_isAlgClosed κ
    (gX := pullback.fst a e ≫ sG) (gY := sG)
    ⟨pullback.fst a e ≫ E₁, by rw [Category.assoc, hE₁]⟩ ⟨pullback.fst a e ≫ E₂, by rw [Category.assoc, hE₂]⟩
    (fun x => by
      have hx : x.1 ≫ pullback.fst a e ≫ sG = 𝟙 _ := x.2
      have hsnd : x.1 ≫ pullback.snd a e = 𝟙 _ := by
        calc x.1 ≫ pullback.snd a e = x.1 ≫ pullback.snd a e ≫ (e ≫ sΛ) := by rw [he, Category.comp_id]
          _ = x.1 ≫ (pullback.snd a e ≫ e) ≫ sΛ := by simp only [Category.assoc]
          _ = x.1 ≫ (pullback.fst a e ≫ a) ≫ sΛ := by rw [pullback.condition]
          _ = x.1 ≫ pullback.fst a e ≫ sG := by rw [Category.assoc, ha]
          _ = 𝟙 _ := hx
      have hya : (x.1 ≫ pullback.fst a e) ≫ a = e := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, Category.id_comp]
      have h' := h (x.1 ≫ pullback.fst a e) (by rw [Category.assoc]; exact hx) hya
      show x.1 ≫ pullback.fst a e ≫ E₁ = x.1 ≫ pullback.fst a e ≫ E₂
      simpa only [Category.assoc] using h')
  exact congrArg Subtype.val key

theorem nsmul_coe {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h := G.nsmul_natural f t x.1 x.2 n (RelativeGroupLaw.idPoint (f := f))
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

theorem comp_one_eq_one {R : Type} [CommRing R] {A B : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    {g : B ⟶ Spec (CommRingCat.of R)} (GA : RelativeGroupLaw R f) (GB : RelativeGroupLaw R g)
    (φ : SchemeHomOver f g) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (hmul : ∀ x y : SchemeHomOver t f, NeronModelInfra.schemeHomOverComp (GA.mul t x y) φ =
      GB.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    NeronModelInfra.schemeHomOverComp (GA.one t) φ = GB.one t := by
  have h : GB.mul t (NeronModelInfra.schemeHomOverComp (GA.one t) φ) (NeronModelInfra.schemeHomOverComp (GA.one t) φ) =
      NeronModelInfra.schemeHomOverComp (GA.one t) φ := by rw [← hmul, GA.one_mul]
  calc NeronModelInfra.schemeHomOverComp (GA.one t) φ
      = GB.mul t (GB.inv t (NeronModelInfra.schemeHomOverComp (GA.one t) φ))
          (GB.mul t (NeronModelInfra.schemeHomOverComp (GA.one t) φ) (NeronModelInfra.schemeHomOverComp (GA.one t) φ)) := by
        rw [← GB.mul_assoc, GB.inv_mul_cancel, GB.one_mul]
    _ = GB.mul t (GB.inv t (NeronModelInfra.schemeHomOverComp (GA.one t) φ)) (NeronModelInfra.schemeHomOverComp (GA.one t) φ) := by
        rw [h]
    _ = GB.one t := GB.inv_mul_cancel t _

theorem ringHom_baseRing_ext (p : ℕ) [hp : Fact p.Prime] {S : Type} [CommRing S]
    (f g : baseRing p →+* S) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hp.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)

theorem specMap_frobenius_comp_resPt_comp (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥Pl) p] (ρ : R p →+* ↥Pl) :
    Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥Pl) p)) ≫ resPt Pl ≫ Spec.map (CommRingCat.ofHom ρ) =
      resPt Pl ≫ Spec.map (CommRingCat.ofHom ρ) := by
  simp only [resPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (ringHom_baseRing_ext p _ _)

theorem hecke_dia_one (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl) (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (S : Set ℕ) : (O.hecke S (CohCarrier.Gen.dia 1)).1 = 𝟙 O.G := by
  haveI := O.smooth
  haveI := O.separated
  haveI : IsPrincipalIdealRing (baseRing p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsReduced O.G := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian O.g
  haveI : IsFractionRing (baseRing p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  refine AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated ℚ (AlgebraicClosure ℚ)
    O.g O.g _ _ (O.hecke S (CohCarrier.Gen.dia 1)).2 (Category.id_comp _) ?_
  intro x hx
  obtain ⟨j, hj⟩ : ∃ j : JH M H, (O.pts j).1 = x := ⟨O.pts.symm ⟨x, hx⟩, by rw [Equiv.apply_symm_apply]⟩
  rw [Category.comp_id, ← hj, ← O.hecke_pts S (CohCarrier.Gen.dia 1) j, ModularCurve.genOpH_dia,
    ModularCurve.diamondHBar_apply_eq_self_of_mem M H 1 H.one_mem j]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 24000000 in

theorem points_identity
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))
    (S : Set ℕ)

    [NeZero (M / p)]
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (_ : (Dw : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt Pl ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C),
      ∃ h : (inv (𝔛.efib Pl hPl ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)).base
            ((𝔛.efib Pl hPl ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) ≃ Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hΦpl : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥Pl) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl))),
      (D' : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpull1sp : ∀ (D : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁)

    (hp0 : (p : Γ((RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g), ⊤)) = 0)

    (hΦ : (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g) p 1 Fact.out hp0 ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA)) ≫ O.g =
      pullback.snd O.g (resPt Pl ≫ Λ.σA) ≫ (resPt Pl ≫ Λ.σA))
    (y : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g)
    (hy1 : y ≫ pullback.snd O.g (resPt Pl ≫ Λ.σA) = 𝟙 _)
    (hya : y ≫ (O.abqFibre 1).1 = ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1) :
    Spec.map (CommRingCat.ofHom (powCharRingHom (ResidueField ↥Pl) p 1 Fact.out (CharP.cast_eq_zero _ p))) ≫
        y ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA) ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 ≫
          (O.hecke S (CohCarrier.Gen.dia 1)).1 =
      y ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA) ≫ O.L.schemeNsmul p := by
  have hp : p.Prime := Fact.out
  have hpc : powCharRingHom (ResidueField ↥Pl) p 1 Fact.out (CharP.cast_eq_zero _ p) = frobenius (ResidueField ↥Pl) p :=
    RingHom.ext fun a => by rw [powCharRingHom_apply, pow_one]; exact (frobenius_def p a).symm
  rw [hpc, hecke_dia_one p M H hpM Pl hPl Λ O S, Category.comp_id]

  obtain ⟨yO, hyO⟩ : ∃ yO : SchemeHomOver (resPt Pl ≫ Λ.σA) O.g, yO.1 = y ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA) :=
    ⟨⟨y ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA), by rw [Category.assoc, pullback.condition, ← Category.assoc, hy1, Category.id_comp]⟩, rfl⟩
  have htoF : (toFibrePt yO).1 = y := by
    apply pullback.hom_ext
    · simp only [toFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst, hyO]
    · simp only [toFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]; exact hy1.symm

  obtain ⟨ξ, hξ⟩ : ∃ ξ, O.ptsSp ξ = yO := ⟨O.ptsSp.symm yO, O.ptsSp.apply_symm_apply yO⟩
  obtain ⟨hns, hzero, -⟩ :=
    ModularCurve.JHNeronObjectAtP.ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint p M H hpM Pl hPl Λ O

  have hunitO : toFibrePt (O.L.one (resPt Pl ≫ Λ.σA)) = (O.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _) := by
    show RelativeGroupLaw.baseChangePointOfBase _ (overId (O.L.one (resPt Pl ≫ Λ.σA))) =
      RelativeGroupLaw.baseChangePointOfBase _ (O.L.one (𝟙 _ ≫ (resPt Pl ≫ Λ.σA)))
    congr 1
  have hfib : fibreMap (O.abqFibre 1) (O.ptsSp ξ) = fibreMap (O.abqFibre 1) (O.ptsSp 0) := by
    rw [hξ, hzero]
    show ofFibrePt _ = ofFibrePt _
    congr 1
    rw [hunitO, comp_one_eq_one (O.L.baseChange (resPt Pl ≫ Λ.σA)) (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) (O.abqFibre 1) (𝟙 _) (O.abqFibre_mul 1 (𝟙 _))]
    exact Subtype.ext (by rw [NeronModelInfra.schemeHomOverComp_coe, htoF, hya])
  have hξ2 : (GluedPic0.toPic0Pair O.ssFinset ξ).2 = 0 := by
    have h1 := O.abqFibre_ptsSp ξ 1
    have h0 := O.abqFibre_ptsSp 0 1
    rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h1 h0
    rw [← h1, hfib, h0, map_zero, Prod.snd_zero]

  obtain ⟨hU, hrep⟩ :=
    ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero
      p M H hpM hj 𝔛 Pl hPl Λ O ρ hρ hσA hsp hspΛ hdia0 F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull
      hpull hpull_mul hpullsp Wbar wgen hWbar hwgen S hUPgen σ hσ Φ hΦpl hFdiv hpull1sp
  obtain ⟨x, hx21, hxΦ, hxξ⟩ := hrep ξ hξ2

  have hΦfrob : ∀ v, Φ v = (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • v := fun v => by
    rw [hΦpl v]; exact ModularCurve.qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul p _ _ v
  have hstab : SemilinearAut.IsNodeStable O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) := by
    intro s hs
    rw [O.mem_ssFinset_iff, ModularCurve.mem_ssNodePairsQExp_iff] at hs ⊢
    obtain ⟨hs2, hs1⟩ := hs
    refine ⟨?_, ?_⟩
    · show (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • s.2 ∈
        ModularCurve.ssPlacesQExp (ResidueField ↥Pl) (ΓN p M H hpM) p
      rw [← hΦfrob, hΦpl, ← ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥Pl) p (ΓN p M H hpM)]
      exact ⟨s.2, hs2, rfl⟩
    · show (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • s.1 =
        qExpFrobeniusPlaceModL (ResidueField ↥Pl) (ΓN p M H hpM) p ((ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • s.2)
      rw [← hΦfrob, ← hΦfrob, hΦpl, hΦpl, hs1]
  obtain ⟨τ, hτ⟩ : ∃ τ : SchemeHomOver (resPt Pl ≫ Λ.σA) (resPt Pl ≫ Λ.σA), τ.1 = Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥Pl) p)) :=
    ⟨⟨Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥Pl) p)), by
      rw [hσA]; exact specMap_frobenius_comp_resPt_comp p Pl ρ⟩, rfl⟩
  have hT2 := ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
    p M H hpM hpM2 hHp hj 𝔛 Pl hPl ρ hρ Λ O hσA hsp (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM))
    (fun z n => ModularCurve.coeff_qExpArithFrobC_smul p (ResidueField ↥Pl) _ z n) hstab (frobenius (ResidueField ↥Pl) p)
    (frobenius_def p) τ hτ yO
  have hT2' : O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 yO) =
      GluedPic0.mk O.ssFinset (SemilinearAut.admissibleMap O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) hstab x) := by
    rw [hT2, ← hξ, Equiv.symm_apply_apply, ← hxξ, GluedPic0.glueMap_mk]
  clear hT2

  have hxF1 : ((SemilinearAut.admissibleMap O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) hstab x : ↥(GluingData.admissible O.ssFinset)) :
      GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 = 0 := by
    rw [SemilinearAut.coe_admissibleMap]
    show (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 = 0
    rw [hx21, smul_zero]
  have hxFΦ : ∀ s ∈ O.ssFinset, ((SemilinearAut.admissibleMap O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) hstab x : ↥(GluingData.admissible O.ssFinset)) :
      GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 (Φ s.1) = 0 := by
    intro s hs
    rw [SemilinearAut.coe_admissibleMap]
    show ((ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1) (Φ s.1) = 0
    rw [hΦfrob, SemilinearAut.divisor_smul_apply_smul]
    exact (((GluingData.mem_admissible O.ssFinset).mp x.2).2.2 s hs).1
  have hσperm : ∀ t : ↥O.ssFinset, σ t = SemilinearAut.nodePerm O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) hstab t := by
    intro t
    have ht := (ModularCurve.mem_ssNodePairsQExp_iff _).mp ((O.mem_ssFinset_iff _).mp t.2)
    have hσt := (ModularCurve.mem_ssNodePairsQExp_iff _).mp ((O.mem_ssFinset_iff _).mp (σ t).2)
    apply Subtype.ext
    rw [SemilinearAut.nodePerm_apply]
    refine Prod.ext ?_ ?_
    · show (σ t).1.1 = (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • t.1.1
      rw [hσt.2, hσ t, ← hΦfrob, hΦpl, ht.2]
    · show (σ t).1.2 = (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • t.1.2
      rw [hσ t, ← hΦfrob, hΦpl, ht.2]
  have hbase : ∀ u : Additive (ResidueField ↥Pl)ˣ, SemilinearAut.baseAutUnitsHom (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) u = p • u := by
    intro u
    rw [SemilinearAut.baseAutUnitsHom_apply]
    have : Units.map ((SemilinearAut.baseAut (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) : (ResidueField ↥Pl) →+* (ResidueField ↥Pl)) : (ResidueField ↥Pl) →* (ResidueField ↥Pl)) u.toMul = u.toMul ^ p :=
      Units.ext (by simp [Units.val_pow_eq_pow_val, ModularCurve.baseAut_qExpArithFrobC_apply])
    rw [this, ofMul_pow]
    rfl
  have h1' : ((p • x : ↥(GluingData.admissible O.ssFinset)) : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
      (p : ℤ) • Finsupp.mapDomain Φ.symm ((SemilinearAut.admissibleMap O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) hstab x :
        ↥(GluingData.admissible O.ssFinset)) : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 := by
    rw [SemilinearAut.coe_admissibleMap, AddSubgroup.coe_nsmul, Prod.smul_fst, natCast_zsmul]
    congr 1
    show _ = Finsupp.mapDomain Φ.symm ((ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) • (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1)
    ext w
    rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, hΦfrob, SemilinearAut.divisor_smul_apply_smul]
  have h2' : ((p • x : ↥(GluingData.admissible O.ssFinset)) : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 = 0 := by
    rw [AddSubgroup.coe_nsmul, Prod.smul_snd, Prod.smul_fst, hx21, smul_zero]
  have h3' : ((p • x : ↥(GluingData.admissible O.ssFinset)) : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 =
      ((SemilinearAut.admissibleMap O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) hstab x : ↥(GluingData.admissible O.ssFinset)) :
        GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 ∘ σ := by
    rw [AddSubgroup.coe_nsmul, Prod.smul_snd, Prod.smul_snd, SemilinearAut.coe_admissibleMap]
    funext t
    show p • (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 t =
      SemilinearAut.baseAutUnitsHom (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM))
        ((x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 ((SemilinearAut.nodePerm O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) hstab).symm (σ t)))
    rw [hσperm t, Equiv.symm_apply_apply, hbase]
  have hUp := hU (SemilinearAut.admissibleMap O.ssFinset (ModularCurve.qExpArithFrobC p (ResidueField ↥Pl) (ΓN p M H hpM)) hstab x) (p • x) hxF1 hxFΦ h1' h2' h3'
  rw [map_nsmul, hxξ, ← hT2', Equiv.apply_symm_apply, Equiv.symm_apply_eq, hns, hξ] at hUp

  have hfinal := congrArg Subtype.val hUp
  rw [NeronModelInfra.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe, nsmul_coe, hτ, hyO] at hfinal
  simpa only [Category.assoc] using hfinal

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem main
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))
    (S : Set ℕ)

    [NeZero (M / p)]
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (_ : (Dw : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt Pl ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C),
      ∃ h : (inv (𝔛.efib Pl hPl ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)).base
            ((𝔛.efib Pl hPl ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) ≃ Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hΦpl : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥Pl) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl))),
      (D' : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpull1sp : ∀ (D : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁)

    (hp0 : (p : Γ((RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g), ⊤)) = 0)

    (hΦ : (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g) p 1 Fact.out hp0 ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA)) ≫ O.g =
      pullback.snd O.g (resPt Pl ≫ Λ.σA) ≫ (resPt Pl ≫ Λ.σA))
    :
    ∃ d₀ : (ZMod M)ˣ,
      (pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 :
          Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 ⟶ (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g)) ≫
        pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g) p 1 Fact.out hp0 ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA))
          (pullback.snd O.g (resPt Pl ≫ Λ.σA)) hΦ ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2).symm) (by rw [Category.comp_id, Category.id_comp])) ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.dia d₀)).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.dia d₀)).2).symm) (by rw [Category.comp_id, Category.id_comp])) =
      (pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 :
          Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 ⟶ (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g)) ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (⟨O.L.schemeNsmul p, O.L.schemeNsmul_over p⟩ : SchemeHomOver O.g O.g).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((⟨O.L.schemeNsmul p, O.L.schemeNsmul_over p⟩ : SchemeHomOver O.g O.g).2).symm) (by rw [Category.comp_id, Category.id_comp])) := by
  refine ⟨1, ?_⟩
  haveI := O.locallyOfFiniteType
  haveI := O.separated
  haveI : IsReduced (Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1) :=
    ModularCurve.JHNeronObjectAtP.isReduced_pullback_abqFibre_one_baseChange_one p M H hpM Pl hPl Λ O
  refine fst_comp_eq_of_points (κ := ResidueField ↥Pl) (pullback.snd O.g (resPt Pl ≫ Λ.σA)) (pullback.snd Λ.f (resPt Pl ≫ Λ.σA))
    (O.abqFibre 1).1 (O.abqFibre 1).2 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).2
    _ _ ?_ ?_ ?_
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  · simp only [pullback.lift_snd, Category.comp_id]
  · intro y hy1 hya
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      have hfr := Scheme.frobenius_comp y p 1 Fact.out
        (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero (ResidueField ↥Pl) p)) hp0
      rw [Scheme.frobenius_Spec] at hfr
      rw [← reassoc_of% hfr]
      exact points_identity p M H hpM hpM2 hHp Pl hPl hj 𝔛 Λ O hrep S ρ hρ hσA hsp hspΛ hdia0 F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull hpull hpull_mul hpullsp Wbar wgen hWbar hwgen hUPgen σ hσ Φ hΦpl hFdiv hpull1sp hp0 hΦ y hy1 hya
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]

end ModularCurve.JHNeronObjectAtP.H1E104

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul.ModularCurve _root_.ModularCurve.JHNeronObjectAtP _root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul.ModularCurve.JHNeronObjectAtP in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))
    (S : Set ℕ)

    [NeZero (M / p)]
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (_ : (Dw : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt Pl ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C),
      ∃ h : (inv (𝔛.efib Pl hPl ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)).base
            ((𝔛.efib Pl hPl ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) ≃ Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥Pl) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl))),
      (D' : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpull1sp : ∀ (D : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁)

    (hp0 : (p : Γ((RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g), ⊤)) = 0)

    (hΦ : (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g) p 1 Fact.out hp0 ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA)) ≫ O.g =
      pullback.snd O.g (resPt Pl ≫ Λ.σA) ≫ (resPt Pl ≫ Λ.σA)) :
    ∃ d₀ : (ZMod M)ˣ,
      (pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 :
          Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 ⟶ (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g)) ≫
        pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g) p 1 Fact.out hp0 ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA))
          (pullback.snd O.g (resPt Pl ≫ Λ.σA)) hΦ ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2).symm) (by rw [Category.comp_id, Category.id_comp])) ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.dia d₀)).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.dia d₀)).2).symm) (by rw [Category.comp_id, Category.id_comp])) =
      (pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 :
          Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 ⟶ (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g)) ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (⟨O.L.schemeNsmul p, O.L.schemeNsmul_over p⟩ : SchemeHomOver O.g O.g).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((⟨O.L.schemeNsmul p, O.L.schemeNsmul_over p⟩ : SchemeHomOver O.g O.g).2).symm) (by rw [Category.comp_id, Category.id_comp])) := by
  rename_i hΦpl
  exact ModularCurve.JHNeronObjectAtP.H1E104.main p M H hpM hpM2 hHp Pl hPl hj 𝔛 Λ O hrep S ρ hρ hσA hsp hspΛ hdia0 F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull hpull hpull_mul hpullsp Wbar wgen hWbar hwgen hUPgen σ hσ Φ hΦpl hFdiv hpull1sp hp0 hΦ

end S_ModularCurve_JHNeronObjectAtP_exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul (solution)
