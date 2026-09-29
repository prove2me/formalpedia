-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_sections_multidegree_eq_depth_of_exists_schemeHomOver_of_branch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b5df2f42-8a32-51d0-90a8-75828494d2b6

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_X0MqResolvedTable

import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_mem_support_comp_inl_zero_of_not_mem_range
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_mem_support_comp_inl_one_of_not_mem_range
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_and_comp_eq_of_valuationSubring_comap
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_sections_multidegree_eq_depth_of_exists_schemeHomOver_of_branch
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X"
p2m_attr_erase "simp" "ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve ModularCurve.JZeroNeronObjectAtP"

open IsLocalRing ModularCurve.PlaceSpecialization

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace E5W2bTop

private theorem exists_comp_eq_of_isProper_of_isIso_morphismRestrict
    {O : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
    {Y X : Scheme.{0}} (π : Y ⟶ X) [IsProper π] (U : X.Opens) [IsIso (π ∣_ U)]
    (s : Spec (CommRingCat.of O) ⟶ X)
    (hs : Set.range (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ s).base ⊆ (U : Set X)) :
    ∃ t : Spec (CommRingCat.of O) ⟶ Y, t ≫ π = s := by
  set i : Spec (CommRingCat.of K) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ s with hi
  have hrange : Set.range i.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hs
  let k : Spec (CommRingCat.of K) ⟶ U := IsOpenImmersion.lift U.ι i hrange
  have hk : k ≫ U.ι = i := IsOpenImmersion.lift_fac U.ι i hrange
  let i₁ : Spec (CommRingCat.of K) ⟶ Y := k ≫ inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι
  have hsq : i₁ ≫ π = Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ s := by
    simp only [i₁, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hk]
  have hπ : IsProper π := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hπ
  have hex : ValuativeCriterion.Existence π := hπ.1.1.1.existence
  let S : ValuativeCommSq π := { R := O, K := K, i₁ := i₁, i₂ := s, commSq := ⟨hsq⟩ }
  obtain ⟨ls⟩ := (hex S).exists_lift
  exact ⟨ls.l, ls.fac_right⟩

private theorem exists_section_comp_toDR_eq (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (ρO : DRLevel.R p →+* O)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ) (hp : ((p : ℕ) : O) ≠ 0)
    (s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    ∃ t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y, t ≫ 𝔛reg.toDR = s ∧ t ≫ 𝔛reg.toBase = 𝟙 _ := by
  haveI := 𝔛reg.toDR_iso_generic
  obtain ⟨t, ht⟩ := exists_comp_eq_of_isProper_of_isIso_morphismRestrict (K := FractionRing O) 𝔛reg.toDR
    (pullback.snd (DRLevel.toBase N₀ p) _ ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) s
    (by
      rintro _ ⟨q, rfl⟩
      have hq' : ((p : ℕ) : O) ∉ ((Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))).base q).asIdeal := by
        have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
        change ((p : ℕ) : O) ∉ q.asIdeal.comap (algebraMap O (FractionRing O))
        rw [hq, Ideal.comap_bot_of_injective _ (IsFractionRing.injective O (FractionRing O))]
        simpa using hp
      have h2 : ((Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))) ≫ s) ≫
          pullback.snd (DRLevel.toBase N₀ p) _).base q ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O) := by
        rw [Category.assoc, hs, Category.comp_id]; exact hq'
      exact h2)
  exact ⟨t, ht, by rw [← 𝔛reg.toDR_over, ← Category.assoc, ht, hs]⟩

section Z

private theorem ringHom_ratSubring_ext (S : Subring ℚ) {K : Type} [CommRing K] [IsDomain K] [CharZero K] (f g : S →+* K) : f = g := by
  refine RingHom.ext fun x => ?_
  have hden : ((x : ℚ).den : ℚ) ∈ S := natCast_mem S _
  have hnum : ((x : ℚ).num : ℚ) ∈ S := intCast_mem S _
  have hx : x * ⟨_, hden⟩ = ⟨_, hnum⟩ := Subtype.ext (Rat.mul_den_eq_num (x : ℚ))
  have hd : ((x : ℚ).den : K) ≠ 0 := Nat.cast_ne_zero.2 (x : ℚ).den_nz
  have hden' : (⟨_, hden⟩ : S) = ((x : ℚ).den : S) := Subtype.ext (by simp)
  have hnum' : (⟨_, hnum⟩ : S) = ((x : ℚ).num : S) := Subtype.ext (by simp)
  have hf : f x * ((x : ℚ).den : K) = ((x : ℚ).num : K) := by
    have := congrArg f hx
    rwa [map_mul, hden', hnum', map_natCast, map_intCast] at this
  have hg : g x * ((x : ℚ).den : K) = ((x : ℚ).num : K) := by
    have := congrArg g hx
    rwa [map_mul, hden', hnum', map_natCast, map_intCast] at this
  exact mul_right_cancel₀ hd (hf.trans hg.symm)

private theorem spec_hom_ext_of_ratSubring (S : Subring ℚ) {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    (f g : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of ↥S)) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact ringHom_ratSubring_ext S _ _

variable (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime]

private theorem exists_z {A : ValuationSubring (AlgebraicClosure ℚ)}
    (D : RelativePic0Designation (DRLevel.R p) (DRLevel.toBase N₀ p))
    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_galois : ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ (pts x).1)
    (O : Type) [CommRing O] [IsDomain O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (ρO : DRLevel.R p →+* O)
    {ρ : DRLevel.R p →+* ↥A}
    (x : ↥(inertiaInvariants A (N₀ * p)))
    (hx : ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      (pts ((x : JZero (N₀ * p)))).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1) :
    ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase,
      Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ z.1 = (pts ((x : JZero (N₀ * p)))).1 := by
  set P := (pts (x : JZero (N₀ * p))).1 with hP

  have hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)).toRingEquiv.toRingHom) ≫ P = P := by
    intro σ hσ
    have h1 : σ • (x : JZero (N₀ * p)) = (x : JZero (N₀ * p)) := (mem_inertiaInvariants.mp x.2) σ hσ
    have h2 := hpts_galois σ (x : JZero (N₀ * p))
    rw [h1] at h2
    exact h2.symm

  obtain ⟨x', hx'⟩ := AlgebraicGeometry.Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq
    (A.inertiaSubgroupIn ℚ) P hfix

  obtain ⟨s, hs⟩ := hx
  obtain ⟨z', hz'x, -⟩ := AlgebraicGeometry.exists_comp_eq_and_comp_eq_of_valuationSubring_comap
    (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)) A x' s.1 (by rw [← hs, ← hx'])

  haveI : CharZero O := (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))).charZero
  refine ⟨⟨Spec.map (CommRingCat.ofHom eO.symm.toRingHom) ≫ z', spec_hom_ext_of_ratSubring _ _ _⟩, ?_⟩
  show Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ Spec.map (CommRingCat.ofHom eO.symm.toRingHom) ≫ z' = P
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hring : (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))).comp eO.symm.toRingHom =
      (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype := by
    ext a; simp
  rw [hring, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hz'x, hx']

end Z

private theorem sum_sub_eq_zero_of_degZero (M : ℕ) [NeZero M]
    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M))))
    {m : ℕ} (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)).support))
    (pos neg : Fin m → ℕ)
    (hmult : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
      (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M))) :
    (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0 := by
  have hdeg : Divisor.degree (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) = 0 := D₀.2
  have hdeg' : Divisor.degree (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) =
      ∑ w ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)).support, (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) w := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [AddMonoidHom.mulRight_apply, ModularCurve.deg_eq_one_modularFunctionFieldBar, Nat.cast_one, mul_one]
  calc (∑ j, ((pos j : ℤ) - (neg j : ℤ)))
        = ∑ j, (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)) :=
          Finset.sum_congr rfl fun j _ => hmult j
    _ = ∑ w : ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)).support),
          (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)) :=
          Fintype.sum_equiv idx _ _ fun j => rfl
    _ = ∑ w ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)).support, (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) w :=
          Finset.sum_coe_sort _ _
    _ = 0 := hdeg'.symm.trans hdeg

private theorem mem_and_forall_ne_not_mem {ι Y β : Type*} [Membership Y β] {S : ι → β} {y : Y} {c : ι}
    (H : ∀ v, y ∈ S v ↔ v = c) : y ∈ S c ∧ ∀ w, w ≠ c → y ∉ S w :=
  ⟨(H c).2 rfl, fun w hne hmem => hne ((H w).1 hmem)⟩

end E5W2bTop

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem solution

    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : DRLevel.R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R p) (AlgebraicClosure ℚ))

    (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    [IsProper (DRLevel.toBase N₀ p)]
    (D : RelativePic0Designation (DRLevel.R p) (DRLevel.toBase N₀ p))
    (hD : RepresentsRelSubPic (DRLevel.toBase N₀ p) 𝔓.εinf (algEquivZeroCut (DRLevel.toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (DRLevel.toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (DRLevel.toBase N₀ p) (genPt p) ⟶ pullback (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ) = pullback.fst (DRLevel.toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ) = pullback.snd (DRLevel.toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] [DecidableEq k] {red : ↥A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p}
    (P : PlaceSpecialization A p N₀ data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N₀)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p N₀ k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k N₀) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((p : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (cs : ∀ w ∈ W, R.NodeCoordinates K w)
    (hxy : ∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
        (cs w hw).x * (cs w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u)
    (hmax : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y})
    (hbr : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}).IsPrime ∧
        (cs w hw).y ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).x} ∧ (cs w hw).x ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) → ℕ)
    (hdepth : ∀ w (hw : w ∈ W), (cs w hw).DepthValueLaw depth)
    (hwidth : ∀ w ∈ W, e w = placeWidthChar p N₀ w)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (ρO : DRLevel.R p →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R p) (AlgebraicClosure ℚ))
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO k toκ)

    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k N₀)))

    (hnodePt : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) (hw : P.reduceFst V ∈ W),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V = V) →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) _ →
        s.base (IsLocalRing.closedPoint O) =
          (pullback.fst (𝔓.comp k (toκ.comp ρO) 0) (𝔓.comp k (toκ.comp ρO) 1) ≫ 𝔓.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv (σN ⟨P.reduceFst V, hw⟩)))

    (swap : Bool)
    (hswap : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔓.comp k (toκ.comp ρO) 1 else 𝔓.comp k (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔓.comp k (toκ.comp ρO) 0 else 𝔓.comp k (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔓.comp k (toκ.comp ρO) 0 else 𝔓.comp k (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔓.comp k (toκ.comp ρO) 1 else 𝔓.comp k (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base))

    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K₀]
    (c₁ : ∀ w ∈ W, R.NodeCoordinates K₀ w)
    (E₀ : ↥W → ℕ) (u₀ : ∀ w (hw : w ∈ W), ↥(R.nodeIntegersOver K₀ w)) (hu₀ : ∀ w hw, IsUnit (u₀ w hw))
    (hxy₁ : ∀ w (hw : w ∈ W), (c₁ w hw).x * (c₁ w hw).y =
      R.nodeConst K₀ w ((p : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ E₀ ⟨w, hw⟩ * u₀ w hw)
    (hdepth_eq : ∀ w (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))), P.reduceFst V = w →
      (cs w hw).xDepth V = (c₁ w hw).xDepth V ∧ (cs w hw).yDepth V = (c₁ w hw).yDepth V)
    (hchart : ∀ w (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))), P.reduceFst V = w →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V = V) →
      ∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ t ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) _ →
        ∀ d : ℕ, (c₁ w hw).yDepth V = A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ^ d →
          ∀ v : X0MqComponents 𝔛reg.width,
            t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp v).support ↔
              v = DRResolvedModelPackageLevel.chainPos 𝔛reg.width (σN ⟨w, hw⟩) (if swap then 𝔛reg.width (σN ⟨w, hw⟩) - d else d))

    (x : ↥(inertiaInvariants A (N₀ * p)))
    (hx : ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      (pts ((x : JZero (N₀ * p)))).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1)
    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
    (hD₀ : Pic0.mk D₀ = (x : JZero (N₀ * p)))
    (hadm : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V' = V') ∧
        (P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ P.reduceFst V' ∈ W)) :

    ∃ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase)
      (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
      (pos neg : Fin m → ℕ) (v : Fin m → X0MqComponents 𝔛reg.width)
      (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))).support)),

      Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ z.1 = (pts ((x : JZero (N₀ * p)))).1 ∧

      (∑ j, ((pos j : ℤ) - (neg j : ℤ)) = 0) ∧
      (∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
        (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p)))
          (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))) ∧

      (∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support) ∧

      Nonempty (
        (Scheme.Modules.pullback (pullback.fst 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))).obj
            ((Scheme.Modules.pullback 𝔛reg.toDR).obj (hD.poincare.pullbackAlong z).L) ≅
          (List.finRange m).foldr
            (fun j M => (sectionTwist 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))) (pos j) ⊗
                ((sectionIdeal 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))) ^ (neg j)).module) ⊗ M)
            (𝟙_ (pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))).Modules)) ∧

      (∀ j, v j =
        (if P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) then (if swap then Sum.inl 1 else Sum.inl 0)
         else if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) then (if swap then Sum.inl 0 else Sum.inl 1)
         else if hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) ∈ W then
           DRResolvedModelPackageLevel.chainPos 𝔛reg.width (σN ⟨_, hw⟩)
             (if swap then 𝔛reg.width (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
              else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))))
         else Sum.inl 0)) := by

  obtain ⟨z, hz⟩ := E5W2bTop.exists_z N₀ p D pts hpts_galois O eO ρO x hx

  let m : ℕ := (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))).support.card
  let idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))).support) := ((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))).support.equivFin).symm
  have hfix : ∀ (j : Fin m), ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N₀ * p)) τ • (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) = (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) :=
    fun j => (hadm _ (idx j).2).1

  have hpO : ((p : ℕ) : O) ≠ 0 := fun h =>
    IsDiscreteValuationRing.not_a_field O (by rw [hϖO]; exact Ideal.span_singleton_eq_bot.2 h)
  choose s hs using fun j : Fin m =>
    ModularCurve.DRModelPackageLevel.exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
      N₀ p hpN₀ 𝔓 O eO ρO hρO (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) (hfix j)
  choose t ht htb using fun j : Fin m =>
    E5W2bTop.exists_section_comp_toDR_eq N₀ p 𝔓 O ρO k toκ 𝔛reg hpO (s j) (hs j).1
  let σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase := fun j => ⟨t j, htb j⟩
  have hσ : ∀ j, Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ (σ j).1 ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) =
      ((𝔓.Meta.pointEquivPlace).symm (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) _ := by
    intro j
    show Spec.map _ ≫ t j ≫ 𝔛reg.toDR ≫ _ = _
    rw [reassoc_of% (ht j)]
    exact (hs j).2
  let pos : Fin m → ℕ := fun j => ((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))).toNat
  let neg : Fin m → ℕ := fun j => (-((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))))).toNat

  have hC3 : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) = (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) :=
    fun j => Int.toNat_sub_toNat_neg _
  have hC2 : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0 := E5W2bTop.sum_sub_eq_zero_of_degZero (N₀ * p) D₀ idx pos neg hC3

  have hs1 : ∀ j, ((σ j).1 ≫ 𝔛reg.toDR) ≫ pullback.snd (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ :=
    fun j => by rw [Category.assoc, 𝔛reg.toDR_over]; exact (σ j).2
  have hs2 : ∀ j, Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫
          ((σ j).1 ≫ 𝔛reg.toDR) ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) =
        ((𝔓.Meta.pointEquivPlace).symm (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) _ :=
    fun j => by rw [Category.assoc]; exact hσ j

  refine ⟨z, m, σ, pos, neg, _, idx, hz, hC2, hC3, ?hv, ?hgen, fun j => rfl⟩
  case hgen =>
    exact ModularCurve.DRModelPackageLevel.nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist
      N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQ kQ hkQ₁ ajbar hajbar εbar hεbar pts hpts_add hpts_aj
      O eO hϖO ρO toκ 𝔛reg x D₀ hD₀ z hz m idx pos neg hC3 hC2 σ hσ
  case hv =>
    intro j
    dsimp only
    by_cases h1 : P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
    ·
      rw [if_pos h1]
      obtain ⟨-, hout⟩ := (hswap (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) (hfix j) _ (hs1 j) (hs2 j)).1 h1
      cases swap
      · simp only [Bool.false_eq_true, ↓reduceIte] at hout ⊢
        exact
          ModularCurve.DRResolvedModelPackageLevel.mem_support_comp_inl_zero_of_not_mem_range
            N₀ p hpN₀ 𝔓 O ρO hϖO k toκ 𝔛reg (σ j).1 (σ j).2 hout
      · simp only [↓reduceIte] at hout ⊢
        exact
          ModularCurve.DRResolvedModelPackageLevel.mem_support_comp_inl_one_of_not_mem_range
            N₀ p hpN₀ 𝔓 O ρO hϖO k toκ 𝔛reg (σ j).1 (σ j).2 hout
    rw [if_neg h1]
    by_cases h2 : P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
    ·
      rw [if_pos h2]
      obtain ⟨-, hout⟩ := (hswap (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) (hfix j) _ (hs1 j) (hs2 j)).2 h2
      cases swap
      · simp only [Bool.false_eq_true, ↓reduceIte] at hout ⊢
        exact
          ModularCurve.DRResolvedModelPackageLevel.mem_support_comp_inl_one_of_not_mem_range
            N₀ p hpN₀ 𝔓 O ρO hϖO k toκ 𝔛reg (σ j).1 (σ j).2 hout
      · simp only [↓reduceIte] at hout ⊢
        exact
          ModularCurve.DRResolvedModelPackageLevel.mem_support_comp_inl_zero_of_not_mem_range
            N₀ p hpN₀ 𝔓 O ρO hϖO k toκ 𝔛reg (σ j).1 (σ j).2 hout
    ·
      rw [if_neg h2]
      have hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) ∈ W := ((hadm _ (idx j).2).2.resolve_left h1).resolve_left h2
      rw [dif_pos hw]
      have hyd : (cs _ hw).yDepth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) =
          A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ^ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) :=
        hdepth _ hw (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) rfl (hfix j)
      rw [(hdepth_eq _ hw (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) rfl).2] at hyd
      exact E5W2bTop.mem_and_forall_ne_not_mem
        (hchart _ hw (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) rfl (hfix j) (σ j).1 (σ j).2 (hσ j) (depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))) hyd)

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_exists_sections_multidegree_eq_depth_of_exists_schemeHomOver_of_branch
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_sections_multidegree_eq_depth_of_exists_schemeHomOver_of_branch (solution)
