-- Prove2me | solution 1 for ModularCurve.XOneP.exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f6c71ea4-c700-5608-bfaa-86a848e8b63d

import Mathlib
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

open scoped Pointwise

set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))

    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
    (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
    (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex) :

    let OI : Subring (AlgebraicClosure ℚ) := Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring
    ∃ (ρI : A →+* ↥OI) (hρI : OI.subtype.comp ρI = algebraMap A (AlgebraicClosure ℚ)),

      let toκ : ↥OI →+* IsLocalRing.ResidueField ↥Pl := (IsLocalRing.residue ↥Pl).comp (Subring.inclusion inf_le_left)

      let DOI := SchemeHomOver (Spec.map (CommRingCat.ofHom ρI)) D.toBase
      let Dκ := SchemeHomOver (Spec.map (CommRingCat.ofHom (toκ.comp ρI))) D.toBase

      let dom : Set (ModularCurve.JOne (M * p)) :=
        {x | ∃ z : DOI, (gpts x).1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1}

      (∀ x ∈ dom, ∀ σ ∈ I, σ • x = x) ∧

      (∀ z z' : DOI, Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z'.1 → z = z') ∧

      (0 ∈ dom ∧ ∀ x ∈ dom, ∀ y ∈ dom, x - y ∈ dom) ∧

      (letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom ρI))
       letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom (toκ.comp ρI)))
       ∀ n : ℕ, 0 < n → ¬ p ∣ n →
         (∀ z : DOI, z ^ n = 1 → Spec.map (CommRingCat.ofHom toκ) ≫ z.1 = (1 : Dκ).1 → z = 1) ∧
         (∀ w : Dκ, w ^ n = 1 → ∃ z : DOI, z ^ n = 1 ∧ w.1 = Spec.map (CommRingCat.ofHom toκ) ≫ z.1)) ∧

      (∀ φ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Pl.IsFrobeniusAt φ' p →
        (∀ σ, σ ∈ I ↔ φ' * σ * φ'⁻¹ ∈ I) → ∀ x ∈ dom, φ' • x ∈ dom) := by
  classical
  intro OI

  let Qb := AlgebraicClosure ℚ
  let tQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of A) := specMap A Qb
  let h := hrep.some
  let Glaw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) h
  have hGLc : Glaw.IsCommutative :=
    RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) h

  have hIL : ∀ σ ∈ I, ∀ l : L, σ (algebraMap L Qb l) = algebraMap L Qb l := by
    intro σ hσ l
    let S : Subalgebra ℚ L :=
      { carrier := {l | σ (algebraMap L Qb l) = algebraMap L Qb l}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [map_mul, map_mul, ha, hb]
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [map_add, map_add, ha, hb]
        algebraMap_mem' := fun q => by
          simp only [Set.mem_setOf_eq]
          rw [show algebraMap L Qb (algebraMap ℚ L q) = algebraMap ℚ Qb q from
            (RingHom.congr_fun (Subsingleton.elim ((algebraMap L Qb).comp (algebraMap ℚ L)) (algebraMap ℚ Qb)) q)]
          exact σ.commutes q }
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← ((IsCyclotomicExtension.iff_adjoin_eq_top {p} ℚ L).mp inferInstance).2, Algebra.adjoin_le_iff]
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      subst hn
      show σ (algebraMap L Qb b) = algebraMap L Qb b
      exact hIμ σ hσ _ (by rw [← map_pow, hb, map_one])
    have : l ∈ S := hS ▸ Algebra.mem_top
    exact this
  have hAOI : ∀ a : A, algebraMap A Qb a ∈ OI := by
    intro a
    refine ⟨?_, ?_⟩
    · show algebraMap A Qb a ∈ Pl.toSubring
      rw [← hρ]; exact (ρ a).2
    · show algebraMap A Qb a ∈ IntermediateField.fixedField I
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [IsScalarTower.algebraMap_apply A L Qb]
      exact hIL σ hσ _
  let ρI : A →+* ↥OI := (algebraMap A Qb).codRestrict OI hAOI
  have hρI : OI.subtype.comp ρI = algebraMap A Qb := RingHom.ext fun _ => rfl
  refine ⟨ρI, hρI, ?_⟩
  intro toκ DOI Dκ dom

  have hsubρ : Spec.map (CommRingCat.ofHom OI.subtype) ≫ Spec.map (CommRingCat.ofHom ρI) = tQ := by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap A Qb))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρI]

  letI grpQ : Group (SchemeHomOver tQ D.toBase) := Glaw.pointGroup tQ
  letI grpO : Group DOI := Glaw.pointGroup (Spec.map (CommRingCat.ofHom ρI))
  let bc : DOI → SchemeHomOver tQ D.toBase := fun z =>
    GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom OI.subtype)) hsubρ z
  have hbc : ∀ z : DOI, (bc z).1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1 := fun _ => rfl
  have hbcmul : ∀ z z' : DOI, bc (z * z') = bc z * bc z' :=
    fun z z' => Glaw.mul_natural _ _ _ hsubρ z z'
  have hdom : ∀ x, x ∈ dom ↔ ∃ z : DOI, gpts x = bc z := by
    intro x
    exact ⟨fun ⟨z, hz⟩ => ⟨z, Subtype.ext hz⟩, fun ⟨z, hz⟩ => ⟨z, congrArg Subtype.val hz⟩⟩

  have hgmul : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) = gpts x * gpts y := fun x y => hgadd x y
  have hg0 : gpts 0 = 1 := by
    have h00 := hgmul 0 0
    rw [add_zero] at h00
    have h2 : gpts 0 * gpts 0 = gpts 0 * 1 := by rw [mul_one]; exact h00.symm
    exact mul_left_cancel h2
  have hgneg : ∀ x : ModularCurve.JOne (M * p), gpts (-x) = (gpts x)⁻¹ := by
    intro x; symm; apply inv_eq_of_mul_eq_one_right; rw [← hgmul, add_neg_cancel, hg0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx σ hσ
    obtain ⟨z, hz⟩ := hx
    apply gpts.injective
    apply Subtype.ext
    have key := hτpts σ 1 (fun l => by rw [hIL σ hσ l]; rfl) x
    rw [inv_one, hτ1, Category.comp_id, hz, ← Category.assoc, ← Spec.map_comp] at key
    rw [key, hz]
    congr 2

    change CommRingCat.ofHom OI.subtype ≫ CommRingCat.ofHom (σ.toRingEquiv.toRingHom) = CommRingCat.ofHom OI.subtype
    rw [← CommRingCat.ofHom_comp]
    congr 1
    ext y
    have hy : (y : Qb) ∈ IntermediateField.fixedField I := y.2.2
    rw [IntermediateField.mem_fixedField_iff] at hy
    exact hy σ hσ
  ·
    intro z z' hzz'
    haveI : IsSeparated D.toBase := hsep
    haveI : IsDominant (Spec.map (CommRingCat.ofHom OI.subtype)) := by
      refine ⟨?_⟩
      rw [Spec.map_base]
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
        (by rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]; exact bot_le)
    exact Subtype.ext (ext_of_isDominant_of_isSeparated D.toBase (z.2.trans z'.2.symm)
      (Spec.map (CommRingCat.ofHom OI.subtype)) hzz')
  ·
    refine ⟨?_, ?_⟩
    ·
      refine ⟨⟨Spec.map (CommRingCat.ofHom ρI) ≫ D.zeroSection, by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id]⟩, ?_⟩
      rw [hg0]
      have hn := RelativeGroupLaw.one_natural Glaw (𝟙 _) tQ tQ (Category.comp_id _)
      have h1 : (Glaw.one (𝟙 _)).1 = D.zeroSection :=
        RepresentsRelSubPic.relativeGroupLaw_one (P := algEquivZeroGroupCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) h
      change (Glaw.one tQ).1 = _
      rw [← hn, GoodReductionJacobian.schemeHomOverComp_coe, h1, ← Category.assoc, hsubρ]
    · intro x hx y hy
      rw [hdom] at hx hy ⊢
      obtain ⟨z, hz⟩ := hx
      obtain ⟨z', hz'⟩ := hy
      refine ⟨z * z'⁻¹, ?_⟩
      have hbcinv : bc z'⁻¹ = (bc z')⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← hbcmul, inv_mul_cancel]

        have h11 := hbcmul 1 1
        rw [mul_one] at h11
        have h2 : bc 1 * bc 1 = bc 1 * 1 := by rw [mul_one]; exact h11.symm
        exact mul_left_cancel h2
      rw [sub_eq_add_neg, hgmul, hgneg, hz, hz', hbcmul, hbcinv]
  ·
    haveI : Smooth D.toBase := hsm
    haveI : HenselianLocalRing ↥OI :=
      ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn (K := ℚ) Pl I hI
    haveI : IsAlgClosed (IsLocalRing.ResidueField ↥Pl) := ValuationSubring.isAlgClosed_residueField Pl
    obtain ⟨hπ, hπu⟩ := ValuationSubring.surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn p Pl hPl I hI
    intro n hn0 hnp

    have hnu : IsUnit (n : A) := by
      by_contra hnu
      have hmem : (n : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp) : IsCoprime (p : ℤ) (n : ℤ))
      have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
        have huv' := congrArg (Int.castRingHom A) huv
        simp only [map_add, map_mul, map_natCast, map_one] at huv'
        rw [← huv']
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hAp) (Ideal.mul_mem_left _ _ hmem)
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    exact GoodReductionJacobian.RelativeGroupLaw.eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing
      Glaw hGLc n hnu (↥OI) ρI (IsLocalRing.ResidueField ↥Pl) toκ hπ hπu
  ·
    intro φ' hφ' hnorm x hx
    rw [hdom] at hx ⊢
    obtain ⟨z, hz⟩ := hx

    have hφPl : ∀ y : Qb, y ∈ Pl → φ' y ∈ Pl := by
      intro y hy
      have hst : φ' • Pl = Pl := MulAction.mem_stabilizer_iff.mp hφ'.mem_decompositionSubgroup
      have := ValuationSubring.smul_mem_pointwise_smul φ' y Pl hy
      rwa [hst] at this
    have hφfix : ∀ y : Qb, y ∈ IntermediateField.fixedField I → φ' y ∈ IntermediateField.fixedField I := by
      intro y hy
      rw [IntermediateField.mem_fixedField_iff] at hy ⊢
      intro σ hσ
      have hσ' : φ'⁻¹ * σ * φ' ∈ I := by
        rw [hnorm]
        have : φ' * (φ'⁻¹ * σ * φ') * φ'⁻¹ = σ := by group
        rw [this]; exact hσ
      have h := hy _ hσ'
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h
      have h2 := congrArg φ' h
      rwa [show φ' (φ'⁻¹ (σ (φ' y))) = σ (φ' y) from AlgEquiv.apply_symm_apply φ' _] at h2
    have hφOI : ∀ y : ↥OI, φ' (y : Qb) ∈ OI := fun y => ⟨hφPl y y.2.1, hφfix y y.2.2⟩
    let φO : ↥OI →+* ↥OI := (φ'.toRingEquiv.toRingHom.comp OI.subtype).codRestrict OI hφOI

    haveI : IsScalarTower ℚ L Qb := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p} ℚ L
    let s : L ≃ₐ[ℚ] L := φ'.restrictNormal L
    have hs : ∀ l : L, φ' (algebraMap L Qb l) = algebraMap L Qb (s l) := fun l => (AlgEquiv.restrictNormal_commutes φ' L l).symm

    have hsq : Spec.map (CommRingCat.ofHom φ'.toRingEquiv.toRingHom) ≫ Spec.map (CommRingCat.ofHom OI.subtype) =
        Spec.map (CommRingCat.ofHom OI.subtype) ≫ Spec.map (CommRingCat.ofHom φO) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    have key := hτpts φ' s hs x
    refine ⟨⟨Spec.map (CommRingCat.ofHom φO) ≫ z.1 ≫ (τ s⁻¹).1, ?_⟩, ?_⟩
    ·
      rw [Category.assoc, Category.assoc, (τ s⁻¹).2, ← Category.assoc z.1, z.2, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 1
      ext a
      show φ' (algebraMap A Qb (s⁻¹ • a)) = algebraMap A Qb a
      rw [IsScalarTower.algebraMap_apply A L Qb, hΓA, hs, IsScalarTower.algebraMap_apply A L Qb]
      congr 1
      exact AlgEquiv.apply_symm_apply s _
    · apply Subtype.ext
      rw [key, hz, hbc, hbc]
      simp only [Category.assoc]
      rw [← Category.assoc (Spec.map _), hsq, Category.assoc]

end S_ModularCurve_XOneP_exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul (solution)
