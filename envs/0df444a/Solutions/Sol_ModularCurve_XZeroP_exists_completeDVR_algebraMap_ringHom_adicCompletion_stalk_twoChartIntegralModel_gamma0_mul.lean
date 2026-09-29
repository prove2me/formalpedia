-- Prove2me | solution 1 for ModularCurve.XZeroP.exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b95015e6-6860-5963-9fae-f6874ef6124c

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Theorems.Thm_ModularCurve_XZeroP_isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_gamma0_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Theorems.Thm_IsDiscreteValuationRing_exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete
import Theorems.Thm_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
import Theorems.Thm_PowerSeries_existsUnique_ringHom_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroP_exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

namespace B7Supply

theorem isAdicComplete_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (h : IsAdicComplete I S) : IsAdicComplete (I.map (algebraMap R S)) S := by
  have key : ∀ (n : ℕ) (x : S), x ∈ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S S) ↔ x ∈ (I ^ n • ⊤ : Submodule R S) := by
    intro n x
    rw [Ideal.smul_top_eq_map (I ^ n), Submodule.restrictScalars_mem, Ideal.map_pow, smul_eq_mul, Ideal.mul_top]
  haveI : IsHausdorff (I.map (algebraMap R S)) S := ⟨fun x hx => by
    refine IsHausdorff.haus h.toIsHausdorff x fun n => ?_
    rw [SModEq.zero, ← key]; exact (SModEq.zero).mp (hx n)⟩
  haveI : IsPrecomplete (I.map (algebraMap R S)) S := ⟨fun {f} hf => by
    have hf' : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R S)] := fun {m n} hmn => by
      rw [SModEq.sub_mem, ← key]; exact (SModEq.sub_mem).mp (hf hmn)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete hf'
    exact ⟨L, fun n => by rw [SModEq.sub_mem, key]; exact (SModEq.sub_mem).mp (hL n)⟩⟩
  exact IsAdicComplete.mk

theorem eq_zero_of_forall_mem_pow {S : Type*} [CommRing S] (J : Ideal S) [IsAdicComplete J S] (x : S)
    (hx : ∀ n : ℕ, x ∈ J ^ n) : x = 0 :=
  IsHausdorff.haus (inferInstance : IsAdicComplete J S).toIsHausdorff x fun n => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact hx n

theorem algebraMap_mem_of_mem_maximalIdeal {A B S : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing S] [IsLocalRing S]
    (y : Ideal B) [y.IsPrime] (e : S ≃+* Localization.AtPrime y) (s : S) (hs : s ∈ IsLocalRing.maximalIdeal S)
    (a : A) (h : e s = algebraMap A (Localization.AtPrime y) a) : algebraMap A B a ∈ y := by
  have h2 : e s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime y) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    exact fun hu => hs (by simpa using hu.map e.symm)
  rw [h, IsScalarTower.algebraMap_apply A B (Localization.AtPrime y),
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y) y] at h2
  exact h2

theorem residue_localization_surjective {B : Type*} [CommRing B] (y : Ideal B) [hy : y.IsMaximal] :
    Function.Surjective (fun b : B => IsLocalRing.residue (Localization.AtPrime y) (algebraMap B _ b)) := by
  intro x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective y.primeCompl x

  have hs : (s : B) ∉ y := s.2
  obtain ⟨t, ht⟩ : ∃ t : B, s * t - 1 ∈ y := by
    have := (Ideal.Quotient.maximal_ideal_iff_isField_quotient y).mp hy
    obtain ⟨u, hu⟩ := this.mul_inv_cancel (a := Ideal.Quotient.mk y s)
      (fun h0 => hs ((Ideal.Quotient.eq_zero_iff_mem).mp h0))
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨t, Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, map_mul, map_one, hu, sub_self])⟩
  refine ⟨b * t, ?_⟩
  set R := Localization.AtPrime y
  have htm : algebraMap B R (s * t - 1) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R y _).mpr ht
  have hsu : IsLocalRing.residue R (algebraMap B R s) * IsLocalRing.residue R (IsLocalization.mk' R 1 s) = 1 := by
    rw [← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self', map_one]
  have hst : IsLocalRing.residue R (algebraMap B R s) * IsLocalRing.residue R (algebraMap B R t) = 1 := by
    rw [← map_mul, ← map_mul, show (s : B) * t = (s * t - 1) + 1 by ring, map_add, map_one, map_add, map_one,
      (IsLocalRing.residue_eq_zero_iff _).mpr htm, zero_add]
  have hs0 : IsLocalRing.residue R (algebraMap B R s) ≠ 0 := fun h => by simp [h] at hsu
  have heq : IsLocalRing.residue R (IsLocalization.mk' R 1 s) = IsLocalRing.residue R (algebraMap B R t) :=
    mul_left_cancel₀ hs0 (hsu.trans hst.symm)
  show IsLocalRing.residue R (algebraMap B R (b * t)) = IsLocalRing.residue R (IsLocalization.mk' R b s)
  rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, map_mul, map_mul, heq]

end B7Supply

open B7Supply

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (z₂ : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂))
    (ϖz₂ : (AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)
    (hϖz₂ : ϖz₂ = (((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ z₂ trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))))
    (hz₂ : ϖz₂ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂))
    (y₂ : ↥(XFin A (↥K₂) j₂)) (hy₂ : (ιFin A (↥K₂) j₂).base y₂ = z₂)
    (hss₂ : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₂) j₂) →+* Ω),
      RingHom.ker φ = y₂.asIdeal → φ (jChartFin A (↥K₂) j₂) ∈ ModularCurve.ssJSet p Ω)

    (𝔶₂ : Ideal ↥(chartAlgFin A (↥K₂) j₂)) (h𝔶₂ : 𝔶₂ = y₂.asIdeal) :
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsDiscreteValuationRing W₂)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₂) W₂) (τ₂ : A →+* W₂)
      (_ : IsLocalRing.maximalIdeal W₂ = Ideal.span {τ₂ ϖ})
      (σ₂ : W₂ →+* (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂))),
      (∀ a : A, σ₂ (τ₂ a) =
        algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ z₂ trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) ∧
      ∀ f : ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂), ∃ o : W₂,
        algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) f - σ₂ o ∈
          Ideal.map (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)))
            (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) := by
  classical
  subst h𝔶₂
  subst hy₂
  have hp : p.Prime := Fact.out
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩

  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (M * p) := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  haveI hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma0 (M * p)) hT L K₂ hK₂ j₂ hj₂
  have htj : Transcendental A j₂ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₂ A j₂ hj₂
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ := Algebra.IsSeparable.of_integral _ _
  obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K₂) j₂ htj hFD hsep
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K₂) j₂) := Algebra.FiniteType.isNoetherianRing A _
  haveI hyprime : y₂.asIdeal.IsPrime := y₂.isPrime

  have hmF : Spec.map (CommRingCat.ofHom (AlgHom.id A ↥(chartAlgFin A (↥K₂) j₂)).toRingHom) ≫ ιFin A (↥K₂) j₂ =
      ιFin A (↥K₂) j₂ ≫ 𝟙 _ := by
    rw [Category.comp_id]
    have : Spec.map (CommRingCat.ofHom (AlgHom.id A ↥(chartAlgFin A (↥K₂) j₂)).toRingHom) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _
      rw [CommRingCat.ofHom_id]; exact Spec.map_id _
    rw [this, Category.id_comp]
  obtain ⟨eX, -, heX, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom A (↥K₂) j₂ (↥K₂) j₂
      (AlgHom.id A _) (𝟙 _) hmF y₂
  let eXr : ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) ≃+* Localization.AtPrime y₂.asIdeal :=
    eX.commRingCatIsoToRingEquiv
  have heXr : ∀ a : A, eXr (((((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂)).presheaf.germ ⊤ ((ιFin A (↥K₂) j₂).base y₂) trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
      algebraMap A (Localization.AtPrime y₂.asIdeal) a := heX
  haveI : IsNoetherianRing (Localization.AtPrime y₂.asIdeal) :=
    IsLocalization.isNoetherianRing y₂.asIdeal.primeCompl _ inferInstance
  haveI hNoeth : IsNoetherianRing ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) :=
    isNoetherianRing_of_ringEquiv _ eXr.symm

  have hyϖ : algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ ∈ y₂.asIdeal :=
    algebraMap_mem_of_mem_maximalIdeal y₂.asIdeal eXr ϖz₂ hz₂ ϖ (by rw [hϖz₂]; exact heXr ϖ)

  obtain ⟨hmax, hfin⟩ :=
    ModularCurve.XZeroP.isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_gamma0_mul
      p M hM hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ y₂ hyϖ hss₂
  haveI := hmax
  have hresfin : Finite (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) := by
    haveI : Finite (↥(chartAlgFin A (↥K₂) j₂) ⧸ y₂.asIdeal) := hfin

    let q : ↥(chartAlgFin A (↥K₂) j₂) ⧸ y₂.asIdeal →+* IsLocalRing.ResidueField (Localization.AtPrime y₂.asIdeal) :=
      Ideal.Quotient.lift y₂.asIdeal ((IsLocalRing.residue _).comp (algebraMap _ _)) (fun b hb => by
        rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y₂.asIdeal) y₂.asIdeal b).mpr hb)
    have hq : Function.Surjective q := by
      intro x
      obtain ⟨b, hb⟩ := residue_localization_surjective y₂.asIdeal x
      exact ⟨Ideal.Quotient.mk _ b, hb⟩
    haveI : Finite (IsLocalRing.ResidueField (Localization.AtPrime y₂.asIdeal)) := Finite.of_surjective q hq
    exact Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv eXr).symm.toEquiv

  let θ : A →+* ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) :=
    (((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂)).presheaf.germ ⊤ ((ιFin A (↥K₂) j₂).base y₂) trivial).hom.comp
      ((((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  have hθ : ∀ a : A, θ a = ((((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂)).presheaf.germ ⊤ ((ιFin A (↥K₂) j₂).base y₂) trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) :=
    fun a => rfl
  have hϖθ : θ ϖ = ϖz₂ := by rw [hθ, hϖz₂]
  have hϖmax : θ ϖ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) := by rw [hϖθ]; exact hz₂
  let Oh := AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))
  have hfg : (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))).FG := IsNoetherian.noetherian _
  have hcO : IsAdicComplete (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) Oh := AdicCompletion.isAdicComplete hfg
  let J : Ideal Oh := (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))).map (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh)
  haveI hcJ : IsAdicComplete J Oh := isAdicComplete_map (S := Oh) (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) hcO

  let ρ : Oh →ₐ[((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))] ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) ⧸ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) := AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)))
  have hρalg : ∀ o : ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)), ρ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh o) = Ideal.Quotient.mk _ o := fun o => by
    rw [AlgHom.commutes]; rfl
  have hkerρ : ∀ x : Oh, ρ x = 0 → x ∈ J := by
    intro x hx
    have h1 : AdicCompletion.eval (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) 1 x = 0 := by
      have := AdicCompletion.factorₐ_evalₐ_one (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) x
      rw [hx] at this

      have hinj : Function.Injective (Ideal.Quotient.factor (show IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) ^ 1 ≤ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) by simp)) := by
        rw [injective_iff_map_eq_zero]
        intro a ha
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
        rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact ha
      have h2 : AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) 1 x = 0 := hinj (by rw [this, map_zero])
      have h3 := AdicCompletion.factor_evalₐ_eq_eval (I := IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) (n := 1) x
        (by rw [smul_eq_mul, Ideal.mul_top])
      rw [h2, map_zero] at h3
      exact h3.symm
    have h4 : x ∈ ((IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) ^ 1 • ⊤ : Submodule ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg]; exact h1
    rw [pow_one, Ideal.smul_top_eq_map] at h4
    exact h4

  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  obtain ⟨iD, iV, iC, hπ⟩ := PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hirr
  let W₀ : Type := PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A) - PowerSeries.C ϖ}
  letI : IsDomain W₀ := iD
  letI : IsDiscreteValuationRing W₀ := iV
  letI : IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀ := iC
  have hmaxW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {Ideal.Quotient.mk _ (PowerSeries.C ϖ)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
  let θh : A →+* Oh := (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh).comp θ
  let x : Oh := algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh (θ ϖ)
  have hxJ : x ∈ J := Ideal.mem_map_of_mem _ hϖmax
  obtain ⟨φ, hφ, -⟩ := PowerSeries.existsUnique_ringHom_of_isAdicComplete J θh x hxJ
  have hφC : ∀ o : A, φ (PowerSeries.C o) = θh o := by
    intro o
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_mem_pow J
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    · have h := hφ (PowerSeries.C o) n
      have hsum : (Finset.range n).sum (fun i => θh (PowerSeries.coeff i (PowerSeries.C o)) * x ^ i) = θh o := by
        rw [Finset.sum_eq_single 0]
        · rw [PowerSeries.coeff_zero_C, pow_zero, mul_one]
        · intro i _ hi; rw [PowerSeries.coeff_C, if_neg hi, map_zero, zero_mul]
        · intro h0; exact absurd (Finset.mem_range.mpr hn) h0
      rwa [hsum] at h
  have hφX : φ PowerSeries.X = x := by
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_mem_pow J
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      · have h := hφ PowerSeries.X 1
        rw [Finset.sum_range_one, PowerSeries.coeff_zero_X, map_zero, zero_mul, sub_zero, pow_one] at h
        rw [pow_one]
        exact J.sub_mem h hxJ
    · have h := hφ PowerSeries.X n
      have hsum : (Finset.range n).sum (fun i => θh (PowerSeries.coeff i PowerSeries.X) * x ^ i) = x := by
        rw [Finset.sum_eq_single 1]
        · rw [PowerSeries.coeff_one_X, map_one, one_mul, pow_one]
        · intro i _ hi; rw [PowerSeries.coeff_X, if_neg hi, map_zero, zero_mul]
        · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1
      rwa [hsum] at h
  have hxθ : θh ϖ = x := rfl
  have hkill : ∀ a ∈ Ideal.span {(PowerSeries.X : PowerSeries A) - PowerSeries.C ϖ}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_sub, hφX, hφC, hxθ, sub_self, mul_zero]
  let ψ₀ : W₀ →+* Oh := Ideal.Quotient.lift _ φ hkill
  have hψ₀C : ∀ a : A, ψ₀ (Ideal.Quotient.mk _ (PowerSeries.C a)) = θh a := fun a => by
    show Ideal.Quotient.lift _ φ hkill (Ideal.Quotient.mk _ (PowerSeries.C a)) = _
    rw [Ideal.Quotient.lift_mk, hφC]
  letI algW₀ : Algebra W₀ Oh := ψ₀.toAlgebra

  haveI : Finite (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) := hresfin
  let r₀ : W₀ →+* (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) := ρ.toRingHom.comp ψ₀
  have hr₀ : ∀ w ∈ IsLocalRing.maximalIdeal W₀, r₀ w = 0 := by
    intro w hw
    rw [hmaxW₀, Ideal.mem_span_singleton'] at hw
    obtain ⟨c, rfl⟩ := hw
    show ρ (ψ₀ (c * Ideal.Quotient.mk _ (PowerSeries.C ϖ))) = 0
    rw [map_mul, map_mul, hψ₀C, show θh ϖ = algebraMap _ _ (θ ϖ) from rfl, hρalg, Ideal.Quotient.eq_zero_iff_mem.mpr hϖmax, mul_zero]
  let rk : IsLocalRing.ResidueField W₀ →+* (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) := Ideal.Quotient.lift _ r₀ hr₀
  letI algk : Algebra (IsLocalRing.ResidueField W₀) (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) := rk.toAlgebra
  have hrk : ∀ w : W₀, algebraMap (IsLocalRing.ResidueField W₀) (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) (IsLocalRing.residue W₀ w) = ρ (ψ₀ w) := fun w => rfl
  haveI : Finite (IsLocalRing.ResidueField W₀) := Finite.of_injective _ rk.injective
  haveI : PerfectField (IsLocalRing.ResidueField W₀) := PerfectField.ofFinite
  haveI : Module.Finite (IsLocalRing.ResidueField W₀) (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField W₀) (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂))) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨W, iWR, iWD, iWV, iWC, iWA, iWfin, iWfree, iWflat, iWfaith, iWet, ι, hmapmax, hιres, -, -, -⟩ :=
    IsDiscreteValuationRing.exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete W₀ (IsLocalRing.ResidueField ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)))
  letI := iWR; letI := iWA; letI := iWet
  haveI : Algebra.FormallySmooth W₀ W := inferInstance

  have hleJ : IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) ≤ J.comap (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh) := fun o ho => Ideal.mem_map_of_mem _ ho
  let f₀ : W →+* Oh ⧸ J :=
    (Ideal.quotientMap J (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh) hleJ).comp (ι.toRingHom.comp (IsLocalRing.residue W))
  have hρJ : ∀ z : Oh, Ideal.quotientMap J (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh) hleJ (ρ z) = Ideal.Quotient.mk J z := by
    intro z
    obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (ρ z)
    have hdiff : z - algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh o ∈ J := hkerρ _ (by rw [map_sub, hρalg, ho, sub_self])
    rw [← ho]
    show Ideal.quotientMap J (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh) hleJ (Ideal.Quotient.mk _ o) = _
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq]
    exact hdiff
  have hf₀alg : ∀ w₀ : W₀, f₀ (algebraMap W₀ W w₀) = algebraMap W₀ (Oh ⧸ J) w₀ := by
    intro w₀
    show Ideal.quotientMap J (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) Oh) hleJ (ι (IsLocalRing.residue W (algebraMap W₀ W w₀))) = Ideal.Quotient.mk J (ψ₀ w₀)
    rw [hιres, hrk, hρJ]
  let f : W →ₐ[W₀] Oh ⧸ J := { f₀ with commutes' := hf₀alg }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := J) f

  let τ₂ : A →+* W := (algebraMap W₀ W).comp ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))
  refine ⟨W, iWR, iWD, iWV, iWC, τ₂, ?_, g.toRingHom, ?_, ?_⟩
  ·
    rw [← hmapmax, hmaxW₀, Ideal.map_span, Set.image_singleton]
    rfl
  ·
    intro a
    show g (algebraMap W₀ W (Ideal.Quotient.mk _ (PowerSeries.C a))) = _
    rw [g.commutes]
    show ψ₀ (Ideal.Quotient.mk _ (PowerSeries.C a)) = _
    rw [hψ₀C]
    rfl
  ·
    intro fO
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (R := W) (ι.symm (IsLocalRing.residue ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((ιFin A (↥K₂) j₂).base y₂)) fO))
    refine ⟨o, ?_⟩
    have h1 : Ideal.Quotient.mk J (g o) = f₀ o := by
      have := congrArg (fun h : W →ₐ[W₀] Oh ⧸ J => h o) hg
      first | exact this | simpa using this | simpa +zetaDelta using this
    have h2 : f₀ o = Ideal.Quotient.mk J (algebraMap _ Oh fO) := by
      show Ideal.quotientMap J (algebraMap _ Oh) hleJ (ι (IsLocalRing.residue W o)) = _
      rw [ho, RingEquiv.apply_symm_apply]
      exact Ideal.quotientMap_mk (f := algebraMap _ Oh) (H := hleJ) (x := fO)
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, eq_comm]
    exact h1.trans h2

end S_ModularCurve_XZeroP_exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_XZeroP_exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul (solution)
