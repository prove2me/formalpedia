-- Prove2me | solution 1 for ModularCurve.FullLevel.isRegularLocalRing_fibre_of_not_isMaximal_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/439e907f-779d-5e10-9413-40edd5e414c4

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_not_isMaximal_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace GenRed

theorem ringKrullDim_le_of_isIntegral_ringHom
    {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)

theorem ringKrullDim_chartAlg_singleton_le
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (s : F) :
    ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) ≤ ringKrullDim (Polynomial R) := by
  let ψ : Polynomial R →ₐ[R] ↥(Algebra.adjoin R ({s} : Set F)) :=
    (Polynomial.aeval s).codRestrict (Algebra.adjoin R ({s} : Set F))
      (fun P => by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨P, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, Subtype.ext rfl⟩
  let ι : ↥(Algebra.adjoin R ({s} : Set F)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) :=
    (Subalgebra.inclusion (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg R F {s})).toRingHom
  have hι : ι.IsIntegral := by
    intro x
    obtain ⟨P, hPm, hP⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff R F).mp x.2
    refine ⟨P, hPm, ?_⟩
    apply Subtype.ext
    have h1 := Polynomial.hom_eval₂ P ι ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom) x
    have h2 : ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom).comp ι =
        algebraMap ↥(Algebra.adjoin R ({s} : Set F)) F := rfl
    rw [h2] at h1
    exact h1.trans hP
  calc ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s})
      ≤ ringKrullDim ↥(Algebra.adjoin R ({s} : Set F)) := ringKrullDim_le_of_isIntegral_ringHom ι hι
    _ ≤ ringKrullDim (Polynomial R) :=
        ringKrullDim_le_of_isIntegral_ringHom ψ.toRingHom (RingHom.isIntegral_of_surjective _ hψ)

theorem eq_of_height_eq_one_of_le_of_not_isMaximal
    {B : Type} [CommRing B] (hdim : ringKrullDim B ≤ 2)
    (P y : Ideal B) [P.IsPrime] [y.IsPrime] (hP : P.height = 1) (hle : P ≤ y) (hy : ¬ y.IsMaximal) :
    y = P := by
  haveI : FiniteRingKrullDim B := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    constructor
    · intro h
      have := Ideal.height_le_ringKrullDim_of_isPrime (I := P)
      rw [h, hP] at this
      exact absurd this (by simp)
    · intro h
      rw [h, top_le_iff] at hdim
      exact absurd hdim (by decide)
  by_contra hne
  have hlt : P < y := lt_of_le_of_ne hle (Ne.symm hne)
  have h1 : P.height < y.height := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  obtain ⟨m, hm, hym⟩ := Ideal.exists_le_maximal y (Ideal.IsPrime.ne_top inferInstance)
  have hym' : y < m := lt_of_le_of_ne hym (fun h => hy (h ▸ hm))
  haveI := hm.isPrime
  have h2 : y.height < m.height := Ideal.height_strict_mono_of_isPrime_of_isPrime hym'
  have h3 : (m.height : WithBot ℕ∞) ≤ ringKrullDim B := Ideal.height_le_ringKrullDim_of_isPrime
  have hmfin : m.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have hyfin : y.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime

  rw [hP] at h1
  have h3' : m.height ≤ 2 := by
    have := h3.trans hdim
    rw [← WithBot.coe_ofNat, WithBot.coe_le_coe] at this
    exact this
  lift m.height to ℕ using hmfin with mh hmh
  lift y.height to ℕ using hyfin with yh hyh
  norm_cast at h1 h2 h3'
  omega

theorem exists_eq_C_mul_of_map_residue_eq_zero
    {A : Type} [CommRing A] [IsLocalRing A] (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (x : PowerSeries A) (hx : x.map (IsLocalRing.residue A) = 0) :
    ∃ x' : PowerSeries A, x = PowerSeries.C ϖ * x' := by
  classical
  have hc : ∀ n, ∃ c, PowerSeries.coeff n x = ϖ * c := by
    intro n
    have h0 : IsLocalRing.residue A (PowerSeries.coeff n x) = 0 := by
      have := congrArg (PowerSeries.coeff n) hx
      rwa [PowerSeries.coeff_map, map_zero] at this
    have hm : PowerSeries.coeff n x ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.residue_eq_zero_iff _).mp h0
    rw [hϖ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hcc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hcc]

end GenRed

namespace GenRed

theorem exists_eq_algebraMap_mul_of_mem_nonunits
    {L : Type} [Field L] {K : IntermediateField L (LaurentSeries L)}
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (hϖ0 : algebraMap A L ϖ ≠ 0)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hWnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (f : ↥K) (hf : f ∈ W₀.nonunits) :
    ∃ g : ↥K, g ∈ W₀ ∧ f = algebraMap A ↥K ϖ * g := by
  have hfW : f ∈ W₀ := W₀.nonunits_subset hf
  obtain ⟨x, yy, hyy, heq⟩ := (hW₀ f).mp hfW
  have hx0 : x.map (IsLocalRing.residue A) = 0 := (hWnu f x yy hyy heq).mp hf
  obtain ⟨x', rfl⟩ := exists_eq_C_mul_of_map_residue_eq_zero ϖ hϖ x hx0
  have hϖK : ((algebraMap A ↥K ϖ : ↥K) : LaurentSeries L) = HahnSeries.C (algebraMap A L ϖ) := by
    rw [IsScalarTower.algebraMap_apply A L ↥K]
    change algebraMap L (LaurentSeries L) (algebraMap A L ϖ) = _
    change HahnSeries.ofPowerSeries ℤ L (PowerSeries.C (algebraMap A L ϖ)) = _
    exact HahnSeries.ofPowerSeries_C _
  have hϖK0 : (algebraMap A ↥K ϖ : ↥K) ≠ 0 := by
    intro h
    apply hϖ0
    have := congrArg (fun t : ↥K => (t : LaurentSeries L)) h
    simp only [hϖK, ZeroMemClass.coe_zero] at this
    rw [← HahnSeries.C_zero] at this
    exact HahnSeries.C_injective this
  have heq' : (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (yy.map (algebraMap A L)) =
      HahnSeries.C (algebraMap A L ϖ) * HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) := by
    rw [heq, map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C]
  refine ⟨f / algebraMap A ↥K ϖ, ?_, ?_⟩
  · rw [hW₀]
    refine ⟨x', yy, hyy, ?_⟩
    have hC0 : (HahnSeries.C (algebraMap A L ϖ) : LaurentSeries L) ≠ 0 := HahnSeries.C_ne_zero hϖ0
    have hcoe : (((f / algebraMap A ↥K ϖ) : ↥K) : LaurentSeries L) =
        (f : LaurentSeries L) * (HahnSeries.C (algebraMap A L ϖ))⁻¹ := by
      rw [div_eq_mul_inv]
      push_cast
      rw [hϖK]
    rw [hcoe]
    calc (f : LaurentSeries L) * (HahnSeries.C (algebraMap A L ϖ))⁻¹ *
          HahnSeries.ofPowerSeries ℤ L (yy.map (algebraMap A L))
        = (HahnSeries.C (algebraMap A L ϖ))⁻¹ *
          ((f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (yy.map (algebraMap A L))) := by ring
      _ = (HahnSeries.C (algebraMap A L ϖ))⁻¹ *
          (HahnSeries.C (algebraMap A L ϖ) * HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L))) := by rw [heq']
      _ = HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
  · symm
    rw [mul_comm]
    exact div_mul_cancel₀ f hϖK0

end GenRed

namespace GenRed

theorem exists_mul_eq_of_mem_centre
    {L : Type} [Field L] {K : IntermediateField L (LaurentSeries L)}
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (hϖ0 : algebraMap A L ϖ ≠ 0)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hWnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (B : Subalgebra A ↥K) (P : Ideal ↥B)
    (hPmem : ∀ b : ↥B, b ∈ P ↔ (b : ↥K) ∈ W₀.nonunits)
    (hPloc : ∀ f : ↥K, f ∈ W₀ ↔ ∃ a b : ↥B, b ∉ P ∧ f * (b : ↥K) = (a : ↥K))
    (b : ↥B) (hb : b ∈ P) :
    ∃ a s : ↥B, s ∉ P ∧ b * s = algebraMap A ↥B ϖ * a := by
  obtain ⟨g, hgW, hbg⟩ := exists_eq_algebraMap_mul_of_mem_nonunits ϖ hϖ hϖ0 W₀ hW₀ hWnu (b : ↥K) ((hPmem b).mp hb)
  obtain ⟨a, s, hs, hgs⟩ := (hPloc g).mp hgW
  refine ⟨a, s, hs, Subtype.ext ?_⟩
  show (b : ↥K) * (s : ↥K) = ((algebraMap A ↥B ϖ : ↥B) : ↥K) * (a : ↥K)
  rw [hbg, mul_assoc, hgs]
  rfl

theorem isRegularLocalRing_quotient_localization_of_forall_exists
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (ϖ : A)
    (hϖP : algebraMap A B ϖ ∈ P)
    (hdiv : ∀ b ∈ P, ∃ a s : B, s ∉ P ∧ b * s = algebraMap A B ϖ * a) :
    IsRegularLocalRing (Localization.AtPrime P ⧸
      Ideal.span {algebraMap B (Localization.AtPrime P) (algebraMap A B ϖ)}) := by
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap B (Localization.AtPrime P) (algebraMap A B ϖ)} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      obtain ⟨a, s, hs, hbs⟩ := hdiv b hb
      refine ⟨IsLocalization.mk' (Localization.AtPrime P) a (⟨s, hs⟩ : P.primeCompl), ?_⟩
      have hu : IsUnit (algebraMap B (Localization.AtPrime P) s) :=
        IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl)
      apply hu.mul_left_injective
      show algebraMap _ _ b * algebraMap _ _ s =
        algebraMap _ _ (algebraMap A B ϖ) * IsLocalization.mk' (Localization.AtPrime P) a (⟨s, hs⟩ : P.primeCompl) *
          algebraMap _ _ s
      rw [mul_assoc, IsLocalization.mk'_spec, ← map_mul, ← map_mul, hbs]
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hϖP
  rw [← hmax]
  change IsRegularLocalRing (IsLocalRing.ResidueField (Localization.AtPrime P))
  infer_instance

end GenRed

set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing
open AlgebraicCurve.TwoChartIntegralModel

namespace OrdRegL0

theorem algebraMap_stalk_eq_germ {S : Type} [CommRing S] (q : ↥(Spec (CommRingCat.of S))) (s : S) :
    letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
    algebraMap S ((Spec (CommRingCat.of S)).presheaf.stalk q) s =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) := by
  show AlgebraicGeometry.StructureSheaf.toStalk S q s = _
  rfl

theorem exists_ringEquiv_stalk_localization_map_germ_eq
    {A S : Type} [CommRing A] [CommRing S] [Algebra A S] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A S))) (q : ↥(Spec (CommRingCat.of S))) :
    ∃ E : X.presheaf.stalk (ι.base q) ≃+* Localization.AtPrime q.asIdeal,
      ∀ a : A, E ((X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
        algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S a) := by
  have key : ∀ a : A, (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap A S a)) := by
    intro a
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A S))).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
  let E₁ : X.presheaf.stalk (ι.base q) ≃+* (Spec (CommRingCat.of S)).presheaf.stalk q :=
    (asIso (ι.stalkMap q)).commRingCatIsoToRingEquiv
  let E₂ : ((Spec (CommRingCat.of S)).presheaf.stalk q) ≃ₐ[S] Localization.AtPrime q.asIdeal :=
    (AlgebraicGeometry.StructureSheaf.stalkIso S q).symm
  refine ⟨E₁.trans E₂.toRingEquiv, fun a => ?_⟩
  rw [RingEquiv.trans_apply]
  change E₂ ((ι.stalkMap q).hom _) = _
  rw [key a, ← algebraMap_stalk_eq_germ q (algebraMap A S a)]
  exact E₂.commutes _

variable (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

theorem L0_isRegularLocalRing_fibre_of_localization
    (ϖ : A) (z : ↥(AlgebraicCurve.TwoChartIntegralModel A K j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ z trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (y : ↥(XFin A K j)) (hy : (ιFin A K j).base y = z)
    (h : IsRegularLocalRing (Localization.AtPrime y.asIdeal ⧸
      Ideal.span {algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y.asIdeal) (algebraMap A _ ϖ)})) :
    IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by
  subst hy
  subst hϖz
  obtain ⟨E, hE⟩ := exists_ringEquiv_stalk_localization_map_germ_eq (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y
  refine @IsRegularLocalRing.of_ringEquiv _ _ h _ _ (Ideal.quotientEquiv _ _ E.symm ?_)
  rw [Ideal.map_span, Set.image_singleton, ← hE ϖ]
  simp only [RingHom.coe_coe, RingEquiv.symm_apply_apply]

end OrdRegL0

open GenRed OrdRegL0 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hgen : ¬ y.asIdeal.IsMaximal)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal) :
    IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by
  classical

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
  have hK' : K = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) := hK
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange _
      (ModularCurve.translation_mem_GammaH _ _) L K hK' j hj
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _

  obtain ⟨W, hW, hWA, hWm, hWj, hWnu⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC _ L K hK' A j hj
  have hWW : W = W₀ := by
    ext f
    exact (hW f).trans (hW₀ f).symm
  subst hWW

  obtain ⟨-, ⟨𝔓, h𝔓p, h𝔓ht, h𝔓mem, h𝔓A, h𝔓loc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K) j htj hFD hsep W hWA hWm hWj
  haveI := h𝔓p

  have hle : 𝔓 ≤ y.asIdeal := fun b hb => hz₀ b ((h𝔓mem b).mp hb)
  have hdimB : ringKrullDim ↥(chartAlgFin A (↥K) j) ≤ 2 := by
    refine (ringKrullDim_chartAlg_singleton_le A (↥K) (j : ↥K)).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one A]
    norm_num
  have hy𝔓 : y.asIdeal = 𝔓 := eq_of_height_eq_one_of_le_of_not_isMaximal hdimB 𝔓 y.asIdeal h𝔓ht hle hgen
  subst hy𝔓

  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hϖ0 : ϖ ≠ 0 := fun h => IsDiscreteValuationRing.not_a_field A (by rw [hϖ, h, Ideal.span_singleton_eq_bot])
  have hϖ0L : algebraMap A L ϖ ≠ 0 := fun h => hϖ0 (IsFractionRing.injective A L (by rw [h, map_zero]))
  apply L0_isRegularLocalRing_fibre_of_localization A (↥K) j ϖ z ϖz hϖz y hy
  exact isRegularLocalRing_quotient_localization_of_forall_exists y.asIdeal ϖ (h𝔓A ϖ hϖm)
    (fun b hb => exists_mul_eq_of_mem_centre ϖ hϖ hϖ0L W hW₀ hWnu
      ((chartAlgFin A (↥K) j).restrictScalars A) y.asIdeal h𝔓mem h𝔓loc b hb)

end S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_not_isMaximal_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH
end P2MW
export P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_not_isMaximal_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH (solution)
