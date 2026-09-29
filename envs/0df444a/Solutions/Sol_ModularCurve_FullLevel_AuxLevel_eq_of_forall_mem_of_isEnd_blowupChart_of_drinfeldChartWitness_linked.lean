-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.eq_of_forall_mem_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/93fbb0d4-bf2f-5119-9712-9e60ddcb57fd

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_eq_of_forall_mem_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace EndsIncomp

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

section Pin
variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem pin_mem (Ba : Subalgebra A K) (P : Ideal ↥Ba) (O : Subring K)
    (hloc : ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K))
    (h1 : (1 : ↥Ba) ∉ P) (x : ↥Ba) : (x : K) ∈ O :=
  (hloc _).mpr ⟨x, 1, h1, by simp⟩

theorem pin_isUnit_of_not_mem (Ba : Subalgebra A K) (P : Ideal ↥Ba) (O : Subring K)
    (hloc : ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K))
    (h1 : (1 : ↥Ba) ∉ P) (x : ↥Ba) (hx : x ∉ P) (hxO : (x : K) ∈ O) :
    IsUnit (⟨(x : K), hxO⟩ : ↥O) := by
  have hx0 : (x : K) ≠ 0 := by
    intro h
    apply hx
    have : x = 0 := Subtype.ext h
    rw [this]; exact P.zero_mem
  have hinv : (x : K)⁻¹ ∈ O := (hloc _).mpr ⟨1, x, hx, by rw [inv_mul_cancel₀ hx0]; simp⟩
  exact isUnit_iff_exists_inv.mpr ⟨⟨(x : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem pin_not_isUnit_iff (Ba : Subalgebra A K) (P : Ideal ↥Ba) (hP : P.IsPrime) (O : Subring K)
    (hloc : ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K))
    (f : K) (hf : f ∈ O) :
    ¬ IsUnit (⟨f, hf⟩ : ↥O) ↔ ∃ g h : ↥Ba, h ∉ P ∧ g ∈ P ∧ f * (h : K) = (g : K) := by
  have h1 : (1 : ↥Ba) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  constructor
  · intro hnu
    obtain ⟨g, h, hh, hfh⟩ := (hloc f).mp hf
    refine ⟨g, h, hh, ?_, hfh⟩
    by_contra hg
    apply hnu
    have hg0 : (g : K) ≠ 0 := by
      intro h0; apply hg
      have : g = 0 := Subtype.ext h0
      rw [this]; exact P.zero_mem
    have hhg : (h : K) * (g : K)⁻¹ ∈ O :=
      (hloc _).mpr ⟨h, g, hg, by rw [mul_assoc, inv_mul_cancel₀ hg0, mul_one]⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(h : K) * (g : K)⁻¹, hhg⟩, Subtype.ext ?_⟩
    show f * ((h : K) * (g : K)⁻¹) = 1
    rw [← mul_assoc, hfh, mul_inv_cancel₀ hg0]
  · rintro ⟨g, h, hh, hg, hfh⟩ hu
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨g', h', hh', hvh⟩ := (hloc (v : K)).mp v.2
    have hfv : f * (v : K) = 1 := by
      have := congrArg Subtype.val hv
      exact this
    have key : ((h * h' : ↥Ba) : K) = ((g * g' : ↥Ba) : K) := by
      push_cast
      rw [← hfh, ← hvh]
      calc (h : K) * (h' : K) = (f * (v : K)) * ((h : K) * (h' : K)) := by rw [hfv, one_mul]
        _ = f * (h : K) * ((v : K) * (h' : K)) := by ring
    have hmem : h * h' ∈ P := by
      rw [Subtype.ext key]; exact P.mul_mem_right _ hg
    rcases hP.mem_or_mem hmem with h1' | h2'
    · exact hh h1'
    · exact hh' h2'

theorem pin_not_isUnit_of_mem (Ba : Subalgebra A K) (P : Ideal ↥Ba) (hP : P.IsPrime) (O : Subring K)
    (hloc : ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K))
    (x : ↥Ba) (hx : x ∈ P) (hxO : (x : K) ∈ O) : ¬ IsUnit (⟨(x : K), hxO⟩ : ↥O) := by
  have h1 : (1 : ↥Ba) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  exact (pin_not_isUnit_iff Ba P hP O hloc _ hxO).mpr ⟨x, 1, h1, hx, by simp⟩

theorem pin_isLocalRing (Ba : Subalgebra A K) (P : Ideal ↥Ba) (hP : P.IsPrime) (O : Subring K)
    (hloc : ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K)) :
    IsLocalRing ↥O := by
  refine IsLocalRing.of_nonunits_add ?_
  intro u v hu hv
  rw [mem_nonunits_iff] at hu hv ⊢
  have hu' := (pin_not_isUnit_iff Ba P hP O hloc (u : K) u.2).mp (by exact hu)
  have hv' := (pin_not_isUnit_iff Ba P hP O hloc (v : K) v.2).mp (by exact hv)
  obtain ⟨g₁, h₁, hh₁, hg₁, e₁⟩ := hu'
  obtain ⟨g₂, h₂, hh₂, hg₂, e₂⟩ := hv'
  have key := (pin_not_isUnit_iff Ba P hP O hloc ((u : K) + (v : K)) (O.add_mem u.2 v.2)).mpr
    ⟨g₁ * h₂ + g₂ * h₁, h₁ * h₂, fun hm => (hP.mem_or_mem hm).elim hh₁ hh₂,
      P.add_mem (P.mul_mem_right _ hg₁) (P.mul_mem_right _ hg₂), by
        push_cast
        rw [← e₁, ← e₂]; ring⟩
  exact key

end Pin

section Integral
variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem exists_monic_eval₂_not_isUnit [IsLocalRing A]
    (Ba : Subalgebra A K) [hft : Algebra.FiniteType A ↥Ba] (P : Ideal ↥Ba) (hP : P.IsMaximal) (O : Subring K)
    (hloc : ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K))
    (hAP : ∀ a : A, a ∈ maximalIdeal A → algebraMap A ↥Ba a ∈ P) :
    ∀ (f : K) (hf : f ∈ O), ∃ p : Polynomial A, p.Monic ∧
      ∃ hpf : Polynomial.eval₂ (algebraMap A K) f p ∈ O, ¬ IsUnit (⟨_, hpf⟩ : ↥O) := by
  classical
  have hPp : P.IsPrime := hP.isPrime
  have h1 : (1 : ↥Ba) ∉ P := fun h => hPp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  haveI : IsLocalRing ↥O := pin_isLocalRing Ba P hPp O hloc
  have memO : ∀ x : ↥Ba, (x : K) ∈ O := pin_mem Ba P O hloc h1
  have hcoeA : ∀ a : A, ((algebraMap A ↥Ba a : ↥Ba) : K) = algebraMap A K a := fun a => rfl
  have hAO : ∀ a : A, algebraMap A K a ∈ O := fun a => by rw [← hcoeA]; exact memO _
  letI algAO : Algebra A ↥O := ((algebraMap A K).codRestrict O hAO).toAlgebra
  have halgO : ∀ a : A, ((algebraMap A ↥O a : ↥O) : K) = algebraMap A K a := fun a => rfl
  let ι : ↥Ba →ₐ[A] ↥O :=
    { toFun := fun x => ⟨(x : K), memO x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      commutes' := fun a => Subtype.ext (by rw [halgO]; rfl) }
  have hιP : ∀ x : ↥Ba, x ∈ P → ι x ∈ maximalIdeal ↥O := by
    intro x hx
    exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (pin_not_isUnit_of_mem Ba P hPp O hloc x hx (memO x)))
  let π : ↥O →ₐ[A] (↥O ⧸ maximalIdeal ↥O) := Ideal.Quotient.mkₐ A (maximalIdeal ↥O)
  have hsurj : Function.Surjective (π.comp ι) := by
    intro z
    obtain ⟨⟨f, hf⟩, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨g, h, hh, hfh⟩ := (hloc f).mp hf
    haveI := hP
    letI := Ideal.Quotient.field P
    have hne : Ideal.Quotient.mk P h ≠ 0 := by
      intro h0; exact hh (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    obtain ⟨k, hk⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk P h)⁻¹
    have hk1 : h * k - 1 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, hk, mul_inv_cancel₀ hne, sub_self]
    refine ⟨g * k, ?_⟩
    show Ideal.Quotient.mk (maximalIdeal ↥O) (ι (g * k)) = Ideal.Quotient.mk (maximalIdeal ↥O) ⟨f, hf⟩
    rw [Ideal.Quotient.eq]
    have hmem := hιP _ hk1
    have : (⟨f, hf⟩ : ↥O) - ι (g * k) = - (⟨f, hf⟩ * ι (h * k - 1)) := by
      apply Subtype.ext
      show f - ((g : K) * (k : K)) = - (f * ((h : K) * (k : K) - 1))
      rw [← hfh]; ring
    rw [show ι (g * k) - (⟨f, hf⟩ : ↥O) = - ((⟨f, hf⟩ : ↥O) - ι (g * k)) by ring, this, neg_neg]
    exact Ideal.mul_mem_left _ _ hmem
  haveI hftO : Algebra.FiniteType A (↥O ⧸ maximalIdeal ↥O) := hft.of_surjective (π.comp ι) hsurj
  have hkill : ∀ a : A, a ∈ maximalIdeal A → algebraMap A (↥O ⧸ maximalIdeal ↥O) a = 0 := by
    intro a ha
    rw [show algebraMap A (↥O ⧸ maximalIdeal ↥O) a = Ideal.Quotient.mk (maximalIdeal ↥O) (algebraMap A ↥O a) from rfl,
      Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap A ↥O a = ι (algebraMap A ↥Ba a) := Subtype.ext (by rw [halgO]; rfl)
    rw [this]
    exact hιP _ (hAP a ha)
  let φ : ResidueField A →+* (↥O ⧸ maximalIdeal ↥O) :=
    Ideal.Quotient.lift (maximalIdeal A) (algebraMap A (↥O ⧸ maximalIdeal ↥O)) hkill
  letI algR : Algebra (ResidueField A) (↥O ⧸ maximalIdeal ↥O) := φ.toAlgebra
  haveI : IsScalarTower A (ResidueField A) (↥O ⧸ maximalIdeal ↥O) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI hftR : Algebra.FiniteType (ResidueField A) (↥O ⧸ maximalIdeal ↥O) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (ResidueField A) (↥O ⧸ maximalIdeal ↥O)
  letI : Field (↥O ⧸ maximalIdeal ↥O) := Ideal.Quotient.field (maximalIdeal ↥O)
  have hfin := finite_of_finite_type_of_isJacobsonRing (ResidueField A) (↥O ⧸ maximalIdeal ↥O)
  intro f hf
  have hint : IsIntegral (ResidueField A) (Ideal.Quotient.mk (maximalIdeal ↥O) (⟨f, hf⟩ : ↥O)) := by
    haveI := hfin
    exact IsIntegral.of_finite (ResidueField A) _
  obtain ⟨p₀, hp₀, hp₀x⟩ := hint
  have hlifts : p₀ ∈ Polynomial.lifts (algebraMap A (ResidueField A)) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ Ideal.Quotient.mk_surjective p₀
  obtain ⟨p, hpmap, -, hpmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp₀
  refine ⟨p, hpmonic, ?_⟩
  have heval : Polynomial.aeval (Ideal.Quotient.mk (maximalIdeal ↥O) (⟨f, hf⟩ : ↥O)) p = 0 := by
    rw [← Polynomial.aeval_map_algebraMap (ResidueField A), hpmap]
    exact hp₀x
  have heval2 : Ideal.Quotient.mk (maximalIdeal ↥O) (Polynomial.aeval (⟨f, hf⟩ : ↥O) p) = 0 := by
    rw [← heval, ← Ideal.Quotient.mkₐ_eq_mk A, ← Polynomial.aeval_algHom_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem] at heval2
  have hval : ((Polynomial.aeval (⟨f, hf⟩ : ↥O) p : ↥O) : K) = Polynomial.eval₂ (algebraMap A K) f p := by
    rw [Polynomial.aeval_def, show ((Polynomial.eval₂ (algebraMap A ↥O) (⟨f, hf⟩ : ↥O) p : ↥O) : K) =
      O.subtype (Polynomial.eval₂ (algebraMap A ↥O) ⟨f, hf⟩ p) from rfl, Polynomial.hom_eval₂]
    rfl
  refine ⟨hval ▸ (Polynomial.aeval (⟨f, hf⟩ : ↥O) p).2, ?_⟩
  have : (⟨Polynomial.eval₂ (algebraMap A K) f p, hval ▸ (Polynomial.aeval (⟨f, hf⟩ : ↥O) p).2⟩ : ↥O) =
      Polynomial.aeval (⟨f, hf⟩ : ↥O) p := Subtype.ext hval.symm
  rw [this]
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp heval2)

theorem finiteType_chart [IsNoetherianRing A] (C : Subalgebra A K) (hC : Algebra.FiniteType A ↥C)
    (J : Ideal ↥C) (a : K) (ha : a ≠ 0) :
    Algebra.FiniteType A ↥((Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * a = ((i : ↥C) : K)}).restrictScalars A) := by
  classical
  haveI : IsNoetherianRing ↥C := Algebra.FiniteType.isNoetherianRing A ↥C
  obtain ⟨s, hs⟩ := (inferInstance : IsNoetherian ↥C ↥C).noetherian J
  have heq : Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * a = ((i : ↥C) : K)} =
      Algebra.adjoin ↥C (↑(s.image fun i : ↥C => ((i : ↥C) : K) * a⁻¹) : Set K) := by
    apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro x ⟨i, hi, hx⟩
      have hx' : x = ((i : ↥C) : K) * a⁻¹ := by rw [← hx, mul_assoc, mul_inv_cancel₀ ha, mul_one]
      rw [hx']
      rw [← hs] at hi
      refine Submodule.span_induction (p := fun i _ => ((i : ↥C) : K) * a⁻¹ ∈
          Algebra.adjoin ↥C (↑(s.image fun i : ↥C => ((i : ↥C) : K) * a⁻¹) : Set K)) ?_ ?_ ?_ ?_ hi
      · intro g hg
        exact Algebra.subset_adjoin (by simp only [Finset.coe_image]; exact ⟨g, hg, rfl⟩)
      · simp
      · intro u v _ _ hu hv
        rw [Subalgebra.coe_add, add_mul]; exact Subalgebra.add_mem _ hu hv
      · intro c u _ hu
        rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]
        have : ((c : ↥C) : K) * (((u : ↥C) : K) * a⁻¹) = algebraMap (↥C) K c * (((u : ↥C) : K) * a⁻¹) := rfl
        rw [this]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hu
    · refine Algebra.adjoin_le ?_
      intro x hx
      simp only [Finset.coe_image, Set.mem_image] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      refine Algebra.subset_adjoin ⟨g, ?_, by rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]⟩
      rw [← hs]; exact Submodule.subset_span hg
  have hfg : (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * a = ((i : ↥C) : K)}).FG := by
    rw [heq]; exact Subalgebra.fg_adjoin_finset _
  have hftC : Algebra.FiniteType ↥C ↥(Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * a = ((i : ↥C) : K)}) :=
    (Subalgebra.fg_iff_finiteType _).mp hfg
  have hftA : Algebra.FiniteType A ↥(Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * a = ((i : ↥C) : K)}) :=
    hC.trans hftC
  exact hftA

end Integral

section Core
variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem core' [IsLocalRing A] [IsNoetherianRing A]
    (C : Subalgebra A K) (J y : Ideal ↥C)
    (hAy : ∀ a : A, a ∈ maximalIdeal A → algebraMap A ↥C a ∈ y)
    (O O' : Subring K)
    (a : ↥C) (haJ : a ∈ J) (ha0 : ((a : ↥C) : K) ≠ 0)
    (Ba : Subalgebra A K)
    (hmemBa : ∀ x : K, x ∈ Ba ↔ x ∈ Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)})
    [hftBa : Algebra.FiniteType A ↥Ba]
    (P : Ideal ↥Ba) (hP : P.IsMaximal)
    (hOloc : ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K))
    (hOy : ∀ b : ↥C, b ∈ y → ∀ hb : ((b : ↥C) : K) ∈ O, ¬ IsUnit (⟨((b : ↥C) : K), hb⟩ : ↥O))
    (a' : ↥C) (haJ' : a' ∈ J) (ha0' : ((a' : ↥C) : K) ≠ 0)
    (Ba' : Subalgebra A K)
    (hmemBa' : ∀ x : K, x ∈ Ba' ↔ x ∈ Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * ((a' : ↥C) : K) = ((i : ↥C) : K)})
    (P' : Ideal ↥Ba') (hP' : P'.IsMaximal)
    (hOloc' : ∀ f : K, f ∈ O' ↔ ∃ g h : ↥Ba', h ∉ P' ∧ f * (h : K) = (g : K))
    (hle : ∀ f : K, f ∈ O' → f ∈ O) : O = O' := by
  classical
  have hPp : P.IsPrime := hP.isPrime
  have hPp' : P'.IsPrime := hP'.isPrime
  have h1 : (1 : ↥Ba) ∉ P := fun h => hPp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have h1' : (1 : ↥Ba') ∉ P' := fun h => hPp'.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have memO : ∀ x : ↥Ba, (x : K) ∈ O := pin_mem Ba P O hOloc h1
  have memO' : ∀ x : ↥Ba', (x : K) ∈ O' := pin_mem Ba' P' O' hOloc' h1'
  haveI : IsLocalRing ↥O := pin_isLocalRing Ba P hPp O hOloc
  haveI : IsLocalRing ↥O' := pin_isLocalRing Ba' P' hPp' O' hOloc'
  have hleS : O' ≤ O := fun f hf => hle f hf
  have hCBa : ∀ c : ↥C, (c : K) ∈ Ba := fun c => by
    rw [hmemBa]; exact Subalgebra.algebraMap_mem _ c
  have hCBa' : ∀ c : ↥C, (c : K) ∈ Ba' := fun c => by
    rw [hmemBa']; exact Subalgebra.algebraMap_mem _ c
  have htBa' : ((a : ↥C) : K) * (((a' : ↥C) : K))⁻¹ ∈ Ba' := by
    rw [hmemBa']
    exact Algebra.subset_adjoin ⟨a, haJ, inv_mul_cancel_right₀ ha0' _⟩
  have ht'Ba : ((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹ ∈ Ba := by
    rw [hmemBa]
    exact Algebra.subset_adjoin ⟨a', haJ', inv_mul_cancel_right₀ ha0 _⟩
  have htO : ((a : ↥C) : K) * (((a' : ↥C) : K))⁻¹ ∈ O := hle _ (memO' ⟨_, htBa'⟩)
  have ht'O : ((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹ ∈ O := memO ⟨_, ht'Ba⟩
  have htt' : ((a : ↥C) : K) * (((a' : ↥C) : K))⁻¹ * (((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹) = 1 := by
    field_simp
  have htunit : IsUnit (⟨_, htO⟩ : ↥O) :=
    isUnit_iff_exists_inv.mpr ⟨⟨_, ht'O⟩, Subtype.ext htt'⟩
  have hAP : ∀ a₀ : A, a₀ ∈ maximalIdeal A → algebraMap A ↥Ba a₀ ∈ P := by
    intro a₀ ha₀
    by_contra hnot
    have hu := pin_isUnit_of_not_mem Ba P O hOloc h1 _ hnot (memO _)
    exact hOy (algebraMap A ↥C a₀) (hAy a₀ ha₀) (memO (algebraMap A ↥Ba a₀)) hu
  let ι' : ↥Ba' →+* ↥O :=
    { toFun := fun x => ⟨(x : K), hle _ (memO' x)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  let P'' : Ideal ↥Ba' := Ideal.comap ι' (maximalIdeal ↥O)
  have hP''le : P'' ≤ P' := by
    intro x hx
    by_contra hxP'
    have hu : IsUnit (⟨(x : K), memO' x⟩ : ↥O') := pin_isUnit_of_not_mem Ba' P' O' hOloc' h1' x hxP' (memO' x)
    have hu2 : IsUnit (ι' x) := hu.map (Subring.inclusion hleS)
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hx)) hu2
  have hint := exists_monic_eval₂_not_isUnit Ba P hP O hOloc hAP
  have hP''max : P''.IsMaximal := by
    haveI : P''.IsPrime := Ideal.comap_isPrime ι' _
    have hf : ((Ideal.Quotient.mk P'').comp (algebraMap A ↥Ba')).IsIntegral := by
      intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨p, hpm, hpO, hnu⟩ := hint (x : K) (hle _ (memO' x))
      refine ⟨p, hpm, ?_⟩
      rw [← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
      show ι' (Polynomial.eval₂ (algebraMap A ↥Ba') x p) ∈ maximalIdeal ↥O
      have hval : ι' (Polynomial.eval₂ (algebraMap A ↥Ba') x p) = ⟨_, hpO⟩ := by
        apply Subtype.ext
        show ((Polynomial.eval₂ (algebraMap A ↥Ba') x p : ↥Ba') : K) = Polynomial.eval₂ (algebraMap A K) (x : K) p
        rw [← Polynomial.aeval_def, ← Polynomial.aeval_def, Subalgebra.aeval_coe]
      rw [hval]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have hker : Ideal.comap ((Ideal.Quotient.mk P'').comp (algebraMap A ↥Ba')) ⊥ = maximalIdeal A := by
      symm
      apply (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
      · intro htop
        have hone : (1 : A) ∈ Ideal.comap ((Ideal.Quotient.mk P'').comp (algebraMap A ↥Ba')) ⊥ := by
          rw [htop]; exact Submodule.mem_top
        rw [Ideal.mem_comap, Ideal.mem_bot, map_one] at hone
        exact one_ne_zero hone
      · intro a₀ ha₀
        rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        show ι' (algebraMap A ↥Ba' a₀) ∈ maximalIdeal ↥O
        have hmemC : ((algebraMap A ↥C a₀ : ↥C) : K) ∈ O' := memO' ⟨((algebraMap A ↥C a₀ : ↥C) : K), hCBa' (algebraMap A ↥C a₀)⟩
        have hval : ι' (algebraMap A ↥Ba' a₀) = ⟨((algebraMap A ↥C a₀ : ↥C) : K), hle _ hmemC⟩ :=
          Subtype.ext rfl
        rw [hval]
        exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hOy _ (hAy a₀ ha₀) _))
    have hbot : (⊥ : Ideal (↥Ba' ⧸ P'')).IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hf ⊥ ?_
      rw [hker]; exact IsLocalRing.maximalIdeal.isMaximal A
    have h := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk P'') Ideal.Quotient.mk_surjective (K := ⊥)
    rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
  have hP''eq : P'' = P' := hP''max.eq_of_le hP'.ne_top hP''le
  have htP' : (⟨_, htBa'⟩ : ↥Ba') ∉ P' := by
    rw [← hP''eq]
    intro h
    have h' := mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h)
    exact h' htunit
  have htunit' : IsUnit (⟨_, memO' ⟨_, htBa'⟩⟩ : ↥O') := pin_isUnit_of_not_mem Ba' P' O' hOloc' h1' _ htP' _
  have ht'O' : ((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹ ∈ O' := by
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp htunit'
    have hv' : ((a : ↥C) : K) * (((a' : ↥C) : K))⁻¹ * (v : K) = 1 := congrArg Subtype.val hv
    have : (v : K) = ((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹ := by
      calc (v : K) = (((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹ * (((a : ↥C) : K) * (((a' : ↥C) : K))⁻¹)) * (v : K) := by
              rw [show ((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹ * (((a : ↥C) : K) * (((a' : ↥C) : K))⁻¹) = 1 by field_simp, one_mul]
        _ = ((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹ := by rw [mul_assoc, hv', mul_one]
    rw [← this]; exact v.2
  have hBaO' : ∀ x : ↥Ba, (x : K) ∈ O' := by
    rintro ⟨x₁, hx⟩
    simp only
    rw [hmemBa] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x₀ hx₀ =>
        obtain ⟨i, hi, hxi⟩ := hx₀
        have hiBa' : ((i : ↥C) : K) * (((a' : ↥C) : K))⁻¹ ∈ Ba' := by
          rw [hmemBa']
          exact Algebra.subset_adjoin ⟨i, hi, inv_mul_cancel_right₀ ha0' _⟩
        have hx₀eq : x₀ = ((i : ↥C) : K) * (((a' : ↥C) : K))⁻¹ * (((a' : ↥C) : K) * (((a : ↥C) : K))⁻¹) := by
          rw [← hxi]; field_simp
        rw [hx₀eq]
        exact O'.mul_mem (memO' ⟨_, hiBa'⟩) ht'O'
    | algebraMap c => exact memO' ⟨_, hCBa' c⟩
    | add u v _ _ hu hv => exact O'.add_mem hu hv
    | mul u v _ _ hu hv => exact O'.mul_mem hu hv
  have hunitO' : ∀ h : ↥Ba, h ∉ P → IsUnit (⟨(h : K), hBaO' h⟩ : ↥O') := by
    intro h hh
    haveI := hP
    letI := Ideal.Quotient.field P
    have hne : Ideal.Quotient.mk P h ≠ 0 := fun h0 => hh (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    obtain ⟨k, hk⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk P h)⁻¹
    have hk1 : h * k - 1 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, hk, mul_inv_cancel₀ hne, sub_self]
    have hcO : ¬ IsUnit (⟨((h * k - 1 : ↥Ba) : K), memO _⟩ : ↥O) := pin_not_isUnit_of_mem Ba P hPp O hOloc _ hk1 _
    have hcO' : ¬ IsUnit (⟨((h * k - 1 : ↥Ba) : K), hBaO' _⟩ : ↥O') := by
      intro hu; exact hcO (hu.map (Subring.inclusion hleS))
    have hhk : IsUnit (⟨(h : K), hBaO' h⟩ * ⟨(k : K), hBaO' k⟩ : ↥O') := by
      apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
      rw [mem_nonunits_iff]
      have : (1 : ↥O') - ⟨(h : K), hBaO' h⟩ * ⟨(k : K), hBaO' k⟩ = - ⟨((h * k - 1 : ↥Ba) : K), hBaO' _⟩ := by
        apply Subtype.ext
        show (1 : K) - (h : K) * (k : K) = - (((h * k - 1 : ↥Ba) : K))
        push_cast; ring
      rw [this, IsUnit.neg_iff]
      exact hcO'
    exact isUnit_of_mul_isUnit_left hhk
  have hOO' : ∀ f : K, f ∈ O → f ∈ O' := by
    intro f hf
    obtain ⟨g, h, hh, hfh⟩ := (hOloc f).mp hf
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp (hunitO' h hh)
    have hv' : (h : K) * (v : K) = 1 := congrArg Subtype.val hv
    have : f = (g : K) * (v : K) := by
      calc f = f * ((h : K) * (v : K)) := by rw [hv', mul_one]
        _ = f * (h : K) * (v : K) := by ring
        _ = (g : K) * (v : K) := by rw [hfh]
    rw [this]
    exact O'.mul_mem (hBaO' g) v.2
  exact le_antisymm (fun f hf => hOO' f hf) hleS

theorem core [IsLocalRing A] [IsNoetherianRing A]
    (C : Subalgebra A K) (J y : Ideal ↥C) (B : Subalgebra A K)
    (hAy : ∀ a : A, a ∈ maximalIdeal A → algebraMap A ↥C a ∈ y)
    (hCft : Algebra.FiniteType A ↥C)
    (O O' : Subring K)
    (hO : ∃ (a : ↥C) (_ : a ∈ J) (_ : ((a : ↥C) : K) ≠ 0),
          let Ba : Subalgebra A K := (Algebra.adjoin ↥C
            {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K)) ∧
            (∀ b : ↥C, b ∈ y → ∀ hb : ((b : ↥C) : K) ∈ O, ¬ IsUnit (⟨((b : ↥C) : K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : K, f ∈ B → f ∈ O))
    (hO' : ∃ (a : ↥C) (_ : a ∈ J) (_ : ((a : ↥C) : K) ≠ 0),
          let Ba : Subalgebra A K := (Algebra.adjoin ↥C
            {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : K, f ∈ O' ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K)) ∧
            (∀ b : ↥C, b ∈ y → ∀ hb : ((b : ↥C) : K) ∈ O', ¬ IsUnit (⟨((b : ↥C) : K), hb⟩ : ↥O')) ∧
            ¬ (∀ f : K, f ∈ B → f ∈ O'))
    (hle : ∀ f : K, f ∈ O' → f ∈ O) : O = O' := by
  classical
  obtain ⟨a, haJ, ha0, P, hP, hOloc, hOy, -⟩ := hO
  obtain ⟨a', haJ', ha0', P', hP', hOloc', -, -⟩ := hO'
  haveI := finiteType_chart C hCft J ((a : ↥C) : K) ha0
  exact core' C J y hAy O O' a haJ ha0 _ (fun x => Subalgebra.mem_restrictScalars A) P hP hOloc hOy
    a' haJ' ha0' _ (fun x => Subalgebra.mem_restrictScalars A) P' hP' hOloc' hle

end Core

end EndsIncomp

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
                (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))
    (O O' : Subring ↥K)
    (hO : ∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O))
    (hO' : ∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O' ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O', ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O')) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O'))
    (hle : ∀ f : ↥K, f ∈ O' → f ∈ O)
    :
      O = O' := by

  have hAy : ∀ a₀ : A, a₀ ∈ maximalIdeal A → algebraMap A ↥(chartAlgFin A (↥K) j) a₀ ∈ y := by
    intro a₀ ha₀
    rw [hϖ, Ideal.mem_span_singleton] at ha₀
    obtain ⟨b, rfl⟩ := ha₀
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ hϖy

  have htA : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have htL : Transcendental L j := fun h => htA ((IsFractionRing.isAlgebraic_iff A L ↥K).mpr h)
  haveI : NeZero ((q * ℓ) ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (mul_ne_zero (Fact.out : q.Prime).ne_zero
    (Fact.out : ℓ.Prime).ne_zero)) (NeZero.ne M')⟩
  have hCE := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField L ((q * ℓ) ^ 2 * M')
    (ModularCurve.FullLevel.levelH (q * ℓ) M')
  have hCft : Algebra.FiniteType A ↥(chartAlgFin A (↥K) j) := by
    subst hK
    obtain ⟨hcurve, hess⟩ := hCE
    have hfd : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥(ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))))
        ↥(ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :=
      AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType htL
    have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥(ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))))
        ↥(ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M'))) := inferInstance
    exact (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L _ j htA hfd hsep).1
  exact EndsIncomp.core (chartAlgFin A (↥K) j) J y B hAy hCft O O' hO hO' hle

end S_ModularCurve_FullLevel_AuxLevel_eq_of_forall_mem_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_eq_of_forall_mem_of_isEnd_blowupChart_of_drinfeldChartWitness_linked (solution)
