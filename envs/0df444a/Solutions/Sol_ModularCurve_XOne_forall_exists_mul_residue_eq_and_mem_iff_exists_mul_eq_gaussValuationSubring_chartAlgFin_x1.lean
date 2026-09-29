-- Prove2me | solution 1 for ModularCurve.XOne.forall_exists_mul_residue_eq_and_mem_iff_exists_mul_eq_gaussValuationSubring_chartAlgFin_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/53ccb158-f010-521d-a200-93c89b5fc364

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_forall_exists_mul_residue_eq_and_mem_iff_exists_mul_eq_gaussValuationSubring_chartAlgFin_x1
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace GaussLocal

theorem CruxC.false_of_chain {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.IsIntegral R S] (hR : ringKrullDim R ≤ ((2 : ℕ) : ℕ∞))
    {𝔮 𝔭' m : Ideal S} [𝔮.IsPrime] [𝔭'.IsPrime] [m.IsPrime]
    (h0 : 𝔮 ≠ ⊥) (h1 : 𝔮 < 𝔭') (h2 : 𝔭' < m) : False := by
  have hb : (⊥ : Ideal S) < 𝔮 := bot_lt_iff_ne_bot.mpr h0
  have c01 := Ideal.IsIntegral.comap_lt_comap (R := R) hb
  have c12 := Ideal.IsIntegral.comap_lt_comap (R := R) h1
  have c23 := Ideal.IsIntegral.comap_lt_comap (R := R) h2
  have e01 := Ideal.height_add_one_le_of_lt_of_isPrime c01
  have e12 := Ideal.height_add_one_le_of_lt_of_isPrime c12
  have e23 := Ideal.height_add_one_le_of_lt_of_isPrime c23
  have h3 : ((3 : ℕ) : ℕ∞) ≤ (m.comap (algebraMap R S)).height :=
    calc ((3 : ℕ) : ℕ∞) = 0 + 1 + 1 + 1 := by norm_num
      _ ≤ (Ideal.comap (algebraMap R S) ⊥).height + 1 + 1 + 1 := by gcongr; simp
      _ ≤ (Ideal.comap (algebraMap R S) 𝔮).height + 1 + 1 := by gcongr
      _ ≤ (Ideal.comap (algebraMap R S) 𝔭').height + 1 := by gcongr
      _ ≤ (Ideal.comap (algebraMap R S) m).height := e23
  have h4 : (((3 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ) : ℕ∞) :=
    (WithBot.coe_le_coe.mpr h3).trans (Ideal.height_le_ringKrullDim_of_isPrime.trans hR)
  have h5 : ((3 : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp h4
  have h6 : (3 : ℕ) ≤ 2 := by exact_mod_cast h5
  omega

theorem CruxC.ringKrullDim_polynomial_le (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ringKrullDim (Polynomial A) ≤ ((2 : ℕ) : ℕ∞) := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
  exact le_of_eq (by norm_cast)

end GaussLocal

open GaussLocal in
set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hSW₀ : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀) :
    (∀ e : IsLocalRing.ResidueField ↥W₀, ∃ s t : ↥(chartAlgFin A (↥K₁) j), (t : ↥K₁) ∉ W₀.nonunits ∧
      e * IsLocalRing.residue ↥W₀ ⟨(t : ↥K₁), hSW₀ t⟩ = IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩) ∧
    (∀ f : ↥K₁, f ∈ W₀ ↔ ∃ c s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∉ W₀.nonunits ∧ f * (s : ↥K₁) = (c : ↥K₁)) := by
  classical
  haveI hp : Fact p.Prime := inferInstance
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖmax : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ

  obtain ⟨W₀', hW₀', hA', hAm', hWj', -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField M L K₁ hK₁ A j hj
  have hWW : W₀ = W₀' := by ext f; rw [hW₀ f, hW₀' f]
  have hAm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₁ a ∈ W₀.nonunits := by rw [hWW]; exact hAm'
  have hWj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ W₀ ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀ := by rw [hWW]; exact hWj'
  have hϖK0 : algebraMap A ↥K₁ ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A L ↥K₁, map_ne_zero]
    exact fun h => hϖirr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective A L)).mp h)
  have hW₀top : W₀ ≠ ⊤ := by
    intro htop
    have hnu := hAm ϖ hϖmax
    rcases (ValuationSubring.mem_nonunits_iff_or W₀).mp hnu with h0 | hninv
    · exact hϖK0 h0
    · exact hninv (by rw [htop]; exact ValuationSubring.mem_top _)

  let φ : ↥(chartAlgFin A (↥K₁) j) →+* ↥W₀ :=
    ((chartAlgFin A (↥K₁) j).val.toRingHom).codRestrict W₀.toSubring (fun t => hSW₀ t)
  set 𝔓₀ : Ideal ↥(chartAlgFin A (↥K₁) j) := (IsLocalRing.maximalIdeal ↥W₀).comap φ with h𝔓₀
  have hmem𝔓₀ : ∀ t : ↥(chartAlgFin A (↥K₁) j), t ∈ 𝔓₀ ↔ (t : ↥K₁) ∈ W₀.nonunits := by
    intro t
    rw [h𝔓₀, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  haveI h𝔓₀p : 𝔓₀.IsPrime := Ideal.IsPrime.comap φ
  have hϖ𝔓₀ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ 𝔓₀ := by rw [hmem𝔓₀]; exact hAm ϖ hϖmax
  have h𝔓₀ne : 𝔓₀ ≠ ⊥ := by
    intro h
    rw [h] at hϖ𝔓₀
    have h0 := (Ideal.mem_bot).mp hϖ𝔓₀
    apply hϖK0
    have := congrArg (fun x : ↥(chartAlgFin A (↥K₁) j) => (x : ↥K₁)) h0
    simpa using this

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₁ A j hj
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K₁)) ↥K₁ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M) (by simp [ModularGroup.T]) L K₁ hK₁ j hj
  haveI hAlg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K₁)) ↥K₁ := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K₁)) ↥K₁ := inferInstance
  have hfin := (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K₁) j htj hFD hsep).1
  letI algP : Algebra (Polynomial A) ↥(chartAlgFin A (↥K₁) j) := (polynomialToChartFin A (↥K₁) j).toRingHom.toAlgebra
  haveI hfinI : Module.Finite (Polynomial A) ↥(chartAlgFin A (↥K₁) j) := hfin
  haveI : IsScalarTower A (Polynomial A) ↥(chartAlgFin A (↥K₁) j) := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A _ a = polynomialToChartFin A (↥K₁) j (algebraMap A (Polynomial A) a)
    exact (AlgHom.commutes (polynomialToChartFin A (↥K₁) j) a).symm
  haveI : Algebra.IsIntegral (Polynomial A) ↥(chartAlgFin A (↥K₁) j) := Algebra.IsIntegral.of_finite _ _
  have hco : ∀ R : Polynomial A, ((algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₁) j) R :
      ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) = Polynomial.aeval j R := fun R => by
    show ((polynomialToChartFin A (↥K₁) j R : ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) = _
    rw [polynomialToChartFin, ← coe_jChartFin A (↥K₁) j]
    exact (Polynomial.aeval_algHom_apply (chartAlgFin A (↥K₁) j).val (jChartFin A (↥K₁) j) R).symm

  haveI : Algebra.FiniteType A ↥(chartAlgFin A (↥K₁) j) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A (Polynomial A))
      (Module.Finite.finiteType (R := Polynomial A) ↥(chartAlgFin A (↥K₁) j))
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K₁) j) := Algebra.FiniteType.isNoetherianRing A _
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₁) j) := isIntegrallyClosed_chartAlg A (↥K₁) ({j} : Set ↥K₁)
  haveI : IsFractionRing ↥(chartAlgFin A (↥K₁) j) ↥K₁ := isFractionRing_chartAlg A L (↥K₁) ({j} : Set ↥K₁)

  have h𝔓₀nm : ¬ 𝔓₀.IsMaximal := by
    intro hmax
    set 𝔫 : Ideal (Polynomial A) := 𝔓₀.under (Polynomial A) with h𝔫
    haveI : 𝔫.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔓₀
    set P₀ : Ideal (Polynomial A) := (IsLocalRing.maximalIdeal A).map Polynomial.C with hP₀
    haveI hP₀p : P₀.IsPrime := Ideal.isPrime_map_C_of_isPrime
    have h𝔫le : 𝔫 ≤ P₀ := by
      intro P hP
      have hP' : (Polynomial.aeval j P : ↥K₁) ∈ W₀.nonunits := by
        rw [← hco, ← hmem𝔓₀]; exact hP
      by_cases hred : P.map (IsLocalRing.residue A) = 0
      · rw [hP₀, Ideal.mem_map_C_iff]
        intro n
        have := congrArg (fun Q => Polynomial.coeff Q n) hred
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
        exact (IsLocalRing.residue_eq_zero_iff _).mp this
      · exfalso
        obtain ⟨-, hinv⟩ := hWj P hred
        have hP0 : Polynomial.aeval j P ≠ 0 := by
          intro h0
          apply hred
          rw [(transcendental_iff.mp htj) P h0, Polynomial.map_zero]
        rcases (ValuationSubring.mem_nonunits_iff_or W₀).mp hP' with h0 | hninv
        · exact hP0 h0
        · exact hninv hinv
    have h𝔫eq : 𝔫 = P₀ := (Ideal.IsMaximal.eq_of_le inferInstance hP₀p.ne_top h𝔫le)
    have hF : IsField (Polynomial A ⧸ P₀) := by
      rw [← h𝔫eq]; exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔫).mp inferInstance
    exact Polynomial.not_isField _
      (MulEquiv.isField hF (Ideal.polynomialQuotientEquivQuotientPolynomial (IsLocalRing.maximalIdeal A)).toMulEquiv)
  obtain ⟨m, hm, h𝔓₀m⟩ := Ideal.exists_le_maximal 𝔓₀ h𝔓₀p.ne_top
  have hltm : 𝔓₀ < m := lt_of_le_of_ne h𝔓₀m (fun h => h𝔓₀nm (h ▸ hm))

  have hht : 𝔓₀.height = 1 := by
    apply le_antisymm
    · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
      intro q hq hqlt
      haveI := hq
      by_cases hq0 : q = ⊥
      · subst hq0; rw [Ideal.height_bot]; exact zero_lt_one
      · exact (CruxC.false_of_chain (R := Polynomial A) (CruxC.ringKrullDim_polynomial_le A)
          (m := m) hq0 hqlt hltm).elim
    · have h := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr h𝔓₀ne)
      rw [Ideal.height_bot, zero_add] at h
      exact h

  obtain ⟨V, hVmem, hCV, hVnu, -, -⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
      (C := ↥(chartAlgFin A (↥K₁) j)) (K := ↥K₁) 𝔓₀ hht
  have halg : ∀ c : ↥(chartAlgFin A (↥K₁) j), algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁ c = (c : ↥K₁) := fun c => rfl
  have hVle : V ≤ W₀ := by
    intro x hx
    obtain ⟨c, s, hs, hxs⟩ := (hVmem x).mp hx
    rw [halg, halg] at hxs
    have hsu : (s : ↥K₁) ∉ W₀.nonunits := by rw [← hmem𝔓₀]; exact hs
    have hs0 : (s : ↥K₁) ≠ 0 := fun h => hsu (by rw [h]; exact (ValuationSubring.mem_nonunits_iff_or W₀).mpr (Or.inl rfl))
    have hsinv : ((s : ↥K₁))⁻¹ ∈ W₀ := by
      rcases (ValuationSubring.mem_nonunits_iff_or W₀).not.mp hsu |> not_or.mp with ⟨-, h⟩
      exact not_not.mp h
    have : x = (c : ↥K₁) * ((s : ↥K₁))⁻¹ := by rw [← hxs, mul_inv_cancel_right₀ hs0]
    rw [this]
    exact W₀.mul_mem _ _ (hSW₀ c) hsinv

  letI algV : Algebra ↥(chartAlgFin A (↥K₁) j) ↥V :=
    (((chartAlgFin A (↥K₁) j).val.toRingHom).codRestrict V.toSubring (fun t => hCV t)).toAlgebra
  have halgV : ∀ c : ↥(chartAlgFin A (↥K₁) j), ((algebraMap ↥(chartAlgFin A (↥K₁) j) ↥V c : ↥V) : ↥K₁) = (c : ↥K₁) :=
    fun c => rfl
  haveI : IsLocalization.AtPrime (↥V) 𝔓₀ :=
    { map_units := by
        rintro ⟨s, hs⟩
        have hs' : (s : ↥K₁) ∉ V.nonunits := by rw [← halg, hVnu]; exact hs
        rw [ValuationSubring.valuation_eq_one_iff]
        have h1 := V.valuation_le_one (algebraMap ↥(chartAlgFin A (↥K₁) j) ↥V s)
        rcases h1.lt_or_eq with hlt | heq
        · exact absurd (V.mem_nonunits_iff.mpr hlt) hs'
        · exact heq
      surj := by
        intro z
        obtain ⟨c, s, hs, hzs⟩ := (hVmem (z : ↥K₁)).mp z.2
        refine ⟨(c, ⟨s, hs⟩), Subtype.ext ?_⟩
        simpa [halgV] using hzs
      exists_of_eq := by
        intro x y hxy
        refine ⟨1, ?_⟩
        have := congrArg (fun v : ↥V => (v : ↥K₁)) hxy
        simp only [halgV] at this
        simpa using Subtype.ext this }
  haveI : Ring.KrullDimLE 1 ↥V := by
    rw [Ring.krullDimLE_iff]
    have e := (IsLocalization.algEquiv 𝔓₀.primeCompl (Localization.AtPrime 𝔓₀) ↥V).toRingEquiv
    rw [← ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height 𝔓₀ (Localization.AtPrime 𝔓₀), hht]
    rfl

  have hVW : V = W₀ := ValuationSubring.eq_of_le_of_ne_top V hVle hW₀top
  have h2 : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ c s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∉ W₀.nonunits ∧ f * (s : ↥K₁) = (c : ↥K₁) := by
    intro f
    rw [← hVW, hVmem f]
    constructor
    · rintro ⟨c, s, hs, h⟩; exact ⟨c, s, by rw [hVW, ← hmem𝔓₀]; exact hs, h⟩
    · rintro ⟨c, s, hs, h⟩; exact ⟨c, s, by rw [hmem𝔓₀, ← hVW]; exact hs, h⟩
  refine ⟨?_, h2⟩
  intro e
  obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective e
  obtain ⟨c, s, hs, hws⟩ := (h2 (w : ↥K₁)).mp w.2
  refine ⟨c, s, hs, ?_⟩
  rw [← map_mul]
  congr 1
  exact Subtype.ext hws

end S_ModularCurve_XOne_forall_exists_mul_residue_eq_and_mem_iff_exists_mul_eq_gaussValuationSubring_chartAlgFin_x1
end P2MW
export P2MW.S_ModularCurve_XOne_forall_exists_mul_residue_eq_and_mem_iff_exists_mul_eq_gaussValuationSubring_chartAlgFin_x1 (solution)
