-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_end_blowupChart_on_component_of_isPrime_lt_supersingular_of_drinfeldChartWitness_linked_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/48101735-c70c-55b3-ad6b-3ce0b86703a4

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
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isPrime_forall_mem_iff_germ_mem_comap_of_le_of_ne_of_drinfeldChartWitness_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense_of_dvd
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_end_blowupChart_on_component_of_isPrime_lt_supersingular_of_drinfeldChartWitness_linked_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace PenOffendT4

theorem mem_maximalIdeal_iff {K : Type} [Field K] (V : ValuationSubring K) (x : K) (hx : x ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ IsLocalRing.maximalIdeal ↥V ↔ x = 0 ∨ x⁻¹ ∉ V :=
  (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨x, hx⟩)).symm.trans V.mem_nonunits_iff_or

theorem exists_composite {K : Type} [Field K] (V₁ : ValuationSubring K)
    (D : ValuationSubring (IsLocalRing.ResidueField ↥V₁)) :
    ∃ V₂ : ValuationSubring K, ∀ x : K, x ∈ V₂ ↔ ∃ hx : x ∈ V₁, IsLocalRing.residue ↥V₁ ⟨x, hx⟩ ∈ D := by
  classical
  let PV : K → Prop := fun x => ∃ hx : x ∈ V₁, IsLocalRing.residue ↥V₁ ⟨x, hx⟩ ∈ D

  have hnu : ∀ x : K, x ∈ V₁ → x⁻¹ ∉ V₁ → PV x := by
    intro x hx hxi
    refine ⟨hx, ?_⟩
    have hm : (⟨x, hx⟩ : ↥V₁) ∈ IsLocalRing.maximalIdeal ↥V₁ :=
      (mem_maximalIdeal_iff V₁ x hx).mpr (Or.inr hxi)
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr hm]
    exact D.zero_mem

  have hun : ∀ x : K, x ∈ V₁ → x⁻¹ ∈ V₁ → PV x ∨ PV x⁻¹ := by
    intro x hx hxi
    by_cases hx0 : x = 0
    · left
      refine ⟨hx, ?_⟩
      have : (⟨x, hx⟩ : ↥V₁) = 0 := Subtype.ext hx0
      rw [this, map_zero]; exact D.zero_mem
    have hprod : IsLocalRing.residue ↥V₁ ⟨x, hx⟩ * IsLocalRing.residue ↥V₁ ⟨x⁻¹, hxi⟩ = 1 := by
      rw [← map_mul, ← map_one (IsLocalRing.residue ↥V₁)]
      congr 1
      exact Subtype.ext (mul_inv_cancel₀ hx0)
    rcases D.mem_or_inv_mem (IsLocalRing.residue ↥V₁ ⟨x, hx⟩) with hD | hD
    · exact Or.inl ⟨hx, hD⟩
    · right
      refine ⟨hxi, ?_⟩
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact hD
  refine ⟨{ carrier := {x | PV x}
            mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_
            mem_or_inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro a b ⟨ha, haD⟩ ⟨hb, hbD⟩
    refine ⟨V₁.mul_mem _ _ ha hb, ?_⟩
    have : (⟨a * b, V₁.mul_mem _ _ ha hb⟩ : ↥V₁) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]; exact D.mul_mem _ _ haD hbD
  · refine ⟨V₁.one_mem, ?_⟩
    have : (⟨1, V₁.one_mem⟩ : ↥V₁) = 1 := rfl
    rw [this, map_one]; exact D.one_mem
  · rintro a b ⟨ha, haD⟩ ⟨hb, hbD⟩
    refine ⟨V₁.add_mem _ _ ha hb, ?_⟩
    have : (⟨a + b, V₁.add_mem _ _ ha hb⟩ : ↥V₁) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [this, map_add]; exact D.add_mem _ _ haD hbD
  · refine ⟨V₁.zero_mem, ?_⟩
    have : (⟨0, V₁.zero_mem⟩ : ↥V₁) = 0 := rfl
    rw [this, map_zero]; exact D.zero_mem
  · rintro a ⟨ha, haD⟩
    refine ⟨V₁.neg_mem _ ha, ?_⟩
    have : (⟨-a, V₁.neg_mem _ ha⟩ : ↥V₁) = -⟨a, ha⟩ := rfl
    rw [this, map_neg]; exact D.neg_mem _ haD
  · intro x
    show PV x ∨ PV x⁻¹
    rcases V₁.mem_or_inv_mem x with hx | hxi
    · by_cases hxi : x⁻¹ ∈ V₁
      · exact hun x hx hxi
      · exact Or.inl (hnu x hx hxi)
    · by_cases hx : x ∈ V₁
      · exact hun x hx hxi
      · exact Or.inr (hnu x⁻¹ hxi (by rwa [inv_inv]))

theorem exists_min_gen {K : Type} [Field K] (V : ValuationSubring K) (t : Finset K)
    (h : ∃ x ∈ t, x ≠ 0) : ∃ a ∈ t, a ≠ 0 ∧ ∀ x ∈ t, x * a⁻¹ ∈ V := by
  classical
  induction t using Finset.induction_on with
  | empty => obtain ⟨x, hx, -⟩ := h; simp at hx
  | insert b t hbt ih =>
    by_cases ht : ∃ x ∈ t, x ≠ 0
    · obtain ⟨a, hat, ha0, hall⟩ := ih ht
      by_cases hba : b * a⁻¹ ∈ V
      · refine ⟨a, Finset.mem_insert_of_mem hat, ha0, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hba
        · exact hall x hx
      · have hab : a * b⁻¹ ∈ V := by
          rcases V.mem_or_inv_mem (b * a⁻¹) with h1 | h1
          · exact absurd h1 hba
          · rwa [mul_inv_rev, inv_inv] at h1
        have hb0 : b ≠ 0 := by
          rintro rfl; apply hba; rw [zero_mul]; exact V.zero_mem
        refine ⟨b, Finset.mem_insert_self b t, hb0, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rw [mul_inv_cancel₀ hb0]; exact V.one_mem
        · have : x * b⁻¹ = (x * a⁻¹) * (a * b⁻¹) := by
            rw [mul_assoc, ← mul_assoc a⁻¹, inv_mul_cancel₀ ha0, one_mul]
          rw [this]; exact V.mul_mem _ _ (hall x hx) hab
    · push_neg at ht
      obtain ⟨x, hx, hx0⟩ := h
      have hxb : x = b := by
        rcases Finset.mem_insert.mp hx with h1 | h1
        · exact h1
        · exact absurd (ht x h1) hx0
      subst hxb
      refine ⟨x, Finset.mem_insert_self x t, hx0, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rw [mul_inv_cancel₀ hx0]; exact V.one_mem
      · rw [ht z hz, zero_mul]; exact V.zero_mem

theorem exists_locSubring {A K : Type} [CommRing A] [Field K] [Algebra A K]
    (Ba : Subalgebra A K) (P : Ideal ↥Ba) (hPp : P.IsPrime) :
    ∃ O : Subring K, ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K) := by
  classical
  refine ⟨{ carrier := {f : K | ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K)}
            mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun f => Iff.rfl⟩
  · rintro f f' ⟨g, h, hh, hfh⟩ ⟨g', h', hh', hfh'⟩
    refine ⟨g * g', h * h', fun hm => (hPp.mem_or_mem hm).elim hh hh', ?_⟩
    push_cast
    calc f * f' * ((h : K) * (h' : K)) = (f * (h : K)) * (f' * (h' : K)) := by ring
      _ = (g : K) * (g' : K) := by rw [hfh, hfh']
  · exact ⟨1, 1, fun h1 => hPp.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩
  · rintro f f' ⟨g, h, hh, hfh⟩ ⟨g', h', hh', hfh'⟩
    refine ⟨g * h' + g' * h, h * h', fun hm => (hPp.mem_or_mem hm).elim hh hh', ?_⟩
    push_cast
    calc (f + f') * ((h : K) * (h' : K)) = (f * (h : K)) * (h' : K) + (f' * (h' : K)) * (h : K) := by ring
      _ = (g : K) * (h' : K) + (g' : K) * (h : K) := by rw [hfh, hfh']
  · exact ⟨0, 1, fun h1 => hPp.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩
  · rintro f ⟨g, h, hh, hfh⟩
    exact ⟨-g, h, hh, by push_cast; rw [neg_mul, hfh]⟩

end PenOffendT4

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
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
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
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
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

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

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
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
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
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
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

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

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
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
          (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
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
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))
    :
      (∀ 𝔭 : Ideal ↥(chartAlgFin A (↥K) j), (𝔭.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭 ∧ 𝔭 ≤ y ∧ 𝔭 ≠ y) →
        ∃ O : Subring ↥K, (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O)) ∧ (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O) ∈ 𝔮))) := by
  classical
  intro 𝔭 h𝔭all
  obtain ⟨h𝔭, hϖ𝔭, h𝔭y, h𝔭ne⟩ := h𝔭all
  haveI h𝔭I : 𝔭.IsPrime := h𝔭
  haveI hyI : y.IsPrime := hy.isPrime

  let STK : Type := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
  let CMP : Type := (AdicCompletion (IsLocalRing.maximalIdeal STK) STK)
  let S : Type := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
  let mkS : MvPowerSeries (Fin 2) W₁ →+* S := (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}))
  let toC : STK →+* CMP := algebraMap _ _
  let germY : ↥(chartAlgFin A (↥K) j) →+* STK := (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom))
  let Ψ : ↥(chartAlgFin A (↥K) j) →+* S := ((e₁ : CMP →+* S).comp (toC.comp germY))

  obtain ⟨PS, hPSp, hPSne, hPSϖ, hPSiff⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.exists_isPrime_forall_mem_iff_germ_mem_comap_of_le_of_ne_of_drinfeldChartWitness_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ 𝔭 h𝔭 hϖ𝔭 h𝔭y h𝔭ne
  obtain ⟨hK1i, -, -⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  have hK2 := ModularCurve.FullLevel.AuxLevelOne.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁.1
  obtain ⟨hcen, hdense, -, hres, -, -, hSmax1, hSmax2, -⟩ := hK2
  have hK3 := ModularCurve.FullLevel.AuxLevelOne.map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense_of_dvd
    q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ hK1i hcen hdense hres ⟨hSmax1, hSmax2⟩
  obtain ⟨hmapJ, -, hJy, hϖtJ⟩ := hK3

  have hALK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hq21 : q ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith [(Fact.out : q.Prime).two_le]
    omega
  obtain ⟨ut, hut, hϖtq⟩ := id hϖt
  have hq0 : (q : A) ≠ 0 := by
    intro h
    have h1 : ((q : ℕ) : L) = 0 := by
      have := congrArg (algebraMap A L) h
      rwa [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h1
  have hϖt0 : ϖt ≠ 0 := by
    intro h
    apply hq0
    have h1 : ϖt ^ (q ^ 2 - 1) = 0 := by rw [h]; exact zero_pow hq21
    rw [hϖtq] at h1
    exact (hut.mul_left_eq_zero).mp h1
  have hϖtK0 : algebraMap A ↥K ϖt ≠ 0 := fun h => hϖt0 (hALK (by rw [h, map_zero]))
  have hCBa0 : ∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) = 0 → c = 0 := fun c h => by exact_mod_cast h

  have hϖt𝔭 : algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ 𝔭 := by
    have hqA : (q : A) ∈ maximalIdeal A := hAq
    rw [hϖ, Ideal.mem_span_singleton'] at hqA
    obtain ⟨cq, hcq⟩ := hqA
    have : algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ^ (q ^ 2 - 1) ∈ 𝔭 := by
      rw [← map_pow, hϖtq, ← hcq, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hϖ𝔭)
    exact h𝔭.mem_of_pow_mem _ this

  obtain ⟨b, hby, hb𝔭⟩ : ∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ b ∉ 𝔭 := by
    by_contra hcon
    push_neg at hcon
    exact h𝔭ne (le_antisymm h𝔭y fun b hb => hcon b hb)

  obtain ⟨i₀, hi₀J, hi₀𝔭⟩ : ∃ i₀ : ↥(chartAlgFin A (↥K) j), i₀ ∈ J ∧ i₀ ∉ 𝔭 := by
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.map Ψ J ≤ PS := by
      rw [Ideal.map_le_iff_le_comap]
      intro c hc
      have := (hPSiff c).1 (hcon c hc)
      rw [Ideal.mem_comap] at this
      rw [Ideal.mem_comap]
      exact this
    have hX0 : mkS (MvPowerSeries.X 0) ∈ PS := hle (hmapJ ▸ Ideal.subset_span (by right; left; rfl))
    have hX1 : mkS (MvPowerSeries.X 1) ∈ PS := hle (hmapJ ▸ Ideal.subset_span (by right; right; rfl))
    rcases hPSne with h0 | h1
    · exact h0 hX0
    · exact h1 hX1

  obtain ⟨htj, hFD, hsepK⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
      (q ^ 2 * M') H₁ L K hK A j hj
  have hft : Algebra.FiniteType A ↥(chartAlgFin A (↥K) j) :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsepK).1
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K) j) := by
    haveI := hft
    exact Algebra.FiniteType.isNoetherianRing A ↥(chartAlgFin A (↥K) j)
  obtain ⟨sJ, hsJ⟩ := (IsNoetherian.noetherian J : J.FG)

  obtain ⟨V₁, hVC₁, hcen₁⟩ : ∃ V₁ : ValuationSubring ↥K,
      (∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ V₁) ∧
      (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ V₁), (⟨_, hc⟩ : ↥V₁) ∈ maximalIdeal ↥V₁ ↔ c ∈ 𝔭) := by
    have hunit : ∀ s : 𝔭.primeCompl, IsUnit (algebraMap ↥(chartAlgFin A (↥K) j) ↥K s) := by
      intro s
      apply isUnit_iff_ne_zero.mpr
      intro h0
      apply s.2
      have h0' : (((s : ↥(chartAlgFin A (↥K) j)) : ↥K)) = 0 := h0
      have hs0 : (s : ↥(chartAlgFin A (↥K) j)) = 0 := by exact_mod_cast h0'
      rw [hs0]; exact Submodule.zero_mem _
    let f : Localization.AtPrime 𝔭 →+* ↥K := IsLocalization.lift (M := 𝔭.primeCompl) hunit
    have hfC : ∀ c : ↥(chartAlgFin A (↥K) j), f (algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime 𝔭) c) = (c : ↥K) :=
      fun c => IsLocalization.lift_eq hunit c
    obtain ⟨V, hfV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
    have hVC : ∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ V := by
      intro c
      have := hfV (algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime 𝔭) c)
      rw [hfC] at this
      exact this
    refine ⟨V, hVC, ?_⟩
    intro c hc
    have hgc : (f.codRestrict V.toSubring hfV (algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime 𝔭) c) : ↥V.toSubring) =
        ⟨_, hc⟩ := Subtype.ext (hfC c)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hnu
      by_contra hc𝔭
      apply hnu
      have hu : IsUnit (algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime 𝔭) c) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 c).mpr hc𝔭
      have hu' := hu.map (f.codRestrict V.toSubring hfV)
      rw [hgc] at hu'
      exact hu'
    · intro hc𝔭 hu
      have hc' : c ∉ 𝔭.primeCompl := fun h => h hc𝔭
      apply hc'
      apply (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 c).mp
      haveI := hloc
      apply (isUnit_map_iff (f.codRestrict V.toSubring hfV) _).mp
      rw [hgc]
      exact hu
  have hϖtV₁ : (⟨algebraMap A ↥K ϖt, hVC₁ (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt)⟩ : ↥V₁) ∈ maximalIdeal ↥V₁ :=
    (hcen₁ (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) _).mpr hϖt𝔭

  let ιC₁ : ↥(chartAlgFin A (↥K) j) →+* ↥V₁ :=
    { toFun := fun c => ⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hVC₁ c⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  let ψ : ↥(chartAlgFin A (↥K) j) →+* ResidueField ↥V₁ := (IsLocalRing.residue ↥V₁).comp ιC₁
  have hψ : ∀ c : ↥(chartAlgFin A (↥K) j), ψ c = IsLocalRing.residue ↥V₁ ⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hVC₁ c⟩ := fun c => rfl
  have hunit₂ : ∀ s : y.primeCompl, IsUnit (ψ s) := by
    intro s
    apply isUnit_iff_ne_zero.mpr
    intro h0
    rw [hψ, IsLocalRing.residue_eq_zero_iff] at h0
    exact s.2 (h𝔭y ((hcen₁ _ _).mp h0))
  let f₂ : Localization.AtPrime y →+* ResidueField ↥V₁ := IsLocalization.lift (M := y.primeCompl) hunit₂
  have hf₂C : ∀ c : ↥(chartAlgFin A (↥K) j), f₂ (algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime y) c) = ψ c :=
    fun c => IsLocalization.lift_eq hunit₂ c
  obtain ⟨D, hfD, hlocD⟩ := IsLocalRing.exists_factor_valuationRing f₂
  have hψD : ∀ c : ↥(chartAlgFin A (↥K) j), ψ c ∈ D := by
    intro c
    have := hfD (algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime y) c)
    rw [hf₂C] at this
    exact this
  have hcenD : ∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ψ c ∈ D), (⟨ψ c, hc⟩ : ↥D) ∈ maximalIdeal ↥D ↔ c ∈ y := by
    intro c hc
    have hgc : (f₂.codRestrict D.toSubring hfD (algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime y) c) : ↥D.toSubring) =
        ⟨_, hc⟩ := Subtype.ext (hf₂C c)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hnu
      by_contra hcy
      apply hnu
      have hu : IsUnit (algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime y) c) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime y) y c).mpr hcy
      have hu' := hu.map (f₂.codRestrict D.toSubring hfD)
      rw [hgc] at hu'
      exact hu'
    · intro hcy hu
      have hc' : c ∉ y.primeCompl := fun h => h hcy
      apply hc'
      apply (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime y) y c).mp
      haveI := hlocD
      apply (isUnit_map_iff (f₂.codRestrict D.toSubring hfD) _).mp
      rw [hgc]
      exact hu

  obtain ⟨V₂, hV₂⟩ := PenOffendT4.exists_composite V₁ D
  have hV₂₁ : ∀ x : ↥K, x ∈ V₂ → x ∈ V₁ := fun x hx => ((hV₂ x).mp hx).1
  have hVC₂ : ∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ V₂ := fun c => (hV₂ _).mpr ⟨hVC₁ c, hψD c⟩
  have hyV₂ : ∀ c : ↥(chartAlgFin A (↥K) j), c ∈ y → ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 → (((c : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∉ V₂ := by
    intro c hcy hc0 hinv
    obtain ⟨hinv₁, hinvD⟩ := (hV₂ _).mp hinv
    by_cases hc𝔭 : c ∈ 𝔭
    · have hm := (hcen₁ c (hVC₁ c)).mpr hc𝔭
      rcases (PenOffendT4.mem_maximalIdeal_iff V₁ _ (hVC₁ c)).mp hm with h0 | hni
      · exact hc0 h0
      · exact hni hinv₁
    · have hcD : (⟨ψ c, hψD c⟩ : ↥D) ∈ maximalIdeal ↥D := (hcenD c (hψD c)).mpr hcy
      rcases (PenOffendT4.mem_maximalIdeal_iff D (ψ c) (hψD c)).mp hcD with h0 | hni
      · rw [hψ, IsLocalRing.residue_eq_zero_iff] at h0
        exact hc𝔭 ((hcen₁ _ _).mp h0)
      · apply hni
        have hprod : IsLocalRing.residue ↥V₁ ⟨_, hVC₁ c⟩ * IsLocalRing.residue ↥V₁ ⟨_, hinv₁⟩ = 1 := by
          rw [← map_mul, ← map_one (IsLocalRing.residue ↥V₁)]
          congr 1
          exact Subtype.ext (mul_inv_cancel₀ hc0)
        rw [hψ, ← eq_inv_of_mul_eq_one_right hprod]
        exact hinvD

  obtain ⟨aK, haKt, haK0, hmin⟩ := PenOffendT4.exists_min_gen V₂
    (insert (algebraMap A ↥K ϖt) (sJ.image fun c : ↥(chartAlgFin A (↥K) j) => ((c : ↥(chartAlgFin A (↥K) j)) : ↥K)))
    ⟨algebraMap A ↥K ϖt, Finset.mem_insert_self _ _, hϖtK0⟩
  obtain ⟨a, haJ, haK⟩ : ∃ a : ↥(chartAlgFin A (↥K) j), a ∈ J ∧ ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = aK := by
    rcases Finset.mem_insert.mp haKt with h | h
    · exact ⟨algebraMap A ↥(chartAlgFin A (↥K) j) ϖt, hϖtJ, h.symm⟩
    · obtain ⟨c, hc, hcK⟩ := Finset.mem_image.mp h
      refine ⟨c, ?_, hcK⟩
      rw [← hsJ]; exact Submodule.subset_span hc
  have ha0 : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 := by rw [haK]; exact haK0
  have hJa : ∀ i : ↥(chartAlgFin A (↥K) j), i ∈ J → ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK⁻¹ ∈ V₂ := by
    intro i hi
    rw [← hsJ] at hi
    induction hi using Submodule.span_induction with
    | mem x hx =>
      exact hmin _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))
    | zero => simp only [ZeroMemClass.coe_zero, zero_mul]; exact V₂.zero_mem
    | add x x' _ _ hx hx' =>
      simp only [Subalgebra.coe_add, add_mul]
      exact V₂.add_mem _ _ hx hx'
    | smul c x _ hx =>
      have : (((c • x : ↥(chartAlgFin A (↥K) j)) : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK⁻¹ = ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) * ((((x : ↥(chartAlgFin A (↥K) j)) : ↥K)) * aK⁻¹) := by
        rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]
      rw [this]
      exact V₂.mul_mem _ _ (hVC₂ c) hx
  set Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A with hBa
  have hCBa : ∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba := by
    intro c
    rw [hBa, Subalgebra.mem_restrictScalars]
    exact Subalgebra.algebraMap_mem _ c
  have hBaV₂ : ∀ x : ↥K, x ∈ Ba → x ∈ V₂ := by
    intro x hx
    rw [hBa, Subalgebra.mem_restrictScalars] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi, hxi⟩ := hx
      have : x = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK⁻¹ := by
        rw [← hxi, ← haK, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
      rw [this]; exact hJa i hi
    | algebraMap c => exact hVC₂ c
    | add x x' _ _ hx hx' => exact V₂.add_mem _ _ hx hx'
    | mul x x' _ _ hx hx' => exact V₂.mul_mem _ _ hx hx'

  let ιBa : ↥Ba →+* ↥V₂ :=
    { toFun := fun r => ⟨(r : ↥K), hBaV₂ r r.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun r s => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun r s => Subtype.ext rfl }
  have hιBa : ∀ r : ↥Ba, ιBa r = ⟨(r : ↥K), hBaV₂ r r.2⟩ := fun r => rfl
  haveI : (maximalIdeal ↥V₂).IsPrime := (maximalIdeal.isMaximal ↥V₂).isPrime
  set P : Ideal ↥Ba := Ideal.comap ιBa (maximalIdeal ↥V₂) with hPdef
  have hPne : P ≠ ⊤ := Ideal.comap_ne_top ιBa (maximalIdeal.isMaximal ↥V₂).ne_top
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hPne
  obtain ⟨O, hOmem⟩ := PenOffendT4.exists_locSubring Ba M hM.isPrime
  have h1M : (1 : ↥Ba) ∉ M := (Ideal.ne_top_iff_one M).mp hM.ne_top
  have hBaO : ∀ r : ↥Ba, (r : ↥K) ∈ O := fun r => (hOmem _).mpr ⟨r, 1, h1M, by simp⟩
  have hCO : ∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O := fun c => hBaO ⟨_, hCBa c⟩

  have hOV₂ : ∀ x : ↥K, x ∈ O → x ∈ V₂ := by
    intro x hx
    obtain ⟨g, h, hhM, hxh⟩ := (hOmem x).mp hx
    have hhP : h ∉ P := fun hh => hhM (hPM hh)
    have hhm : (⟨(h : ↥K), hBaV₂ h h.2⟩ : ↥V₂) ∉ maximalIdeal ↥V₂ := by
      intro hm; apply hhP; rw [hPdef, Ideal.mem_comap, hιBa]; exact hm
    rw [PenOffendT4.mem_maximalIdeal_iff] at hhm
    push_neg at hhm
    obtain ⟨hh0, hhinv⟩ := hhm
    have : x = (g : ↥K) * ((h : ↥K))⁻¹ := by rw [← hxh, mul_assoc, mul_inv_cancel₀ hh0, mul_one]
    rw [this]
    exact V₂.mul_mem _ _ (hBaV₂ g g.2) hhinv
  have hOV₁ : ∀ x : ↥K, x ∈ O → x ∈ V₁ := fun x hx => hV₂₁ x (hOV₂ x hx)

  let ιO : ↥O →+* ↥V₁ :=
    { toFun := fun r => ⟨(r : ↥K), hOV₁ r r.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun r s => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun r s => Subtype.ext rfl }
  have hιO : ∀ r : ↥O, ιO r = ⟨(r : ↥K), hOV₁ r r.2⟩ := fun r => rfl
  haveI : (maximalIdeal ↥V₁).IsPrime := (maximalIdeal.isMaximal ↥V₁).isPrime
  refine ⟨O, ⟨a, haJ, ha0, M, hM, hOmem, ?_, ?_⟩, Ideal.comap ιO (maximalIdeal ↥V₁), Ideal.comap_isPrime ιO _, ?_, ⟨b, hby, ?_⟩, ?_⟩
  ·
    intro c hcy hcO hu
    obtain ⟨w, hw1⟩ := hu.exists_right_inv
    have e1 : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) * (w : ↥K) = 1 := by
      have := congrArg (fun t : ↥O => (t : ↥K)) hw1
      simpa using this
    have hc0 : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 := fun h0 => by rw [h0, zero_mul] at e1; exact zero_ne_one e1
    apply hyV₂ c hcy hc0
    rw [← eq_inv_of_mul_eq_one_right e1]
    exact hOV₂ _ w.2
  ·
    intro hBO
    have hxB : aK * (algebraMap A ↥K ϖt)⁻¹ ∈ B := by
      rw [hB, Subalgebra.mem_restrictScalars]
      exact Algebra.subset_adjoin ⟨a, haJ, by rw [mul_assoc, inv_mul_cancel₀ hϖtK0, mul_one, haK]⟩
    have h1 : aK * (algebraMap A ↥K ϖt)⁻¹ ∈ V₁ := hOV₁ _ (hBO _ hxB)
    have h2 : ((i₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK⁻¹ ∈ V₁ := hV₂₁ _ (hJa i₀ hi₀J)
    have h3 : ((i₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ ∈ V₁ := by
      have : ((i₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ = (((i₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK⁻¹) * (aK * (algebraMap A ↥K ϖt)⁻¹) := by
        rw [mul_assoc, ← mul_assoc aK⁻¹, inv_mul_cancel₀ haK0, one_mul]
      rw [this]; exact V₁.mul_mem _ _ h2 h1
    apply hi₀𝔭
    apply (hcen₁ i₀ (hVC₁ i₀)).mp
    have : (⟨((i₀ : ↥(chartAlgFin A (↥K) j)) : ↥K), hVC₁ i₀⟩ : ↥V₁) =
        ⟨_, h3⟩ * ⟨algebraMap A ↥K ϖt, hVC₁ (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt)⟩ := by
      apply Subtype.ext
      show ((i₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ * algebraMap A ↥K ϖt
      rw [mul_assoc, inv_mul_cancel₀ hϖtK0, mul_one]
    rw [this]
    exact Ideal.mul_mem_left _ _ hϖtV₁
  ·
    intro hϖO
    rw [Ideal.mem_comap, hιO]
    exact (hcen₁ (algebraMap A ↥(chartAlgFin A (↥K) j) ϖ) _).mpr hϖ𝔭
  ·
    intro hbO hb𝔮
    rw [Ideal.mem_comap, hιO] at hb𝔮
    exact hb𝔭 ((hcen₁ b _).mp hb𝔮)
  ·
    intro c hc
    rw [Ideal.mem_comap, hιO]
    exact (hcen₁ c _).symm

end S_ModularCurve_FullLevel_AuxLevelOne_exists_end_blowupChart_on_component_of_isPrime_lt_supersingular_of_drinfeldChartWitness_linked_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_end_blowupChart_on_component_of_isPrime_lt_supersingular_of_drinfeldChartWitness_linked_of_dvd (solution)
