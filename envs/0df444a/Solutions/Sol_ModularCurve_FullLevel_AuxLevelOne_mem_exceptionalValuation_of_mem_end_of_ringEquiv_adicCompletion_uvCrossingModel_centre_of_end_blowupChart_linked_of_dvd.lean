-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.mem_exceptionalValuation_of_mem_end_of_ringEquiv_adicCompletion_uvCrossingModel_centre_of_end_blowupChart_linked_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/605e2f70-39f5-58cf-8028-15fb18733f9c

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
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_mem_maximalIdeal_iff_mem_span_image_of_blowupChart_exceptionalValuation_of_isPrime_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness_of_dvd
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_mem_exceptionalValuation_of_mem_end_of_ringEquiv_adicCompletion_uvCrossingModel_centre_of_end_blowupChart_linked_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

open ModularCurve ModularCurve.FullLevel in

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

    (hjK : ModularCurve.jqNModC L q ∈ K)
    (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ chartAlgFin A (↥K) j)

    (m : ℕ) (hm1 : 1 ≤ m) (hmt : ∃ w : A, IsUnit w ∧ ϖ ^ m = ϖt * w)
    (O : Subring ↥K)

    (hO : ∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
      let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
      ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
        (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
        (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
          ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
        ¬ (∀ f : ↥K, f ∈ B → f ∈ O))

    (hOloc : IsLocalRing ↥O) (hOnoe : IsNoetherianRing ↥O)
    (hCO : ∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ O)
    (hOy : ∀ b : ↥(chartAlgFin A (↥K) j), (⟨(b : ↥K), hCO b⟩ : ↥O) ∈ maximalIdeal ↥O ↔ b ∈ y)

    (ι₁ : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel W₁ ((σ₁ ϖ) ^ m)))
    (hι₁c : ∀ (a : A) (ha : algebraMap A ↥K a ∈ O), ι₁ (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((σ₁ ϖ) ^ m) (σ₁ a))

    (a : ↥(chartAlgFin A (↥K) j)) (haJ : a ∈ J) (ha0 : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0) (c : ↥O)
    (γU γV : (UVCrossingModel W₁ ((σ₁ ϖ) ^ m))ˣ)
    (hJa : ∀ i : ↥(chartAlgFin A (↥K) j), i ∈ J → ∃ o : ↥K, o ∈ O ∧ ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * o)
    (hac : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * (c : ↥K) = algebraMap A ↥K ϖt)
    (hιa : ι₁ (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨((a : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO a⟩) = (γV : (UVCrossingModel W₁ ((σ₁ ϖ) ^ m))) * UVCrossingModel.V ((σ₁ ϖ) ^ m))
    (hιc : ι₁ (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) c) = (γU : (UVCrossingModel W₁ ((σ₁ ϖ) ^ m))) * UVCrossingModel.U ((σ₁ ϖ) ^ m))

    (hyB : (Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j)))).IsPrime) :
    ∀ f : ↥K, f ∈ O → f ∈ W := by
  classical
  intro f hfO

  have hR3' := hR3
  obtain ⟨hWL, hWϖ, hWdvr, hWy, hWloc⟩ := hR3'
  have hAKdef : ∀ x : A, algebraMap A ↥K x = algebraMap L ↥K (algebraMap A L x) :=
    fun x => IsScalarTower.algebraMap_apply A L ↥K x
  have hAKinj : Function.Injective (algebraMap A ↥K) := by
    intro x x' h
    rw [hAKdef, hAKdef] at h
    exact IsFractionRing.injective A L ((algebraMap L ↥K).injective h)
  have hq0 : (q : A) ≠ 0 := by
    intro h
    have h2 : algebraMap A L (q : A) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h2
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h2
  have hϖt0 : ϖt ≠ 0 := by
    obtain ⟨ut, hut, hϖtpow⟩ := hϖt
    intro h
    have hpos : q ^ 2 - 1 ≠ 0 := by
      have := (Fact.out : q.Prime).two_le
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    rw [h, zero_pow hpos] at hϖtpow
    exact hq0 ((hut.mul_left_eq_zero).mp hϖtpow.symm)
  have hϖ0 : ϖ ≠ 0 := by
    have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
    exact hirr.ne_zero
  have hϖtK0 : algebraMap A ↥K ϖt ≠ 0 := fun h => hϖt0 (hAKinj (by rw [h, map_zero]))
  have hϖK0 : algebraMap A ↥K ϖ ≠ 0 := fun h => hϖ0 (hAKinj (by rw [h, map_zero]))

  have hAO : ∀ x : A, algebraMap A ↥K x ∈ O := fun x => by
    have := hCO (algebraMap A ↥(chartAlgFin A (↥K) j) x)
    rwa [Subalgebra.coe_algebraMap] at this

  have unitK : ∀ {S : Type} [SetLike S ↥K] [SubringClass S ↥K] (V : S) (x : ↥K) (hx : x ∈ V),
      IsUnit (⟨x, hx⟩ : ↥V) ↔ x ≠ 0 ∧ x⁻¹ ∈ V := by
    intro S _ _ V x hx
    constructor
    · intro hu
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      have hw' : x * (w : ↥K) = 1 := by
        have := congrArg (fun z : ↥V => (z : ↥K)) hw
        simpa using this
      have hx0 : x ≠ 0 := fun h0 => by rw [h0, zero_mul] at hw'; exact zero_ne_one hw'
      refine ⟨hx0, ?_⟩
      have : (w : ↥K) = x⁻¹ := eq_inv_of_mul_eq_one_right hw'
      rw [← this]; exact w.2
    · rintro ⟨hx0, hinv⟩
      exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

  have hc0 : (c : ↥K) ≠ 0 := fun h => by apply hϖtK0; rw [← hac, h, mul_zero]
  have hx₀B : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ ∈ B := by
    rw [hB, Subalgebra.mem_restrictScalars]
    exact Algebra.subset_adjoin ⟨a, haJ, by rw [inv_mul_cancel_right₀ hϖtK0]⟩
  set x₀ : ↥B := ⟨_, hx₀B⟩ with hx₀def
  have hx₀c : ((x₀ : ↥B) : ↥K) * (c : ↥K) = 1 := by
    show ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ * (c : ↥K) = 1
    rw [mul_assoc, mul_comm _ (c : ↥K), ← mul_assoc, hac, mul_inv_cancel₀ hϖtK0]

  have hπirr : Irreducible (σ₁ ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer (σ₁ ϖ)).mpr hσ₁
  obtain ⟨D, _instD1, _instD2, _instD3, ψ, hψinj, hψU, hψV, hψmax, hψiff⟩ :=
    ModularCurve.UVCrossingModel.exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow W₁ (σ₁ ϖ) hπirr m hm1
  let toC : ↥O →+* AdicCompletion (maximalIdeal ↥O) ↥O := algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O)
  let sw : UVCrossingModel W₁ ((σ₁ ϖ) ^ m) ≃+* UVCrossingModel W₁ ((σ₁ ϖ) ^ m) := UVCrossingModel.crossingSwap ((σ₁ ϖ) ^ m)
  have hswU : sw (UVCrossingModel.U ((σ₁ ϖ) ^ m)) = UVCrossingModel.V ((σ₁ ϖ) ^ m) := by
    show UVCrossingModel.crossingSwap _ (UVCrossingModel.mk _ (MvPowerSeries.X 0)) = UVCrossingModel.mk _ (MvPowerSeries.X 1)
    rw [UVCrossingModel.crossingSwap_mk, uvSwapEquiv_X_zero]
  have hswV : sw (UVCrossingModel.V ((σ₁ ϖ) ^ m)) = UVCrossingModel.U ((σ₁ ϖ) ^ m) := by
    show UVCrossingModel.crossingSwap _ (UVCrossingModel.mk _ (MvPowerSeries.X 1)) = UVCrossingModel.mk _ (MvPowerSeries.X 0)
    rw [UVCrossingModel.crossingSwap_mk, uvSwapEquiv_X_one]
  have hswC : ∀ w : W₁, sw (UVCrossingModel.const ((σ₁ ϖ) ^ m) w) = UVCrossingModel.const ((σ₁ ϖ) ^ m) w := by
    intro w
    show UVCrossingModel.crossingSwap _ (UVCrossingModel.mk _ (MvPowerSeries.C w)) = UVCrossingModel.mk _ (MvPowerSeries.C w)
    rw [UVCrossingModel.crossingSwap_mk, uvSwapEquiv_C]
  let β : ↥O →+* D := ψ.comp (sw.toRingHom.comp (ι₁.toRingHom.comp toC))
  have hβ : ∀ o : ↥O, β o = ψ (sw (ι₁ (toC o))) := fun o => rfl
  haveI : (maximalIdeal D).IsPrime := (maximalIdeal.isMaximal D).isPrime
  let 𝔭 : Ideal ↥O := (maximalIdeal D).comap β
  have h𝔭p : 𝔭.IsPrime := Ideal.comap_isPrime β (maximalIdeal D)
  let aO : ↥O := ⟨((a : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO a⟩
  have ha𝔭 : aO ∈ 𝔭 := by
    show β aO ∈ maximalIdeal D
    rw [hβ]
    show ψ (sw (ι₁ (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨((a : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO a⟩))) ∈ maximalIdeal D
    rw [hιa, map_mul, hswV, map_mul]
    exact Ideal.mul_mem_left _ _ hψU
  have hc𝔭 : c ∉ 𝔭 := by
    intro h
    have h' : β c ∈ maximalIdeal D := h
    rw [hβ] at h'
    apply (IsLocalRing.mem_maximalIdeal _).mp h'
    show IsUnit (ψ (sw (ι₁ (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) c))))
    rw [hιc, map_mul, hswU, map_mul]
    exact (((Units.isUnit γU).map sw).map ψ).mul hψV
  have hϖ𝔭 : (⟨algebraMap A ↥K ϖ, hAO ϖ⟩ : ↥O) ∈ 𝔭 := by
    show β ⟨algebraMap A ↥K ϖ, hAO ϖ⟩ ∈ maximalIdeal D
    rw [hβ]
    show ψ (sw (ι₁ (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨algebraMap A ↥K ϖ, hAO ϖ⟩))) ∈ maximalIdeal D
    rw [hι₁c ϖ (hAO ϖ), hswC, hψmax]
    exact Ideal.mem_span_singleton_self _
  have h𝔭top : 𝔭 ≠ ⊤ := fun h => hc𝔭 (h.symm ▸ Submodule.mem_top)
  have h𝔭le : 𝔭 ≤ maximalIdeal ↥O := IsLocalRing.le_maximalIdeal h𝔭top

  have hcmax : c ∈ maximalIdeal ↥O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hcu
    have h1 : IsUnit (ι₁ (toC c)) := (hcu.map toC).map ι₁
    have h1' : IsUnit ((γU : UVCrossingModel W₁ ((σ₁ ϖ) ^ m)) * UVCrossingModel.U ((σ₁ ϖ) ^ m)) := by
      rw [← hιc]; exact h1
    have h2 : IsUnit (UVCrossingModel.U ((σ₁ ϖ) ^ m)) := isUnit_of_mul_isUnit_right h1'
    exact (IsLocalRing.mem_maximalIdeal _).mp hψU (h2.map ψ)

  haveI := h𝔭p
  obtain ⟨V₀, hV₀⟩ := (LocalSubring.ofPrime O 𝔭).exists_le_valuationSubring
  obtain ⟨hleV, hlocV⟩ := hV₀
  have hOV : ∀ x : ↥K, x ∈ O → x ∈ V₀ := fun x hx => hleV (LocalSubring.le_ofPrime O 𝔭 hx)
  have key𝔭 : ∀ (x : ↥K) (hx : x ∈ O), (⟨x, hx⟩ : ↥O) ∈ 𝔭 ↔ ¬ IsUnit (⟨x, hOV x hx⟩ : ↥V₀) := by
    intro x hx
    have h1 := IsLocalization.AtPrime.to_map_mem_maximal_iff ↥(LocalSubring.ofPrime O 𝔭).toSubring 𝔭 (⟨x, hx⟩ : ↥O)
    rw [← h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    refine not_congr ⟨fun hu => ?_, fun hu => ?_⟩
    · exact hu.map (Subring.inclusion hleV)
    · exact hlocV.map_nonunit _ hu

  let inclCO : ↥(chartAlgFin A (↥K) j) →+* ↥O :=
    { toFun := fun b => ⟨(b : ↥K), hCO b⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsup := ModularCurve.FullLevel.AuxLevelOne.exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness_of_dvd
    q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
    W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  obtain ⟨-, -, -, -, -, T, N, hN1, hyT, hTmax, hprod, -⟩ := hsup
  have hy𝔭 : ∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y → inclCO b ∈ 𝔭 := by
    let 𝔭C : Ideal ↥(chartAlgFin A (↥K) j) := 𝔭.comap inclCO
    have h𝔭Cp : 𝔭C.IsPrime := Ideal.comap_isPrime inclCO 𝔭
    have hJ𝔭 : J ≤ 𝔭C := by
      intro i hi
      obtain ⟨o, hoO, hio⟩ := hJa i hi
      show inclCO i ∈ 𝔭
      have : inclCO i = aO * ⟨o, hoO⟩ := Subtype.ext hio
      rw [this]; exact Ideal.mul_mem_right _ _ ha𝔭
    have h1 : ∏ P ∈ T, P ^ N ≤ 𝔭C := hprod.trans hJ𝔭
    obtain ⟨P, hPT, hPle⟩ := (Ideal.IsPrime.prod_le h𝔭Cp).mp h1
    haveI := h𝔭Cp
    have hPle' : P ≤ 𝔭C := Ideal.IsPrime.le_of_pow_le hPle
    have h𝔭Cy : 𝔭C ≤ y := fun b hb => (hOy b).mp (h𝔭le hb)
    have hPy : P = y := (hTmax P hPT).eq_of_le hy.ne_top (hPle'.trans h𝔭Cy)
    intro b hb
    have hbP : b ∈ P := by rw [hPy]; exact hb
    exact hPle' hbP

  have hcV : (c : ↥K) ∈ V₀ := hOV _ c.2
  have hcunitV : IsUnit (⟨(c : ↥K), hcV⟩ : ↥V₀) := by
    by_contra hu
    apply hc𝔭
    have := (key𝔭 (c : ↥K) c.2).mpr hu
    simpa using this
  have hcinvV : (c : ↥K)⁻¹ ∈ V₀ := ((unitK V₀ _ hcV).mp hcunitV).2
  have hBV : ∀ x : ↥K, x ∈ B → x ∈ V₀ := by
    intro x hx
    rw [hB, Subalgebra.mem_restrictScalars] at hx
    let VC : Subalgebra ↥(chartAlgFin A (↥K) j) ↥K :=
      { carrier := (V₀ : Set ↥K)
        mul_mem' := fun hs ht => mul_mem hs ht
        one_mem' := one_mem V₀
        add_mem' := fun hs ht => add_mem hs ht
        zero_mem' := zero_mem V₀
        algebraMap_mem' := fun b => hOV _ (hCO b) }
    have hle : Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} ≤ VC := by
      refine Algebra.adjoin_le ?_
      rintro t ⟨i, hi, hti⟩
      obtain ⟨o, hoO, hio⟩ := hJa i hi
      have h1 : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * (t * (c : ↥K)) = ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * o := by
        rw [← hio, ← hti, ← hac]; ring
      have h2 : t * (c : ↥K) = o := mul_left_cancel₀ ha0 h1
      have h3 : t = o * (c : ↥K)⁻¹ := (eq_mul_inv_iff_mul_eq₀ hc0).mpr h2
      show t ∈ V₀
      rw [h3]; exact mul_mem (hOV o hoO) hcinvV
    exact hle hx

  let inclBV : ↥B →+* ↥V₀ :=
    { toFun := fun b => ⟨(b : ↥K), hBV _ b.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let 𝔫 : Ideal ↥B := (maximalIdeal ↥V₀).comap inclBV
  haveI : (maximalIdeal ↥V₀).IsPrime := (maximalIdeal.isMaximal ↥V₀).isPrime
  have h𝔫p : 𝔫.IsPrime := Ideal.comap_isPrime inclBV (maximalIdeal ↥V₀)
  have h𝔫mem : ∀ b : ↥B, b ∈ 𝔫 ↔ ¬ IsUnit (⟨(b : ↥K), hBV _ b.2⟩ : ↥V₀) := by
    intro b
    show inclBV b ∈ maximalIdeal ↥V₀ ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Iff.rfl
  have eϖB : (⟨((algebraMap A ↥B ϖ : ↥B) : ↥K), hBV _ (algebraMap A ↥B ϖ).2⟩ : ↥V₀) = ⟨algebraMap A ↥K ϖ, hOV _ (hAO ϖ)⟩ :=
    Subtype.ext (by rw [Subalgebra.coe_algebraMap])
  have hϖ𝔫 : algebraMap A ↥B ϖ ∈ 𝔫 := by
    rw [h𝔫mem, eϖB]
    exact (key𝔭 _ (hAO ϖ)).mp hϖ𝔭
  have h𝔫C : ∀ b : ↥(chartAlgFin A (↥K) j), (⟨(b : ↥K), hR1.1 b.2⟩ : ↥B) ∈ 𝔫 ↔ b ∈ y := by
    intro b
    rw [h𝔫mem]
    constructor
    · intro hb
      have : (⟨(b : ↥K), hCO b⟩ : ↥O) ∈ 𝔭 := (key𝔭 _ (hCO b)).mpr hb
      exact (hOy b).mp (h𝔭le this)
    · intro hb
      exact (key𝔭 _ (hCO b)).mp (hy𝔭 b hb)
  obtain ⟨hLi, hLii⟩ := ModularCurve.FullLevel.AuxLevelOne.mem_maximalIdeal_iff_mem_span_image_of_blowupChart_exceptionalValuation_of_isPrime_of_dvd
    q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss J B hB W hBW hR1 hR2 hR3 hyB
  have h𝔴𝔫 : ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → b ∈ 𝔫 := hLii 𝔫 h𝔫p hϖ𝔫 h𝔫C

  suffices hn : ∀ b : ↥B, b ∈ 𝔫 → (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W by
    have hWV : ∀ x : ↥K, x ∈ W → x ∈ V₀ := by
      intro x hx
      obtain ⟨g, h, hh, hxh⟩ := (hWloc x).mp hx
      have hhV : IsUnit (⟨(h : ↥K), hBV _ h.2⟩ : ↥V₀) := by
        by_contra hu
        exact hh (hn h ((h𝔫mem h).mpr hu))
      obtain ⟨hh0, hhinv⟩ := (unitK V₀ _ (hBV _ h.2)).mp hhV
      have : x = (g : ↥K) * ((h : ↥K))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hh0).mpr hxh
      rw [this]; exact mul_mem (hBV _ g.2) hhinv

    have hϖVnu : ¬ IsUnit (⟨algebraMap A ↥K ϖ, hOV _ (hAO ϖ)⟩ : ↥V₀) := (key𝔭 _ (hAO ϖ)).mp hϖ𝔭
    haveI : IsDiscreteValuationRing ↥W := hWdvr
    have hϖW : algebraMap A ↥K ϖ ∈ W := hBW _ (B.algebraMap_mem ϖ)
    have hirrW : Irreducible (⟨algebraMap A ↥K ϖ, hϖW⟩ : ↥W) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hWϖ
    have hVW : ∀ x : ↥K, x ∈ V₀ → x ∈ W := by
      intro x hxV
      by_contra hxW
      have hx0 : x ≠ 0 := fun h0 => hxW (h0.symm ▸ zero_mem W)
      have hxiW : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hxW
      have hxi0 : (⟨x⁻¹, hxiW⟩ : ↥W) ≠ 0 := fun h0 => by
        have := congrArg (fun z : ↥W => (z : ↥K)) h0
        simp only [ZeroMemClass.coe_zero, inv_eq_zero] at this
        exact hx0 this
      obtain ⟨n, u, hnu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxi0 hirrW
      have hn1 : 1 ≤ n := by
        by_contra hn0
        have hn0' : n = 0 := by omega
        rw [hn0', pow_zero, mul_one] at hnu
        have hxiU : IsUnit (⟨x⁻¹, hxiW⟩ : ↥W) := by rw [hnu]; exact Units.isUnit u
        obtain ⟨-, hmem⟩ := (unitK W _ hxiW).mp hxiU
        rw [inv_inv] at hmem
        exact hxW hmem

      have hK : x⁻¹ = ((u : ↥W) : ↥K) * (algebraMap A ↥K ϖ) ^ n := by
        have := congrArg (fun z : ↥W => (z : ↥K)) hnu
        simpa using this
      have huV : ((u : ↥W) : ↥K) ∈ V₀ := hWV _ (u : ↥W).2
      have hne : ((u : ↥W) : ↥K) * (algebraMap A ↥K ϖ) ^ n ≠ 0 := by
        rw [← hK]; exact inv_ne_zero hx0
      have hpn : (algebraMap A ↥K ϖ) ^ (n - 1) * algebraMap A ↥K ϖ = (algebraMap A ↥K ϖ) ^ n := by
        rw [← pow_succ]; congr 1; omega
      have hx' : x = (((u : ↥W) : ↥K) * (algebraMap A ↥K ϖ) ^ n)⁻¹ := by rw [← hK, inv_inv]
      have hprod : x * ((u : ↥W) : ↥K) * (algebraMap A ↥K ϖ) ^ (n - 1) * algebraMap A ↥K ϖ = 1 := by
        calc x * ((u : ↥W) : ↥K) * (algebraMap A ↥K ϖ) ^ (n - 1) * algebraMap A ↥K ϖ
            = x * (((u : ↥W) : ↥K) * ((algebraMap A ↥K ϖ) ^ (n - 1) * algebraMap A ↥K ϖ)) := by ring
          _ = (((u : ↥W) : ↥K) * (algebraMap A ↥K ϖ) ^ n)⁻¹ * (((u : ↥W) : ↥K) * (algebraMap A ↥K ϖ) ^ n) := by
              rw [hpn, hx']
          _ = 1 := inv_mul_cancel₀ hne
      have hinv : x * ((u : ↥W) : ↥K) * (algebraMap A ↥K ϖ) ^ (n - 1) = (algebraMap A ↥K ϖ)⁻¹ :=
        eq_inv_of_mul_eq_one_left hprod
      apply hϖVnu
      refine (unitK V₀ _ (hOV _ (hAO ϖ))).mpr ⟨hϖK0, ?_⟩
      rw [← hinv]
      exact mul_mem (mul_mem hxV huV) (pow_mem (hOV _ (hAO ϖ)) _)
    exact hVW f (hOV f hfO)

  by_contra hn
  push_neg at hn
  obtain ⟨b₀, hb₀𝔫, hb₀W⟩ := hn
  let inclBW : ↥B →+* ↥W :=
    { toFun := fun b => ⟨(b : ↥K), hBW _ b.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  haveI : (maximalIdeal ↥W).IsPrime := (maximalIdeal.isMaximal ↥W).isPrime
  let 𝔴 : Ideal ↥B := (maximalIdeal ↥W).comap inclBW
  have h𝔴p : 𝔴.IsPrime := Ideal.comap_isPrime inclBW (maximalIdeal ↥W)
  have h𝔴𝔫' : 𝔴 ≤ 𝔫 := fun b hb => h𝔴𝔫 b hb
  have hb₀𝔴 : b₀ ∉ 𝔴 := hb₀W
  have hϖ𝔴 : algebraMap A ↥B ϖ ∈ 𝔴 := by
    show (⟨((algebraMap A ↥B ϖ : ↥B) : ↥K), hBW _ (algebraMap A ↥B ϖ).2⟩ : ↥W) ∈ maximalIdeal ↥W
    have e : (⟨((algebraMap A ↥B ϖ : ↥B) : ↥K), hBW _ (algebraMap A ↥B ϖ).2⟩ : ↥W) =
        ⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ := Subtype.ext (by rw [Subalgebra.coe_algebraMap])
    rw [e, hWϖ]
    exact Ideal.mem_span_singleton_self _

  have h𝔫max : 𝔫.IsMaximal := by
    haveI := hR2.2.2
    let I : Ideal ↥B := Ideal.span {algebraMap A ↥B ϖ}
    have hI𝔴 : I ≤ 𝔴 := (Ideal.span_singleton_le_iff_mem _).mpr hϖ𝔴
    have hI𝔫 : I ≤ 𝔫 := hI𝔴.trans h𝔴𝔫'
    have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
    have hker : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
    haveI := h𝔫p
    haveI := h𝔴p
    have hP' : (𝔫.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hI𝔫)
    have hQ' : (𝔴.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hI𝔴)
    have hcomap : ∀ P : Ideal ↥B, I ≤ P → (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P := by
      intro P hP
      rw [Ideal.comap_map_of_surjective _ hmk, ← RingHom.ker_eq_comap_bot, hker]
      exact sup_eq_left.mpr hP
    rcases (Ring.krullDimLE_one_iff.mp ‹_› (𝔫.map (Ideal.Quotient.mk I)) hP') with hmin | hmax
    · exfalso
      have hle : 𝔫.map (Ideal.Quotient.mk I) ≤ 𝔴.map (Ideal.Quotient.mk I) :=
        hmin.2 ⟨hQ', bot_le⟩ (Ideal.map_mono h𝔴𝔫')
      have : 𝔫 ≤ 𝔴 := by
        have h1 := Ideal.comap_mono (f := Ideal.Quotient.mk I) hle
        rwa [hcomap 𝔫 hI𝔫, hcomap 𝔴 hI𝔴] at h1
      exact hb₀𝔴 (this hb₀𝔫)
    · rw [← hcomap 𝔫 hI𝔫]
      exact Ideal.comap_isMaximal_of_surjective _ hmk

  haveI := h𝔫max
  letI fld : Field (↥B ⧸ 𝔫) := Ideal.Quotient.field 𝔫
  let φ : A →+* (↥B ⧸ 𝔫) := (Ideal.Quotient.mk 𝔫).comp (algebraMap A ↥B)
  have hφ : ∀ x ∈ maximalIdeal A, φ x = 0 := by
    intro x hx
    rw [hϖ, Ideal.mem_span_singleton] at hx
    obtain ⟨d, rfl⟩ := hx
    show Ideal.Quotient.mk 𝔫 (algebraMap A ↥B (ϖ * d)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact Ideal.mul_mem_right _ _ (h𝔴𝔫' hϖ𝔴)
  let φκ : ResidueField A →+* (↥B ⧸ 𝔫) := Ideal.Quotient.lift (maximalIdeal A) φ hφ
  have hφκ : φκ.comp (IsLocalRing.residue A) = φ := RingHom.ext fun _ => rfl
  haveI : Algebra.FinitePresentation A ↥B := hR2.2.1
  have hft : φ.FiniteType :=
    RingHom.FiniteType.comp_surjective (RingHom.finiteType_algebraMap.mpr inferInstance) Ideal.Quotient.mk_surjective
  have hftκ : φκ.FiniteType := RingHom.FiniteType.of_comp_finiteType (by rw [hφκ]; exact hft)
  have hint : φκ.IsIntegral := (RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hftκ).to_isIntegral
  have hbij := IsAlgClosed.ringHom_bijective_of_isIntegral φκ hint
  obtain ⟨k, hk⟩ := hbij.2 (Ideal.Quotient.mk 𝔫 x₀)
  obtain ⟨lam, rfl⟩ := IsLocalRing.residue_surjective k
  have hx₀lam : x₀ - algebraMap A ↥B lam ∈ 𝔫 := by
    rw [← Ideal.Quotient.eq, ← hk]
    rfl

  have h1 : ¬ IsUnit (⟨((x₀ - algebraMap A ↥B lam : ↥B) : ↥K), hBV _ (x₀ - algebraMap A ↥B lam).2⟩ : ↥V₀) :=
    (h𝔫mem _).mp hx₀lam
  have h1O : (1 : ↥K) - algebraMap A ↥K lam * (c : ↥K) ∈ O := sub_mem (one_mem _) (mul_mem (hAO lam) c.2)
  have h2 : ¬ IsUnit (⟨(1 : ↥K) - algebraMap A ↥K lam * (c : ↥K), hOV _ h1O⟩ : ↥V₀) := by
    intro hu
    apply h1
    have e : (⟨(1 : ↥K) - algebraMap A ↥K lam * (c : ↥K), hOV _ h1O⟩ : ↥V₀) =
        ⟨((x₀ - algebraMap A ↥B lam : ↥B) : ↥K), hBV _ (x₀ - algebraMap A ↥B lam).2⟩ * ⟨(c : ↥K), hcV⟩ := by
      apply Subtype.ext
      show (1 : ↥K) - algebraMap A ↥K lam * (c : ↥K) = ((x₀ - algebraMap A ↥B lam : ↥B) : ↥K) * (c : ↥K)
      rw [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, sub_mul, hx₀c]
    rw [e] at hu
    exact isUnit_of_mul_isUnit_left hu
  have h3 : (⟨_, h1O⟩ : ↥O) ∈ 𝔭 := (key𝔭 _ h1O).mpr h2
  have h4 : (⟨_, h1O⟩ : ↥O) ∈ maximalIdeal ↥O := h𝔭le h3
  have h5 : (⟨algebraMap A ↥K lam, hAO lam⟩ * c : ↥O) ∈ maximalIdeal ↥O := Ideal.mul_mem_left _ _ hcmax
  have h6 : (1 : ↥O) ∈ maximalIdeal ↥O := by
    have e : (1 : ↥O) = ⟨_, h1O⟩ + ⟨algebraMap A ↥K lam, hAO lam⟩ * c := by
      apply Subtype.ext
      show (1 : ↥K) = ((1 : ↥K) - algebraMap A ↥K lam * (c : ↥K)) + algebraMap A ↥K lam * (c : ↥K)
      ring
    rw [e]; exact add_mem h4 h5
  exact (maximalIdeal.isMaximal ↥O).ne_top ((Ideal.eq_top_iff_one _).mpr h6)

end S_ModularCurve_FullLevel_AuxLevelOne_mem_exceptionalValuation_of_mem_end_of_ringEquiv_adicCompletion_uvCrossingModel_centre_of_end_blowupChart_linked_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_mem_exceptionalValuation_of_mem_end_of_ringEquiv_adicCompletion_uvCrossingModel_centre_of_end_blowupChart_linked_of_dvd (solution)
