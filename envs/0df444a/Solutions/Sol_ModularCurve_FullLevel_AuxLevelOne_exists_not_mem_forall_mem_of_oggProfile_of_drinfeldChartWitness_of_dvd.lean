-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_not_mem_forall_mem_of_oggProfile_of_drinfeldChartWitness_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/6eb41b5e-2393-5df5-a796-60604ec17d1b

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

import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_mem_Gamma_isLevelAutAt_forall_mem_iff_coeff_mem_maximalIdeal_of_le_of_ne_of_drinfeldChartWitness_of_dvd
import Theorems.Thm_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow
import Theorems.Thm_DrinfeldCurve_LocalChart_isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_not_mem_forall_mem_of_oggProfile_of_drinfeldChartWitness_of_dvd
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

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

    (g : ↥(chartAlgFin A (↥K) j)) (hg0 : ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0)
    (hgϖ : ∃ (k : ℕ) (z : ↥(chartAlgFin A (↥K) j)), g * z = algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ^ k)
    (hginv : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        τ ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((g : ↥(chartAlgFin A (↥K) j)) : ↥K))
    (hgprof : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ δ⁻¹ K τ →
        ((∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((τ ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ↔
          ¬ ((q : ℤ) ∣ (δ 1 0 : ℤ))))

    (𝔭 : Ideal ↥(chartAlgFin A (↥K) j)) (h𝔭 : 𝔭.IsPrime) (hϖ𝔭 : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭) (h𝔭y : 𝔭 ≤ y) (h𝔭ne : 𝔭 ≠ y) :
    ∃ (u : ↥(chartAlgFin A (↥K) j)) (_ : ((u : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
      (∃ (k : ℕ) (z : ↥(chartAlgFin A (↥K) j)), u * z = algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ^ k) ∧
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          τ ((u : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((u : ↥(chartAlgFin A (↥K) j)) : ↥K)) ∧
      u ∉ 𝔭 ∧
      ∀ 𝔭' : Ideal ↥(chartAlgFin A (↥K) j), 𝔭'.IsPrime → algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭' → 𝔭' ≤ y → 𝔭' ≠ y → 𝔭' ≠ 𝔭 → u ∈ 𝔭' := by
  classical

  have hconst := hW₁.1
  have hanch := hW₁.2.2.2.2.2.1

  let S : Type := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
  let mkS : MvPowerSeries (Fin 2) W₁ →+* S := (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}))
  let toC : ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) →+* (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) := algebraMap _ _
  let germY : ↥(chartAlgFin A (↥K) j) →+* ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) := (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom))
  let Ψ : ↥(chartAlgFin A (↥K) j) →+* S := ((e₁ : (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) →+* S).comp (toC.comp germY))
  let 𝔐 : Ideal S := Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}

  obtain ⟨hcen, hdense, hΨconst, -, -, hcomapσ, hmax, huniq, -⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hconst

  have hϖA : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hσmem : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → σ₁ a ∈ IsLocalRing.maximalIdeal W₁ := by
    intro a ha; rw [← hcomapσ] at ha; exact ha
  have hqW : (q : W₁) ∈ IsLocalRing.maximalIdeal W₁ := by
    have := hσmem _ hAq; simpa using this
  have hϖtA : ϖt ∈ IsLocalRing.maximalIdeal A := by
    obtain ⟨u, hu, hpow⟩ := hϖt
    have hmem : ϖt ^ (q ^ 2 - 1) ∈ IsLocalRing.maximalIdeal A := by
      rw [hpow]; exact Ideal.mul_mem_right _ _ hAq
    exact (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem _ hmem
  have hc : σ₁ (ϖt ^ (q + 1)) ∈ IsLocalRing.maximalIdeal W₁ :=
    hσmem _ (Ideal.pow_mem_of_mem _ hϖtA _ (Nat.succ_pos q))
  have hσinj : Function.Injective σ₁ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    have hprime : (RingHom.ker σ₁).IsPrime := RingHom.ker_isPrime σ₁
    have hmax' : (RingHom.ker σ₁).IsMaximal := Ideal.IsPrime.isMaximal hprime hne
    have hker : RingHom.ker σ₁ = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax'
    have hϖ0 : σ₁ ϖ = 0 := by
      have : ϖ ∈ RingHom.ker σ₁ := hker.symm ▸ hϖA
      exact this
    have : IsLocalRing.maximalIdeal W₁ = ⊥ := by rw [hσ₁, hϖ0, Ideal.span_singleton_zero]
    exact IsDiscreteValuationRing.not_a_field W₁ this
  have hc0 : σ₁ (ϖt ^ (q + 1)) ≠ 0 := by
    intro h0
    have : ϖt ^ (q + 1) = 0 := hσinj (by rw [h0, map_zero])
    have hϖt0 : ϖt = 0 := pow_eq_zero_iff (Nat.succ_ne_zero q) |>.mp this
    obtain ⟨u, hu, hpow⟩ := hϖt
    rw [hϖt0, zero_pow (by
      have : 2 ≤ q := (Fact.out : q.Prime).two_le
      have : 1 < q ^ 2 := by nlinarith
      omega)] at hpow
    have hq0 : (q : A) = 0 := by
      have := hpow.symm
      rcases hu.exists_right_inv with ⟨w, hw⟩
      calc (q : A) = (q : A) * (u * w) := by rw [hw, mul_one]
        _ = ((q : A) * u) * w := by ring
        _ = 0 := by rw [this, zero_mul]
    have : (q : L) = 0 := by
      have := congrArg (algebraMap A L) hq0
      simpa using this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this

  obtain ⟨huniqA, hmul, hone⟩ :=
    ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L ζ hζ hι H₁ hH₁ K hK
  have hex := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L ζ hζ H₁ hH₁ K hK

  have hfin : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
          τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := hW₁.2.1
  have hfix := hW₁.2.2.1
  have hlin := hW₁.2.2.2.1

  obtain ⟨hexist, -, hiii, -⟩ := DrinfeldCurve.LocalChart.branchPrimes_of_sub_drinfeldForm_mem_pow q W₁ (σ₁ ϖ) hσ₁ hqW
    (σ₁ (ϖt ^ (q + 1))) hc hc0 f₁ u₁ v₁ hu₁ hv₁ hf₁

  have h11 : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ 1 K 1 := hone 1 (one_mem _) (one_mem _) (by simp)
  have h11' : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ (1 : SL(2, ℤ))⁻¹ K 1 := by rw [inv_one]; exact h11

  have hgG : ¬ (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, ((((g : ↥(chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) := by
    intro hG
    have hp := (hgprof 1 (one_mem _) 1 h11').mp (by simpa only [AlgEquiv.one_apply] using hG)
    apply hp
    have : ((1 : SL(2, ℤ)) 1 0 : ℤ) = 0 := by
      rw [Matrix.SpecialLinearGroup.coe_one]; exact Matrix.one_apply_ne (by decide)
    rw [this]; exact dvd_zero _

  obtain ⟨δ₀, hδ₀ℓ, hδ₀0, τ₀, hτ₀, h𝔭iff⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.exists_mem_Gamma_isLevelAutAt_forall_mem_iff_coeff_mem_maximalIdeal_of_le_of_ne_of_drinfeldChartWitness_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ 𝔭 h𝔭 hϖ𝔭 h𝔭y h𝔭ne

  obtain ⟨τ₀', hτ₀'⟩ := hex δ₀⁻¹ (inv_mem hδ₀0)
  have h00' : τ₀ * τ₀' = 1 := by
    have h := hmul _ _ (inv_mem hδ₀0) (inv_mem (inv_mem hδ₀0)) _ _ hτ₀ hτ₀'
    rw [inv_inv, mul_inv_cancel] at h
    exact huniqA 1 (one_mem _) _ _ h h11
  have h0'0 : τ₀' * τ₀ = 1 := by
    have h := hmul _ _ (inv_mem (inv_mem hδ₀0)) (inv_mem hδ₀0) _ _ hτ₀' hτ₀
    rw [inv_inv, inv_mul_cancel] at h
    exact huniqA 1 (one_mem _) _ _ h h11
  have hτ₀inv : ∀ x : ↥K, τ₀ (τ₀' x) = x := fun x => by
    rw [← AlgEquiv.mul_apply, h00', AlgEquiv.one_apply]
  have hτ₀'inv : ∀ x : ↥K, τ₀' (τ₀ x) = x := fun x => by
    rw [← AlgEquiv.mul_apply, h0'0, AlgEquiv.one_apply]
  have hpres0 := hfin δ₀ hδ₀0 τ₀ hτ₀
  have hpres0' := hfin δ₀⁻¹ (inv_mem hδ₀0) τ₀' hτ₀'

  have huC : τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ chartAlgFin A (↥K) j := hpres0' _ g.2
  refine ⟨⟨τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K), huC⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h
    apply hg0
    apply τ₀'.injective
    rw [map_zero]; exact h
  ·
    obtain ⟨k, zc, hgz⟩ := hgϖ
    refine ⟨k, ⟨τ₀' ((zc : ↥(chartAlgFin A (↥K) j)) : ↥K), hpres0' _ zc.2⟩, ?_⟩
    apply Subtype.ext
    have hK : ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) * ((zc : ↥(chartAlgFin A (↥K) j)) : ↥K) = (algebraMap A ↥K ϖ) ^ k := by
      have := congrArg (fun c : ↥(chartAlgFin A (↥K) j) => ((c : ↥(chartAlgFin A (↥K) j)) : ↥K)) hgz
      simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using this
    show τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) * τ₀' ((zc : ↥(chartAlgFin A (↥K) j)) : ↥K) = (((algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ^ k) : ↥(chartAlgFin A (↥K) j)) : ↥K)
    rw [← map_mul, hK, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, map_pow,
      IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  ·
    intro γ hγq hγ0 σ hσ
    have hγ' : δ₀ * γ * δ₀⁻¹ ∈ CongruenceSubgroup.Gamma q :=
      (CongruenceSubgroup.Gamma_normal q).conj_mem γ hγq δ₀
    have hγ'0 : δ₀ * γ * δ₀⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := mul_mem (mul_mem hδ₀0 hγ0) (inv_mem hδ₀0)
    have hatt : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ (δ₀ * γ * δ₀⁻¹)⁻¹ K (τ₀ * σ * τ₀') := by
      have h1 := hmul _ _ (inv_mem hδ₀0) (inv_mem hγ0) _ _ hτ₀ hσ
      have h2 := hmul _ _ (mul_mem (inv_mem hγ0) (inv_mem hδ₀0)) (inv_mem (inv_mem hδ₀0)) _ _ h1 hτ₀'
      have heq : (δ₀ * γ * δ₀⁻¹)⁻¹ = (δ₀⁻¹)⁻¹ * (γ⁻¹ * δ₀⁻¹) := by group
      rw [heq]; exact h2
    have hfixg := hginv (δ₀ * γ * δ₀⁻¹) hγ' hγ'0 (τ₀ * σ * τ₀') hatt
    show σ (τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K)) = τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K)
    calc σ (τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K)) = τ₀' (τ₀ (σ (τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K)))) := (hτ₀'inv _).symm
      _ = τ₀' ((τ₀ * σ * τ₀') ((g : ↥(chartAlgFin A (↥K) j)) : ↥K)) := by simp only [AlgEquiv.mul_apply]
      _ = τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) := by rw [hfixg]
  ·
    intro hu
    have := (h𝔭iff ⟨τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K), huC⟩).mp hu
    apply hgG
    intro n
    obtain ⟨m, hm, hmn⟩ := this n
    refine ⟨m, hm, ?_⟩
    simpa only [hτ₀inv] using hmn
  ·
    intro 𝔭' h𝔭' hϖ𝔭' h𝔭'y h𝔭'ne hne
    obtain ⟨δ', hδ'ℓ, hδ'0, τ', hτ', h𝔭'iff⟩ :=
      ModularCurve.FullLevel.AuxLevelOne.exists_mem_Gamma_isLevelAutAt_forall_mem_iff_coeff_mem_maximalIdeal_of_le_of_ne_of_drinfeldChartWitness_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ 𝔭' h𝔭' hϖ𝔭' h𝔭'y h𝔭'ne

    set ε : SL(2, ℤ) := δ' * δ₀⁻¹ with hεdef
    have hε0 : ε ∈ CongruenceSubgroup.Gamma0 M' := mul_mem hδ'0 (inv_mem hδ₀0)
    have hεℓ : ε ∈ CongruenceSubgroup.Gamma ℓ := mul_mem hδ'ℓ (inv_mem hδ₀ℓ)
    have hεℓ' : ((ε 1 1 : ℤ) : ZMod ℓ) = 1 := (CongruenceSubgroup.Gamma_mem.mp hεℓ).2.2.2
    have hσatt : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ ε⁻¹ K (τ' * τ₀') := by
      have h := hmul _ _ (inv_mem hδ'0) (inv_mem (inv_mem hδ₀0)) _ _ hτ' hτ₀'
      rw [hεdef, mul_inv_rev]; exact h
    have hp := hgprof ε hε0 (τ' * τ₀') hσatt
    by_cases hdiv : (q : ℤ) ∣ (ε 1 0 : ℤ)
    ·
      exfalso
      apply hne
      have hpresσ := hfin ε hε0 (τ' * τ₀') hσatt
      have hfixσ := hfix ε hε0 hεℓ' (τ' * τ₀') hσatt hpresσ
      obtain ⟨θ, cW, M, hθe, hθW, hθM, -, hMc, hcℓ, -⟩ := hlin ε hε0 (τ' * τ₀') hσatt hpresσ hfixσ
      have hcW : cW ∉ IsLocalRing.maximalIdeal W₁ := by
        intro h
        have h1 : (1 : W₁) ∈ IsLocalRing.maximalIdeal W₁ := by
          have := Ideal.sub_mem _ h (hcℓ hεℓ')
          simpa using this
        exact (IsLocalRing.maximalIdeal.isMaximal W₁).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

      have hnd : ¬ ((q : ℤ) ∣ (ε 0 0 : ℤ) ∧ (q : ℤ) ∣ (ε 1 0 : ℤ)) := by
        rintro ⟨h0, h1⟩
        have hdet : (ε 0 0 : ℤ) * (ε 1 1 : ℤ) - (ε 0 1 : ℤ) * (ε 1 0 : ℤ) = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe ε
          rw [Matrix.det_fin_two] at h
          exact h
        have h1' : (q : ℤ) ∣ 1 := by
          rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left h0 _) (dvd_mul_of_dvd_right h1 _)
        have := Int.eq_one_of_dvd_one (by positivity) h1'
        have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
        omega
      obtain ⟨P₁, hP₁, hP₁X, hP₁π, h₀, hh₀, hlinP₁⟩ := hexist (ε 0 0 : ℤ) (ε 1 0 : ℤ) hnd
      have hnd10 : ¬ ((q : ℤ) ∣ (1 : ℤ) ∧ (q : ℤ) ∣ (0 : ℤ)) := by
        rintro ⟨h1, -⟩
        have := Int.eq_one_of_dvd_one (by positivity) h1
        have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
        omega
      obtain ⟨Pinf, hPinf, hPinfX, hPinfπ, hi, hhi, hlinPinf⟩ := hexist 1 0 hnd10
      have hP₁eq : P₁ = Pinf := by
        refine (hiii (ε 0 0 : ℤ) (ε 1 0 : ℤ) 1 0 P₁ Pinf hP₁ hPinf hP₁X hPinfX hP₁π hPinfπ ⟨h₀, hh₀, hlinP₁⟩
          ⟨hi, hhi, hlinPinf⟩ hnd hnd10).mpr ?_
        simpa using hdiv

      have hA : (q : ℤ) ∣ (ε 0 0 : ℤ) - ((ε 0 0 : ℤ) * 1 + (ε 0 1 : ℤ) * 0) := by simp
      have hB : (q : ℤ) ∣ (ε 1 0 : ℤ) - ((ε 1 0 : ℤ) * 1 + (ε 1 1 : ℤ) * 0) := by simp
      obtain ⟨hQ, hQX, hQπ, h₁, hh₁, hlinQ⟩ :=
        DrinfeldCurve.LocalChart.isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime q W₁ (σ₁ ϖ) hσ₁ hqW
          (σ₁ (ϖt ^ (q + 1))) hc hc0 f₁ u₁ v₁ hu₁ hv₁ hf₁ θ hθW M hθM cW hcW ε hMc P₁ hP₁ hP₁X hP₁π 1 0 (ε 0 0 : ℤ) (ε 1 0 : ℤ) hA hB ⟨h₀, hh₀, hlinP₁⟩

      have hanchQ := hanch (Ideal.comap (θ : S →+* S) P₁) hQ hQX hQπ
        ⟨h₁, hh₁, by simpa only [Int.cast_one, Int.cast_zero] using hlinQ⟩
      have hanchI := hanch Pinf hPinf hPinfX hPinfπ ⟨hi, hhi, by simpa only [Int.cast_one, Int.cast_zero] using hlinPinf⟩

      have hborel : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, ((((τ' * τ₀') ((b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ↔
          (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, ((((b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) := by
        intro b
        have e1 := hanchI (((((τ' * τ₀') : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpresσ) b)
        have e2 := hanchQ b
        have hcoe : (((((((τ' * τ₀') : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpresσ) b) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) =
            (τ' * τ₀') ((b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) := rfl
        rw [hcoe] at e1
        rw [← e2, ← e1]
        simp only [Ideal.mem_comap, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [← hθe b, hP₁eq]

      ext a
      rw [h𝔭'iff a, h𝔭iff a]
      have ha0 : τ₀ ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ chartAlgFin A (↥K) j := hpres0 _ a.2
      have hb := hborel ⟨τ₀ ((a : ↥(chartAlgFin A (↥K) j)) : ↥K), ha0⟩
      have hστ : (τ' * τ₀') (τ₀ ((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) = τ' ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) := by
        rw [AlgEquiv.mul_apply, hτ₀'inv]
      simp only [hστ] at hb
      exact hb
    ·
      refine (h𝔭'iff ⟨τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K), huC⟩).mpr ?_
      have : τ' (τ₀' ((g : ↥(chartAlgFin A (↥K) j)) : ↥K)) = (τ' * τ₀') ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) := (AlgEquiv.mul_apply _ _ _).symm
      rw [this]
      exact hp.mpr hdiv

end S_ModularCurve_FullLevel_AuxLevelOne_exists_not_mem_forall_mem_of_oggProfile_of_drinfeldChartWitness_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_not_mem_forall_mem_of_oggProfile_of_drinfeldChartWitness_of_dvd (solution)
