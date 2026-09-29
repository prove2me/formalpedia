-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.blowupChart_primes_transitive_reduced_of_levelAut_stable_of_exceptional_eq_span_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/6c69dce3-924a-5090-937a-4f70ebd97375

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
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_pow_map_germ_mem_span_of_mem_asIdeal_of_ringEquiv_adicCompletion_stalk
import Theorems.Thm_Algebra_FormallySmooth_isReduced_quotient_map_of_isMaximal_of_finitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_primes_transitive_reduced_of_levelAut_stable_of_exceptional_eq_span_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

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

    (hJstab : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        ∀ (a : ↥(chartAlgFin A (↥K) j)) (ha : τ (a : ↥K) ∈ chartAlgFin A (↥K) j),
          a ∈ J ↔ (⟨τ (a : ↥K), ha⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J)

    (hBstab : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        ∀ f : ↥K, f ∈ B → τ f ∈ B)

    (hPid : ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W ↔
      b ∈ Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j))))

    (hJy : J ≤ y) (hϖtJ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ J) :

      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧

      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) := by
  classical

  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(chartAlgFin A (↥K) j) →+* (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}),
      Ψ = (e₁ : (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) →+* (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})).comp ((algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))).comp (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom))) := ⟨_, rfl⟩
  obtain ⟨𝔑, h𝔑⟩ : ∃ 𝔑 : Ideal (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}),
      𝔑 = Ideal.span {(Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})) (MvPowerSeries.C (σ₁ ϖt)), (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})) (MvPowerSeries.X 0), (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})) (MvPowerSeries.X 1)} := ⟨_, rfl⟩
  obtain ⟨Jy, hJy⟩ : ∃ Jy : Ideal ↥(chartAlgFin A (↥K) j), Jy = Ideal.comap Ψ 𝔑 := ⟨_, rfl⟩
  have hJ' : J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) Jy} := by
    rw [hJy, hΨ, h𝔑]; exact hJ

  have hA4c := ModularCurve.FullLevel.AuxLevel.exists_pow_map_germ_mem_span_of_mem_asIdeal_of_ringEquiv_adicCompletion_stalk
    q L K A hAq j ϖ hϖ ϖt hϖt z y' hy' W₁ σ₁ hσ₁ f₁ u₁ v₁ hf₁ e₁
  obtain ⟨n, hn1, hradexp⟩ := hA4c
  have hrad : ∀ a ∈ y, a ^ n ∈ Jy := by
    intro a ha
    have ha' : a ∈ y'.asIdeal := by rw [hy'y]; exact ha
    have h := hradexp a ha'
    rw [hJy, Ideal.mem_comap, map_pow Ψ a n, hΨ, h𝔑]
    exact h

  have hqp : q.Prime := Fact.out
  have hlp : ℓ.Prime := Fact.out
  have hUMO := ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
    q M' hqM' ℓ hℓM' L ζ hζ hι H₁ hH₁ K hK
  obtain ⟨huniq, hmul, hone⟩ := hUMO
  have hEX := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
    q M' hqM' ℓ hℓM' L ζ hζ H₁ hH₁ K hK
  have hSTAB : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ K τ → (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j) :=
    fun γ hγ τ hτ a ha =>
      ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt q M' L q ζ hι
        K A j hj H₁ γ τ hτ a ha
  have hGfin := (ModularCurve.FullLevel.AuxLevelOne.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma_of_dvd
    q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK (Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ}) rfl).1
  have hSfin : ({τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ}).Finite := by
    have h1 : ((Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ} : Subgroup (↥K ≃ₐ[L] ↥K)) : Set (↥K ≃ₐ[L] ↥K)).Finite := by
      haveI := hGfin
      exact Set.toFinite _
    exact h1.subset Subgroup.subset_closure
  have hexTF : ∃ TF : Finset (↥K ≃ₐ[L] ↥K), ∀ τ : ↥K ≃ₐ[L] ↥K, τ ∈ TF ↔ (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ) :=
    ⟨hSfin.toFinset, fun τ => Set.Finite.mem_toFinset hSfin⟩
  obtain ⟨TF, hmemT⟩ := hexTF
  have hstabT : ∀ τ : ↥K ≃ₐ[L] ↥K, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ) → (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j) := by
    rintro τ ⟨γ, hγq, hγ0, hτ⟩
    exact hSTAB γ⁻¹ (inv_mem hγ0) τ hτ
  have hBst : ∀ τ : ↥K ≃ₐ[L] ↥K, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ) → ∀ f : ↥K, f ∈ B → τ f ∈ B := by
    rintro τ ⟨γ, hγq, hγ0, hτ⟩
    exact hBstab γ hγ0 τ hτ
  have hmulT : ∀ σ : ↥K ≃ₐ[L] ↥K, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K σ) → ∀ τ : ↥K ≃ₐ[L] ↥K, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ) → (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K (σ * τ)) := by
    rintro σ ⟨γ₁, h1q, h10, hσ⟩ τ ⟨γ₂, h2q, h20, hτ⟩
    refine ⟨γ₁ * γ₂, mul_mem h1q h2q, mul_mem h10 h20, ?_⟩
    rw [mul_inv_rev]
    exact hmul γ₁⁻¹ γ₂⁻¹ (inv_mem h10) (inv_mem h20) σ τ hσ hτ
  have hinvT : ∀ σ : ↥K ≃ₐ[L] ↥K, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K σ) → ∃ σ' : ↥K ≃ₐ[L] ↥K, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K σ') ∧ σ * σ' = 1 := by
    rintro σ ⟨γ, hγq, hγ0, hσ⟩
    have hex := hEX γ⁻¹ (inv_mem hγ0)
    obtain ⟨σ', hσ'⟩ := hex
    refine ⟨σ', ⟨γ⁻¹, inv_mem hγq, inv_mem hγ0, hσ'⟩, ?_⟩
    have hprod := hmul γ⁻¹ (γ⁻¹)⁻¹ (inv_mem hγ0) (inv_mem (inv_mem hγ0)) σ σ' hσ hσ'
    rw [inv_mul_cancel] at hprod
    have h11 := hone 1 (one_mem _) (one_mem _) (by simp)
    exact huniq 1 (one_mem _) (σ * σ') 1 hprod h11

  have hinvT2 : ∀ σ : ↥K ≃ₐ[L] ↥K, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K σ) → ∃ σ' : ↥K ≃ₐ[L] ↥K, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K σ') ∧
      (∀ k : ↥K, σ (σ' k) = k) ∧ (∀ k : ↥K, σ' (σ k) = k) := by
    intro σ hσ
    obtain ⟨σ', hσ'P, h1⟩ := hinvT σ hσ
    have h2 : σ' * σ = 1 := by
      rw [← inv_eq_of_mul_eq_one_right h1, inv_mul_cancel]
    refine ⟨σ', hσ'P, fun k => ?_, fun k => ?_⟩
    · have := congrArg (fun e : ↥K ≃ₐ[L] ↥K => e k) h1
      simpa [AlgEquiv.mul_apply] using this
    · have := congrArg (fun e : ↥K ≃ₐ[L] ↥K => e k) h2
      simpa [AlgEquiv.mul_apply] using this

  have hexrr : ∃ rr : (↥K ≃ₐ[L] ↥K) → (↥(chartAlgFin A (↥K) j) →+* ↥(chartAlgFin A (↥K) j)),
      ∀ (τ : ↥K ≃ₐ[L] ↥K) (h : (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)), rr τ = ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) h) := by
    refine ⟨fun τ => if h : (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j) then ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) h) else RingHom.id _, ?_⟩
    intro τ h
    exact dif_pos h
  obtain ⟨rr, hrr⟩ := hexrr
  have hrr_coe : ∀ (τ : ↥K ≃ₐ[L] ↥K) (h : (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)) (c : ↥(chartAlgFin A (↥K) j)), ((rr τ c : ↥(chartAlgFin A (↥K) j)) : ↥K) = τ (c : ↥K) := by
    intro τ h c
    rw [hrr τ h]
    rfl
  have hinfJ : TF.inf (fun σ => Jy.comap (rr σ)) ≤ J := by
    rw [hJ']
    refine le_sInf ?_
    intro J' hJ'mem
    obtain ⟨γ, hγq, hγ0, τ, hτ, hpres, rfl⟩ := hJ'mem
    have hτT : τ ∈ TF := (hmemT τ).mpr ⟨γ, hγq, hγ0, hτ⟩
    calc TF.inf (fun σ => Jy.comap (rr σ)) ≤ Jy.comap (rr τ) := Finset.inf_le (f := fun σ => Jy.comap (rr σ)) hτT
      _ = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) Jy := by rw [hrr τ hpres]

  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hq0 : (q : A) ≠ 0 := by
    intro h
    have hL : (q : L) = 0 := by
      have := congrArg (algebraMap A L) h
      simpa using this
    exact (Nat.cast_ne_zero.mpr hqp.ne_zero) hL
  have hϖt0 : ϖt ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, h⟩ := hϖt
    have hpos : q ^ 2 - 1 ≠ 0 := by
      have h2 := hqp.two_le
      have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    rw [zero_pow hpos] at h
    exact hq0 ((hu.mul_left_eq_zero).mp h.symm)
  have hϖtK : algebraMap A ↥K ϖt ≠ 0 := (map_ne_zero_iff _ hinjAK).mpr hϖt0

  have hR5b : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
        ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ ∧
          ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W →
            τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q := by
    intro Q hQ hϖQ

    have hϖtQ : algebraMap A ↥B ϖt ∈ Q := by
      obtain ⟨u, hu, hpow⟩ := hϖt
      have hqmem : (q : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAq
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hqmem
      apply hQ.mem_of_pow_mem (q ^ 2 - 1)
      rw [← map_pow, hpow, ← hd, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hϖQ)

    have hP : (Q.comap (Subalgebra.inclusion hR1.1).toRingHom).IsPrime := Ideal.comap_isPrime _ Q
    have hJP : J ≤ Q.comap (Subalgebra.inclusion hR1.1).toRingHom := by
      intro i hi
      rw [Ideal.mem_comap]
      have hxB : ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ ∈ B := by
        rw [hB, Subalgebra.mem_restrictScalars]
        refine Algebra.subset_adjoin ⟨i, hi, ?_⟩
        rw [mul_assoc, inv_mul_cancel₀ hϖtK, mul_one]
      have heq : (Subalgebra.inclusion hR1.1).toRingHom i =
          (⟨_, hxB⟩ : ↥B) * algebraMap A ↥B ϖt := by
        apply Subtype.ext
        show ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ * ((algebraMap A ↥B ϖt : ↥B) : ↥K)
        rw [Subalgebra.coe_algebraMap, mul_assoc, inv_mul_cancel₀ hϖtK, mul_one]
      rw [heq]
      exact Ideal.mul_mem_left _ _ hϖtQ

    have hinfP := hinfJ.trans hJP
    obtain ⟨τ₀, hτ₀T, hτ₀P⟩ := (Ideal.IsPrime.inf_le' hP).mp hinfP
    have hτ₀P' : y.comap (rr τ₀) ≤ Q.comap (Subalgebra.inclusion hR1.1).toRingHom := by
      intro c hc
      rw [Ideal.mem_comap] at hc
      have h2 : c ^ n ∈ Jy.comap (rr τ₀) := by
        rw [Ideal.mem_comap, map_pow]
        exact hrad _ hc
      exact hP.mem_of_pow_mem n (hτ₀P h2)
    have hτ₀prop := (hmemT τ₀).mp hτ₀T
    have hst₀ := hstabT τ₀ hτ₀prop
    obtain ⟨σ, hσP, hτσ, hστ⟩ := hinvT2 τ₀ hτ₀prop
    have hstσ := hstabT σ hσP
    obtain ⟨γ, hγq, hγ0, hσA⟩ := hσP
    refine ⟨γ, hγq, hγ0, σ, hσA, fun b hbW => ⟨hBst σ ⟨γ, hγq, hγ0, hσA⟩ _ b.2, fun hb => ?_⟩⟩

    have hσy : ∀ c : ↥(chartAlgFin A (↥K) j), c ∈ y → (Subalgebra.inclusion hR1.1).toRingHom (rr σ c) ∈ Q := by
      intro c hc
      have h1 : rr σ c ∈ y.comap (rr τ₀) := by
        rw [Ideal.mem_comap]
        have heq : rr τ₀ (rr σ c) = c := by
          apply Subtype.ext
          rw [hrr_coe τ₀ hst₀, hrr_coe σ hstσ, hτσ]
        rw [heq]; exact hc
      have h2 := hτ₀P' h1
      rw [Ideal.mem_comap] at h2
      exact h2

    have hσBst : ∀ f : ↥K, f ∈ B → σ f ∈ B := hBst σ ⟨γ, hγq, hγ0, hσA⟩
    have hexσB : ∃ σB : ↥B →+* ↥B, ∀ x : ↥B, ((σB x : ↥B) : ↥K) = σ (x : ↥K) :=
      ⟨(σ : ↥K →+* ↥K).restrict B B hσBst, fun x => rfl⟩
    obtain ⟨σB, hσB⟩ := hexσB
    have hbspan := (hPid b).mp hbW
    have hmap : σB b ∈ Ideal.map σB (Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j)))) :=
      Ideal.mem_map_of_mem σB hbspan
    rw [Ideal.map_span] at hmap
    have hle : Ideal.span (σB '' ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j)))) ≤ Q := by
      refine Ideal.span_le.mpr ?_
      rintro x ⟨x', ⟨c, hc, rfl⟩, rfl⟩
      have h := hσy c hc
      have heq : σB (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B) = (Subalgebra.inclusion hR1.1).toRingHom (rr σ c) := by
        apply Subtype.ext
        rw [hσB]
        show σ (c : ↥K) = ((rr σ c : ↥(chartAlgFin A (↥K) j)) : ↥K)
        rw [hrr_coe σ hstσ]
      rw [heq]; exact h
    have hfinal := hle hmap
    have heq : (⟨σ (b : ↥K), hb⟩ : ↥B) = σB b := Subtype.ext (by rw [hσB])
    rw [heq]; exact hfinal
  refine ⟨hR5b, ?_⟩

  intro b hall

  have hbQ : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q → b ∈ Q := by
    intro Q hQ hϖQ
    obtain ⟨γ, hγq, hγ0, τ, hτ, hτQ⟩ := hR5b Q hQ hϖQ
    obtain ⟨τ', hτ'P, hττ', hτ'τ⟩ := hinvT2 τ ⟨γ, hγq, hγ0, hτ⟩
    obtain ⟨γ', hγ'q, hγ'0, hτ'A⟩ := hτ'P
    have hb' : τ' (b : ↥K) ∈ B := hBst τ' ⟨γ', hγ'q, hγ'0, hτ'A⟩ _ b.2
    have hW' := hall γ' hγ'q hγ'0 τ' hτ'A hb'
    have h := hτQ ⟨τ' (b : ↥K), hb'⟩ hW'
    obtain ⟨hmemB, hQmem⟩ := h
    have hbB : τ (τ' (b : ↥K)) ∈ B := hmemB
    have := hQmem hbB
    have heq : (⟨τ (τ' (b : ↥K)), hbB⟩ : ↥B) = b := Subtype.ext (hττ' _)
    rwa [heq] at this

  have hrad_mem : b ∈ (Ideal.span {algebraMap A ↥B ϖ}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro Q ⟨hQle, hQ⟩
    exact hbQ Q hQ (hQle (Ideal.subset_span (by simp)))
  obtain ⟨m, hm⟩ := hrad_mem
  haveI := hR2.1
  haveI := hR2.2.1
  have hred := Algebra.FormallySmooth.isReduced_quotient_map_of_isMaximal_of_finitePresentation A ↥B
    (maximalIdeal A) (maximalIdeal.isMaximal A)
  have hmapI : Ideal.map (algebraMap A ↥B) (maximalIdeal A) = Ideal.span {algebraMap A ↥B ϖ} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]
  rw [hmapI] at hred
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {algebraMap A ↥B ϖ}) b) :=
    ⟨m, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hm⟩
  have h0 := hnil.eq_zero
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨c, hc⟩ := h0
  exact ⟨c, by rw [← hc, mul_comm]⟩

end S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_primes_transitive_reduced_of_levelAut_stable_of_exceptional_eq_span_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_primes_transitive_reduced_of_levelAut_stable_of_exceptional_eq_span_of_dvd (solution)
