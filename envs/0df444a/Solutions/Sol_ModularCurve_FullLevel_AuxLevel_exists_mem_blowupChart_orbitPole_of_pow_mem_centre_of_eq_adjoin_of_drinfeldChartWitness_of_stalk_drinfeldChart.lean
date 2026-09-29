-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_mem_blowupChart_orbitPole_of_pow_mem_centre_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/8807e0ac-f5a3-5887-9df2-1ebb2609a00d

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

import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_mem_blowupChart_orbitPole_of_pow_mem_centre_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

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

    (hRad :
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
        ∃ n : ℕ, 1 ≤ n ∧ ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), a ∈ y →
          (((e₁ : CMP →+* S).comp (toC.comp germY)) a) ^ n ∈
            Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) :

        (∀ y'' : Ideal ↥(chartAlgFin A (↥K) j), y''.IsMaximal → algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y'' →
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              ¬ (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y'')) →
          ∃ b : ↥K, b ∈ B ∧ ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ V : ValuationSubring ↥K,
              (∀ c : ↥(chartAlgFin A (↥K) j), (c : ↥K) ∈ V) →
              (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : τ.symm (c : ↥K) ∈ chartAlgFin A (↥K) j),
                  (⟨τ.symm (c : ↥K), hc⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y'' → ∀ hcV : (c : ↥K) ∈ V, (⟨(c : ↥K), hcV⟩ : ↥V) ∈ maximalIdeal ↥V) →
              b ∉ V) := by
  classical
  have hW₁' := hW₁
  obtain ⟨-, hEQfin, -, -, -, -, -⟩ := hW₁'

  have hqA : (q : A) ≠ 0 := by
    intro h0
    have : (q : L) = 0 := by
      have := congrArg (algebraMap A L) h0
      simpa using this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  have hϖt0 : ϖt ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, hu'⟩ := hϖt
    have hq2 : q ^ 2 - 1 ≠ 0 := by
      have := (Fact.out : q.Prime).two_le
      have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left this 2
      omega
    rw [zero_pow hq2] at hu'
    exact hqA (by simpa [hu.ne_zero] using (mul_eq_zero.mp hu'.symm))
  have hϖt𝔪 : ϖt ∈ maximalIdeal A := by
    obtain ⟨u, hu, hu'⟩ := hϖt
    apply (Ideal.IsMaximal.isPrime inferInstance).mem_of_pow_mem (q ^ 2 - 1)
    rw [hu']
    exact Ideal.mul_mem_right _ _ hAq
  obtain ⟨a', ha'⟩ : ∃ a' : A, ϖt = ϖ * a' := by
    have := hϖt𝔪; rw [hϖ, Ideal.mem_span_singleton'] at this
    obtain ⟨a', ha'⟩ := this; exact ⟨a', by rw [← ha', mul_comm]⟩
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hϖtK0 : algebraMap A ↥K ϖt ≠ 0 := fun h0 => hϖt0 (hinjAK (by simpa using h0))

  let Tset : Set (↥K ≃ₐ[L] ↥K) := {τ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ}
  have hUMO := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  obtain ⟨huniq, hmulT, honeT⟩ := hUMO
  have hEX := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  have hFIN := ModularCurve.FullLevel.AuxLevel.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK (Subgroup.closure Tset) rfl
  obtain ⟨hGfin, -⟩ := hFIN
  have hTfin : Tset.Finite := by
    have : ((Subgroup.closure Tset : Subgroup (↥K ≃ₐ[L] ↥K)) : Set (↥K ≃ₐ[L] ↥K)).Finite :=
      Set.finite_coe_iff.mp hGfin
    exact this.subset Subgroup.subset_closure
  have hT_one : (1 : ↥K ≃ₐ[L] ↥K) ∈ Tset := by
    refine ⟨1, one_mem _, one_mem _, ?_⟩
    rw [inv_one]
    exact honeT 1 (one_mem _) (one_mem _)
  have hT_mul : ∀ σ τ : ↥K ≃ₐ[L] ↥K, σ ∈ Tset → τ ∈ Tset → σ * τ ∈ Tset := by
    rintro σ τ ⟨γ₁, h₁q, h₁0, h₁⟩ ⟨γ₂, h₂q, h₂0, h₂⟩
    refine ⟨γ₁ * γ₂, mul_mem h₁q h₂q, mul_mem h₁0 h₂0, ?_⟩
    rw [mul_inv_rev]
    exact hmulT γ₁⁻¹ γ₂⁻¹ (inv_mem h₁0) (inv_mem h₂0) σ τ h₁ h₂
  have hT_inv : ∀ τ : ↥K ≃ₐ[L] ↥K, τ ∈ Tset → τ⁻¹ ∈ Tset := by
    rintro τ ⟨γ, hγq, hγ0, hτ⟩
    obtain ⟨τ', hτ'⟩ := hEX γ⁻¹ (inv_mem hγ0)
    have hprod : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') 1 K (τ' * τ) := by
      have := hmulT (γ⁻¹)⁻¹ γ⁻¹ (by rw [inv_inv]; exact hγ0) (inv_mem hγ0) τ' τ hτ' hτ
      rwa [inv_inv, inv_mul_cancel] at this
    have h11 : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') 1 K 1 := honeT 1 (one_mem _) (one_mem _)
    have heq : τ' * τ = 1 := huniq 1 (one_mem _) _ _ hprod h11
    have : τ' = τ⁻¹ := eq_inv_of_mul_eq_one_left heq
    exact ⟨γ⁻¹, inv_mem hγq, inv_mem hγ0, this ▸ hτ'⟩
  have hT_C : ∀ τ : ↥K ≃ₐ[L] ↥K, τ ∈ Tset → ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j := by
    rintro τ ⟨γ, -, hγ0, hτ⟩ a ha
    exact hEQfin γ hγ0 τ hτ a ha
  have hT_Csymm : ∀ τ : ↥K ≃ₐ[L] ↥K, τ ∈ Tset → ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ.symm a ∈ chartAlgFin A (↥K) j := by
    intro τ hτ a ha
    have := hT_C τ⁻¹ (hT_inv τ hτ) a ha
    rwa [AlgEquiv.aut_inv] at this

  let res : ∀ τ : ↥K ≃ₐ[L] ↥K, τ ∈ Tset → (↥(chartAlgFin A (↥K) j) →+* ↥(chartAlgFin A (↥K) j)) :=
    fun τ hτ => (τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) (hT_C τ hτ)
  have hres_apply : ∀ (τ : ↥K ≃ₐ[L] ↥K) (hτ : τ ∈ Tset) (c : ↥(chartAlgFin A (↥K) j)),
      ((res τ hτ c : ↥(chartAlgFin A (↥K) j)) : ↥K) = τ (c : ↥K) := fun τ hτ c => rfl
  have hres_surj : ∀ (τ : ↥K ≃ₐ[L] ↥K) (hτ : τ ∈ Tset), Function.Surjective (res τ hτ) := by
    intro τ hτ c
    refine ⟨⟨τ.symm (c : ↥K), hT_Csymm τ hτ _ c.2⟩, Subtype.ext ?_⟩
    rw [hres_apply τ hτ]; simp

  obtain ⟨n, hn1, hrad⟩ := hRad

  let Jy : Ideal ↥(chartAlgFin A (↥K) j) := Ideal.comap
    ((e₁ : (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) →+*
        (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})).comp
      ((algebraMap _ _).comp
        (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom))))
    (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}) (MvPowerSeries.C (σ₁ ϖt)),
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}) (MvPowerSeries.X 0),
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}) (MvPowerSeries.X 1)})
  have hrad' : ∀ a : ↥(chartAlgFin A (↥K) j), a ∈ y → a ^ n ∈ Jy := by
    intro a ha
    have h := hrad a ha
    rw [← map_pow] at h
    exact Ideal.mem_comap.mpr h
  have hJle : ∀ (σ : ↥K ≃ₐ[L] ↥K) (hσ : σ ∈ Tset), J ≤ Jy.comap (res σ hσ) := by
    intro σ hσ
    have hJ' := hJ
    dsimp only at hJ'
    rw [hJ']
    obtain ⟨γ, hγq, hγ0, hσ'⟩ := hσ
    exact sInf_le ⟨γ, hγq, hγ0, σ, hσ', hT_C σ ⟨γ, hγq, hγ0, hσ'⟩, rfl⟩

  have hymax : ∀ (σ : ↥K ≃ₐ[L] ↥K) (hσ : σ ∈ Tset), (y.comap (res σ hσ)).IsMaximal := by
    intro σ hσ
    haveI := hy
    exact Ideal.comap_isMaximal_of_surjective _ (hres_surj σ hσ)

  intro y'' hy'' hϖy'' hnot

  let Qτ : ∀ τ : ↥K ≃ₐ[L] ↥K, Ideal ↥(chartAlgFin A (↥K) j) := fun τ =>
    Ideal.span {c | ∃ d : ↥(chartAlgFin A (↥K) j), d ∈ y'' ∧ (c : ↥K) = τ (d : ↥K)}
  have hJQ : ∀ τ : ↥K ≃ₐ[L] ↥K, τ ∈ Tset → J ⊔ Qτ τ = ⊤ := by
    intro τ hτ
    by_contra hne
    obtain ⟨P, hPmax, hPge⟩ := Ideal.exists_le_maximal _ hne
    have hJP : J ≤ P := le_sup_left.trans hPge
    have hQP : Qτ τ ≤ P := le_sup_right.trans hPge

    have hJ' := hJ
    dsimp only at hJ'
    have hJge : ∀ x : ↥(chartAlgFin A (↥K) j),
        (∀ (σ : ↥K ≃ₐ[L] ↥K) (hσ : σ ∈ Tset), x ∈ Jy.comap (res σ hσ)) → x ∈ J := by
      intro x hx
      rw [hJ', Ideal.mem_sInf]
      rintro J' ⟨γ, hγq, hγ0, τ, hτ, hpres, rfl⟩
      have := hx τ ⟨γ, hγq, hγ0, hτ⟩
      rw [Ideal.mem_comap] at this ⊢
      exact this
    let resT : (↥K ≃ₐ[L] ↥K) → (↥(chartAlgFin A (↥K) j) →+* ↥(chartAlgFin A (↥K) j)) := fun τ =>
      if hτ : τ ∈ Tset then res τ hτ else RingHom.id _
    have hresT : ∀ (τ : ↥K ≃ₐ[L] ↥K) (hτ : τ ∈ Tset), resT τ = res τ hτ := fun τ hτ => dif_pos hτ
    have hprod : (hTfin.toFinset.prod fun σ => Jy.comap (resT σ)) ≤ P := by
      intro x hx
      apply hJP
      apply hJge
      intro σ hσ
      have h1 : x ∈ hTfin.toFinset.inf fun σ => Jy.comap (resT σ) := Ideal.prod_le_inf hx
      have h2 := (Finset.inf_le (hTfin.mem_toFinset.mpr hσ) :
        (hTfin.toFinset.inf fun σ => Jy.comap (resT σ)) ≤ Jy.comap (resT σ)) h1
      rwa [hresT σ hσ] at h2
    obtain ⟨σ, hσmem, hσP⟩ := (Ideal.IsPrime.prod_le hPmax.isPrime).mp hprod
    have hσ : σ ∈ Tset := hTfin.mem_toFinset.mp hσmem
    rw [hresT σ hσ] at hσP

    have hyP : y.comap (res σ hσ) ≤ P := by
      intro a ha
      rw [Ideal.mem_comap] at ha
      have : a ^ n ∈ Jy.comap (res σ hσ) := by
        rw [Ideal.mem_comap, RingHom.map_pow (res σ hσ) a n]; exact hrad' _ ha
      exact hPmax.isPrime.mem_of_pow_mem n (hσP this)
    have hPeq : y.comap (res σ hσ) = P := (hymax σ hσ).eq_of_le hPmax.ne_top hyP

    have hστ : σ * τ ∈ Tset := hT_mul σ τ hσ hτ
    have hy''le : y'' ≤ y.comap (res (σ * τ) hστ) := by
      intro d hd
      rw [Ideal.mem_comap]
      have hmem : (⟨τ (d : ↥K), hT_C τ hτ _ d.2⟩ : ↥(chartAlgFin A (↥K) j)) ∈ Qτ τ :=
        Ideal.subset_span ⟨d, hd, rfl⟩
      have := hQP hmem
      rw [← hPeq, Ideal.mem_comap] at this
      convert this using 1 <;> rfl
    have hy''eq : y'' = y.comap (res (σ * τ) hστ) :=
      hy''.eq_of_le (Ideal.comap_ne_top _ hy.ne_top) hy''le

    obtain ⟨γρ, hγρq, hγρ0, hρ⟩ := hT_inv _ hστ
    apply hnot γρ hγρq hγρ0 (σ * τ)⁻¹ hρ
    intro b hb
    rw [hy''eq, Ideal.mem_comap]
    have : res (σ * τ) hστ ⟨(σ * τ)⁻¹ (b : ↥K), hb⟩ = b := by
      apply Subtype.ext
      rw [hres_apply _ hστ]
      show (σ * τ) ((σ * τ)⁻¹ (b : ↥K)) = b
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [this]

  have hsup : J ⊔ (⨅ τ ∈ hTfin.toFinset, Qτ τ) = ⊤ :=
    Ideal.sup_iInf_eq_top (fun τ hτ => hJQ τ (hTfin.mem_toFinset.mp hτ))
  have h1 : (1 : ↥(chartAlgFin A (↥K) j)) ∈ J ⊔ (⨅ τ ∈ hTfin.toFinset, Qτ τ) := by rw [hsup]; trivial
  obtain ⟨i, hiJ, w, hw, hiw⟩ := Submodule.mem_sup.mp h1
  let b : ↥K := (i : ↥K) * (algebraMap A ↥K ϖt)⁻¹
  have hbϖt : b * algebraMap A ↥K ϖt = (i : ↥K) := by
    simp only [b]; field_simp
  refine ⟨b, ?_, ?_⟩
  · rw [hB, Subalgebra.mem_restrictScalars]
    exact Algebra.subset_adjoin ⟨i, hiJ, hbϖt⟩
  intro γ hγq hγ0 τ hτ V hCV hcen hbV
  have hτT : τ ∈ Tset := ⟨γ, hγq, hγ0, hτ⟩

  let v := V.valuation
  have hv_le : ∀ x : ↥K, x ∈ V → v x ≤ 1 := fun x hx => (V.valuation_le_one_iff x).mpr hx
  have hv_lt : ∀ (x : ↥K) (hx : x ∈ V), (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V → v x < 1 := fun x hx hm =>
    (V.valuation_lt_one_iff ⟨x, hx⟩).mp hm
  have hAV : ∀ a : A, algebraMap A ↥K a ∈ V := fun a => hCV (algebraMap A _ a)

  have hϖV : v (algebraMap A ↥K ϖ) < 1 := by
    have hfixϖ : τ.symm (algebraMap A ↥K ϖ) = algebraMap A ↥K ϖ := by
      rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
    have hc : τ.symm ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖ : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ chartAlgFin A (↥K) j := by
      rw [show ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖ : ↥(chartAlgFin A (↥K) j)) : ↥K) = algebraMap A ↥K ϖ from rfl,
        hfixϖ]
      exact (algebraMap A ↥(chartAlgFin A (↥K) j) ϖ).2
    have := hcen (algebraMap A _ ϖ) hc (by
      convert hϖy'' using 1
      apply Subtype.ext
      exact hfixϖ) (hAV ϖ)
    exact hv_lt _ _ this
  have hvϖt : v (algebraMap A ↥K ϖt) < 1 := by
    rw [ha', map_mul, map_mul]
    calc v (algebraMap A ↥K ϖ) * v (algebraMap A ↥K a') ≤ v (algebraMap A ↥K ϖ) * 1 :=
          mul_le_mul_right (hv_le _ (hAV a')) _
      _ < 1 := by rw [mul_one]; exact hϖV
  have hvi : v (i : ↥K) < 1 := by
    rw [← hbϖt, map_mul]
    calc v b * v (algebraMap A ↥K ϖt) ≤ 1 * v (algebraMap A ↥K ϖt) := mul_le_mul_left (hv_le _ hbV) _
      _ < 1 := by rw [one_mul]; exact hvϖt

  let ιCV : ↥(chartAlgFin A (↥K) j) →+* ↥V := ((chartAlgFin A (↥K) j).val : _ →+* ↥K).codRestrict V (fun c => hCV c)
  have hQle : Qτ τ ≤ (maximalIdeal ↥V).comap ιCV := by
    apply Ideal.span_le.mpr
    rintro c ⟨d, hd, hcd⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    have hc : τ.symm (c : ↥K) ∈ chartAlgFin A (↥K) j := by
      rw [hcd, AlgEquiv.symm_apply_apply]; exact d.2
    have := hcen c hc (by
      convert hd using 1
      apply Subtype.ext
      show τ.symm (c : ↥K) = d
      rw [hcd, AlgEquiv.symm_apply_apply]) (hCV c)
    exact this
  have hwQ : w ∈ Qτ τ := by
    have := (Submodule.mem_iInf _).mp hw τ
    exact (Submodule.mem_iInf _).mp this (hTfin.mem_toFinset.mpr hτT)
  have hvw : v (w : ↥K) < 1 := hv_lt _ (hCV w) (hQle hwQ)
  have h1lt : v ((i : ↥K) + (w : ↥K)) < 1 := Valuation.map_add_lt v hvi hvw
  have : (i : ↥K) + (w : ↥K) = 1 := by
    rw [← Subalgebra.coe_add, hiw]; rfl
  rw [this, map_one] at h1lt
  exact lt_irrefl _ h1lt

end S_ModularCurve_FullLevel_AuxLevel_exists_mem_blowupChart_orbitPole_of_pow_mem_centre_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_mem_blowupChart_orbitPole_of_pow_mem_centre_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart (solution)
