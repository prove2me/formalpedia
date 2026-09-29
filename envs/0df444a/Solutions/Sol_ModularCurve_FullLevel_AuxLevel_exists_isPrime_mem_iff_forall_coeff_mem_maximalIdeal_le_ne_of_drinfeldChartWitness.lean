-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_isPrime_mem_iff_forall_coeff_mem_maximalIdeal_le_ne_of_drinfeldChartWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3f2edebe-4f96-524d-94d2-bb591b50af88

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
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin
import Theorems.Thm_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isPrime_mem_iff_forall_coeff_mem_maximalIdeal_le_ne_of_drinfeldChartWitness
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

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
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h)) :
    ∃ G : Ideal ↥(chartAlgFin A (↥K) j), G.IsPrime ∧
      (∀ a : ↥(chartAlgFin A (↥K) j), a ∈ G ↔ (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m)) ∧
      algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ G ∧ G ≤ y ∧ G ≠ y := by
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
    ModularCurve.FullLevel.AuxLevel.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hconst

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
  obtain ⟨hbr, -, -, -⟩ := DrinfeldCurve.LocalChart.branchPrimes_of_sub_drinfeldForm_mem_pow q W₁ (σ₁ ϖ) hσ₁ hqW
    (σ₁ (ϖt ^ (q + 1))) hc hc0 f₁ u₁ v₁ hu₁ hv₁ hf₁
  obtain ⟨P, hP, hPne, hπP, h, hh, hlinP⟩ := hbr 1 0 (by
    rintro ⟨h1, -⟩
    have : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have : 2 ≤ q := (Fact.out : q.Prime).two_le
    omega)
  have hlinP' : ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
      mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P :=
    ⟨h, hh, by simpa only [Int.cast_one, Int.cast_zero] using hlinP⟩

  have hP𝔐 : P ≤ 𝔐 := by
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    rw [huniq M hM] at hPM
    exact hPM

  haveI : P.IsPrime := hP
  refine ⟨Ideal.comap Ψ P, Ideal.comap_isPrime Ψ P, ?_, ?_, ?_, ?_⟩
  · intro a
    exact (hanch P hP hPne hπP hlinP' a)
  · show Ψ (algebraMap A ↥(chartAlgFin A (↥K) j) ϖ) ∈ P
    rw [hΨconst ϖ]
    exact hπP
  · calc Ideal.comap Ψ P ≤ Ideal.comap Ψ 𝔐 := Ideal.comap_mono hP𝔐
      _ = y := hcen
  · intro hGy

    haveI : IsLocalRing S := IsLocalRing.of_unique_max_ideal ⟨𝔐, hmax, fun M hM => huniq M hM⟩
    have hXmem : ∀ i : Fin 2, mkS (MvPowerSeries.X i) ∈ P ⊔ 𝔐 • 𝔐 := by
      intro i
      have hXi : mkS (MvPowerSeries.X i) ∈ 𝔐 := by
        fin_cases i
        · exact Ideal.subset_span (by simp)
        · exact Ideal.subset_span (by simp)
      obtain ⟨a, ha⟩ := hdense 2 (mkS (MvPowerSeries.X i))
      have hΨa𝔐 : Ψ a ∈ 𝔐 := by
        have : Ψ a = (Ψ a - mkS (MvPowerSeries.X i)) + mkS (MvPowerSeries.X i) := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.pow_le_self (by norm_num) ha) hXi
      have haY : a ∈ y := by rw [← hcen]; exact hΨa𝔐
      have haP : Ψ a ∈ P := by rw [← hGy] at haY; exact haY
      have : mkS (MvPowerSeries.X i) = Ψ a - (Ψ a - mkS (MvPowerSeries.X i)) := by ring
      rw [this]
      refine Ideal.sub_mem _ (Ideal.mem_sup_left haP) (Ideal.mem_sup_right ?_)
      have h22 : 𝔐 ^ 2 = 𝔐 * 𝔐 := pow_two 𝔐
      rw [Ideal.smul_eq_mul, ← h22]
      exact ha
    have h𝔐le : 𝔐 ≤ P ⊔ 𝔐 • 𝔐 := by
      refine Ideal.span_le.mpr ?_
      rintro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · exact Ideal.mem_sup_left hπP
      · exact hXmem 0
      · exact hXmem 1
    have hfg : (𝔐 : Submodule S S).FG := Submodule.fg_span (Set.toFinite _)
    have hjac : 𝔐 ≤ Ideal.jacobson (⊥ : Ideal S) := by
      have h1 : IsLocalRing.maximalIdeal S ≤ Ideal.jacobson (⊥ : Ideal S) := IsLocalRing.maximalIdeal_le_jacobson ⊥
      have h2 : 𝔐 = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hmax
      exact h2.le.trans h1
    have h𝔐P : 𝔐 ≤ P := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac h𝔐le
    rcases hPne with h0 | h1
    · exact h0 (h𝔐P (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
    · exact h1 (h𝔐P (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))

end S_ModularCurve_FullLevel_AuxLevel_exists_isPrime_mem_iff_forall_coeff_mem_maximalIdeal_le_ne_of_drinfeldChartWitness
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isPrime_mem_iff_forall_coeff_mem_maximalIdeal_le_ne_of_drinfeldChartWitness (solution)
