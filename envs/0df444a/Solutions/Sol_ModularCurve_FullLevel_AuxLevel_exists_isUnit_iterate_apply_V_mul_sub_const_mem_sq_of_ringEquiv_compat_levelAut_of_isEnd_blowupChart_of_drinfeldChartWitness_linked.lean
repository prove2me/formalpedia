-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_isUnit_iterate_apply_V_mul_sub_const_mem_sq_of_ringEquiv_compat_levelAut_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/fd4386b4-4f52-5e90-9354-29e7b5c2f77d

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
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isUnit_iterate_apply_V_mul_sub_const_mem_sq_of_ringEquiv_compat_levelAut_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace RingHom p2m_export "RingHom" "restrict FormallySmooth coe_restrict_apply ext mk ker id range comp FinitePresentation" end RingHom
p2m_open_scoped "RingHom" in

private theorem RingHom.eqOn_of_dense {S T : Type} [CommRing S] [CommRing T] (I : Ideal S) (J : Ideal T)
    (g₁ g₂ : S →+* T) (h₁ : ∀ (N : ℕ) (s : S), s ∈ I ^ N → g₁ s ∈ J ^ N)
    (h₂ : ∀ (N : ℕ) (s : S), s ∈ I ^ N → g₂ s ∈ J ^ N)
    (hJ : ∀ t : T, (∀ N : ℕ, t ∈ J ^ N) → t = 0) {X : Type} (ψ : X → S)
    (hD : ∀ (N : ℕ) (s : S), ∃ x : X, ψ x - s ∈ I ^ N) (hg : ∀ x : X, g₁ (ψ x) = g₂ (ψ x)) :
    ∀ s : S, g₁ s = g₂ s := by
  intro s
  apply eq_of_sub_eq_zero
  apply hJ
  intro N
  obtain ⟨d, hds⟩ := hD N s
  have h : g₁ s - g₂ s = g₂ (ψ d - s) - g₁ (ψ d - s) := by
    rw [map_sub, map_sub, hg d]; ring
  rw [h]
  exact Ideal.sub_mem _ (h₂ N _ hds) (h₁ N _ hds)

namespace RingEquiv p2m_export "RingEquiv" "restrict mk toRingHom finite ext" end RingEquiv
p2m_open_scoped "RingEquiv" in

private theorem RingEquiv.mem_maximalIdeal_pow_of_mem {R : Type} [CommRing R] [IsLocalRing R] (e : R ≃+* R)
    (N : ℕ) (x : R) (hx : x ∈ (IsLocalRing.maximalIdeal R) ^ N) : e x ∈ (IsLocalRing.maximalIdeal R) ^ N := by
  have hmap : Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  have := Ideal.mem_map_of_mem e hx
  rwa [Ideal.map_pow, hmap] at this

p2m_open_scoped "RingEquiv" in

private theorem RingEquiv.mem_maximalIdeal_pow_map {R T : Type} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
    (e : R ≃+* T) (N : ℕ) (x : R) (hx : x ∈ (IsLocalRing.maximalIdeal R) ^ N) : e x ∈ (IsLocalRing.maximalIdeal T) ^ N := by
  have hmap : Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal T :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  have := Ideal.mem_map_of_mem e hx
  rwa [Ideal.map_pow, hmap] at this

p2m_open_scoped "RingEquiv" in

private theorem RingEquiv.mem_pow_of_mem_of_unique_maximal {S : Type} [CommRing S] (e : S ≃+* S) (M : Ideal S)
    (hM : M.IsMaximal) (huniq : ∀ I : Ideal S, I.IsMaximal → I = M)
    (N : ℕ) (x : S) (hx : x ∈ M ^ N) : e x ∈ M ^ N := by
  haveI := hM
  have hmap : Ideal.map e M = M := huniq _ (Ideal.map_isMaximal_of_equiv e)
  have := Ideal.mem_map_of_mem e hx
  rwa [Ideal.map_pow, hmap] at this

private theorem eq_zero_of_forall_mem_pow {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T]
    (t : T) (ht : ∀ N : ℕ, t ∈ J ^ N) : t = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff J T) t fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact ht N

namespace AdicCompletion p2m_export "AdicCompletion" "map mk of incl module ext algebraMap_apply mul_apply lift pi maximalIdeal_eq_map" end AdicCompletion
p2m_open_scoped "AdicCompletion" in

private theorem AdicCompletion.map_maximalIdeal_pow_eq' {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (N : ℕ) :
    ((IsLocalRing.maximalIdeal R).map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))) ^ N =
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ^ N := by
  rw [AdicCompletion.maximalIdeal_eq_map]

open ModularCurve ModularCurve.FullLevel in
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

    (n : ℕ) (hn1 : 1 ≤ n) (hnq : n ∣ q + 1)
    (γ₀ : SL(2, ℤ)) (hγ₀q : γ₀ ∈ CongruenceSubgroup.Gamma q) (hγ₀M : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (τ₀ : ↥K ≃ₐ[L] ↥K) (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ₀⁻¹ K τ₀)
    (hτ₀W : ∀ f : ↥K, f ∈ W ↔ τ₀ f ∈ W)
    (hcyc1 : ∀ f : ↥K, f ∈ B → (τ₀ ^ n) f = f)
    (hcyc2 : ∀ k : ℕ, 0 < k → k < n → ∃ f : ↥K, f ∈ B ∧ (τ₀ ^ k) f ≠ f)

    (m : ℕ) (hm1 : 1 ≤ m) (hmt : ∃ w : A, IsUnit w ∧ ϖ ^ m = ϖt * w)
    (O : Subring ↥K)
    (hO : (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
            let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
              {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
            ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
              (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
              (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
                ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
              ¬ (∀ f : ↥K, f ∈ B → f ∈ O)))
    (hOτ : ∀ f : ↥K, f ∈ O ↔ τ₀ f ∈ O) :
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
        ∀ (instM : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))

          (hOloc : IsLocalRing ↥O) (hOnoe : IsNoetherianRing ↥O)
          (hCO : ∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ O)

          (Λ : S →+* (AdicCompletion (maximalIdeal ↥O) ↥O))
          (hΛC : ∀ c : ↥(chartAlgFin A (↥K) j), Λ ((e₁ : CMP →+* S) (toC (germY c))) = algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨(c : ↥K), hCO c⟩)
          (hΛcont : ∀ (N : ℕ) (s : S), s ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ N →
            Λ s ∈ (Ideal.map (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O)) (maximalIdeal ↥O)) ^ N)

          (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
          (hιc : ∀ (a : A) (ha : algebraMap A ↥K a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a))

          (ρ : W₁ →+* (AdicCompletion (maximalIdeal A) A)) (p₀ p₁ : W₁) (α β : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
          (hρσ : ∀ a : A, ρ (σ₁ a) = algebraMap A (AdicCompletion (maximalIdeal A) A) a)
          (hρu : ∀ w : W₁, ¬ IsUnit w → ¬ IsUnit (ρ w))
          (hpdir : p₀ ∉ maximalIdeal W₁ ∨ p₁ ∉ maximalIdeal W₁)
          (hαp : ¬ IsUnit (α - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ p₀)))
          (hβp : ¬ IsUnit (β - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ p₁)))
          (hιX0 : ι (Λ (mkS (MvPowerSeries.X 0))) = UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * α)
          (hιX1 : ι (Λ (mkS (MvPowerSeries.X 1))) = UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * β)
          (hιCw : ∀ w : W₁, ι (Λ (mkS (MvPowerSeries.C w))) = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ w))

          (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
          (hθ₀ : ∀ (f : ↥K) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
            ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))),
        ∃ (b : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (_ : IsUnit b) (c : ℕ → (AdicCompletion (maximalIdeal A) A)),

          (∀ k : ℕ, 0 < k → k < n →
            (θ₀ ^ k) (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (c k) * (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) ∈
              (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ 2) ∧
          (∀ k : ℕ, 0 < k → k < n → IsUnit (c k - 1)) ∧

          (∀ (c' : W₁) (θ : S ≃+* S) (Mx : Matrix (Fin 2) (Fin 2) W₁)
              (hpres : ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ₀ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ₀ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) →
            (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) →
            (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                mkS (∑ ii : Fin 2, MvPowerSeries.C (Mx ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) →
            (∀ ii jj : Fin 2, Mx ii jj - c' * ((γ₀ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) →
            ∀ a : A, c' - σ₁ a ∈ IsLocalRing.maximalIdeal W₁ →
              θ₀ (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a) * (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ 2) := by
  intro STK CMP toC S mkS germY instM hOloc hOnoe hCO Λ hΛC hΛcont ι hιc ρ p₀ p₁ α β hρσ hρloc hpdir hαp hβp hιX0 hιX1 hιCw θ₀ hθ₀
  classical
  haveI := hOloc
  haveI := hOnoe

  have hW₁c := hW₁
  obtain ⟨hconst, hEQfin, -, hEQlin, -, -, -⟩ := hW₁c

  have hDENSE := ModularCurve.FullLevel.AuxLevel.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hconst
  obtain ⟨-, hdense, hΨA, hCAy, hWσ, hσcomap, hMmax, hMuniq, -⟩ := hDENSE

  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hAD := IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete A ϖ hirr
  obtain ⟨instDom, instDVR, instCpl, hirrhat, hisoA, hdensA⟩ := hAD
  have hmaxh : maximalIdeal (AdicCompletion (maximalIdeal A) A) = Ideal.span {(algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirrhat
  have hπu : ¬ IsUnit ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) := fun hu =>
    hirrhat.not_isUnit (isUnit_pow_iff (by omega) |>.mp hu)

  haveI iNM : IsNoetherianRing (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := ModularCurve.UVCrossingModel.isNoetherianRing _
  haveI iCM : IsAdicComplete (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) :=
    ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal _
  have hMmap : Ideal.map (UVCrossingModel.constHom ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) (maximalIdeal (AdicCompletion (maximalIdeal A) A)) ≤ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := by
    rw [ModularCurve.UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair hπu]; exact le_sup_left
  have hUVle : Ideal.span {UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m), UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)} ≤ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := by
    rw [ModularCurve.UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair hπu]; exact le_sup_right
  have hVmem : UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∈ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) :=
    hUVle (Ideal.subset_span (by simp))
  have hUmem : UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∈ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) :=
    hUVle (Ideal.subset_span (by simp))
  have hconstmax : ∀ w : (AdicCompletion (maximalIdeal A) A), w ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) →
      UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) w ∈ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := fun w hw =>
    hMmap (Ideal.mem_map_of_mem _ hw)

  have hτkA : ∀ (k : ℕ) (a : A), (τ₀ ^ k) (algebraMap A ↥K a) = algebraMap A ↥K a := fun k a => by
    rw [IsScalarTower.algebraMap_apply A L ↥K]; exact (τ₀ ^ k).commutes _
  have hτkW : ∀ (k : ℕ) (f : ↥K), f ∈ W ↔ (τ₀ ^ k) f ∈ W := by
    intro k; induction k with
    | zero => intro f; simp
    | succ k ih => intro f; rw [pow_succ', AlgEquiv.mul_apply, ← hτ₀W]; exact ih f
  have hτkO : ∀ (k : ℕ) (f : ↥K), f ∈ O ↔ (τ₀ ^ k) f ∈ O := by
    intro k; induction k with
    | zero => intro f; simp
    | succ k ih => intro f; rw [pow_succ', AlgEquiv.mul_apply, ← hOτ]; exact ih f
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
  have hWmax_iff : ∀ (x : ↥K) (hx : x ∈ W), (⟨x, hx⟩ : ↥W) ∈ maximalIdeal ↥W ↔ ¬ (x ≠ 0 ∧ x⁻¹ ∈ W) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, unitK W x hx]
  have hτkmax : ∀ (k : ℕ) (x : ↥K) (hx : x ∈ W) (hx' : (τ₀ ^ k) x ∈ W),
      (⟨x, hx⟩ : ↥W) ∈ maximalIdeal ↥W ↔ (⟨(τ₀ ^ k) x, hx'⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro k x hx hx'
    rw [hWmax_iff, hWmax_iff]
    refine not_congr (and_congr ?_ ?_)
    · rw [ne_eq, ne_eq, map_eq_zero_iff _ (τ₀ ^ k).injective]
    · rw [← map_inv₀]; exact hτkW k _
  have hpresk : ∀ k : ℕ, ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) → (τ₀ ^ k) a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := by
    intro k; induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih => intro a ha; rw [pow_succ', AlgEquiv.mul_apply]; exact hEQfin γ₀ hγ₀M τ₀ hτ₀ _ (ih a ha)

  have hfixk : ∀ (k : ℕ) (a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
      ((((τ₀ ^ k : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (hpresk k)) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal := by
    intro k a
    rw [hy'y]
    obtain ⟨α', hα'⟩ := hCAy a
    set b : ↥(chartAlgFin A (↥K) j) := a - algebraMap A ↥(chartAlgFin A (↥K) j) α' with hb
    have hyW := hR3.2.2.2.1
    obtain ⟨hbW, hbm⟩ := (hyW b).mp hα'
    have hτb : (τ₀ ^ k) (b : ↥K) ∈ W := (hτkW k _).mp hbW
    have hτbC : (τ₀ ^ k) (b : ↥K) ∈ chartAlgFin A (↥K) j := hpresk k _ b.2
    have hτby : (⟨(τ₀ ^ k) (b : ↥K), hτbC⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y :=
      (hyW _).mpr ⟨hτb, (hτkmax k _ hbW hτb).mp hbm⟩
    have ha' : a = b + algebraMap A ↥(chartAlgFin A (↥K) j) α' := by rw [hb, sub_add_cancel]
    have hτα : (((τ₀ ^ k : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (hpresk k)) (algebraMap A ↥(chartAlgFin A (↥K) j) α')
        = algebraMap A ↥(chartAlgFin A (↥K) j) α' := by
      apply Subtype.ext
      rw [RingHom.coe_restrict_apply, Subalgebra.coe_algebraMap]
      exact hτkA k α'
    have hτb' : (((τ₀ ^ k : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (hpresk k)) b
        = (⟨(τ₀ ^ k) (b : ↥K), hτbC⟩ : ↥(chartAlgFin A (↥K) j)) := Subtype.ext rfl
    rw [ha', map_add, hτα, add_sub_add_right_eq_sub, hτb']
    exact Ideal.sub_mem _ hτby hα'

  have hLAC := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  obtain ⟨-, hmulLA, -⟩ := hLAC
  have hτkLA : ∀ k : ℕ, 1 ≤ k → ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') (γ₀ ^ k)⁻¹ K (τ₀ ^ k) := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; simpa using hτ₀
      · have ih' := ih (by omega)
        have := hmulLA γ₀⁻¹ (γ₀ ^ k)⁻¹ (inv_mem hγ₀M) (inv_mem (pow_mem hγ₀M k)) τ₀ (τ₀ ^ k) hτ₀ ih'
        rwa [← mul_inv_rev, ← pow_succ', ← pow_succ'] at this

  have hpow_succ : ∀ (k : ℕ) (x : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))), (θ₀ ^ (k + 1)) x = θ₀ ((θ₀ ^ k) x) := by
    intro k x; rw [pow_succ']; rfl
  have hθk : ∀ (k : ℕ) (f : ↥K) (hf : f ∈ O) (hf' : (τ₀ ^ k) f ∈ O),
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = (θ₀ ^ k) (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩)) := by
    intro k
    induction k with
    | zero =>
      intro f hf hf'
      have e : (⟨(τ₀ ^ 0) f, hf'⟩ : ↥O) = ⟨f, hf⟩ := Subtype.ext (by simp)
      rw [e, pow_zero]; rfl
    | succ k ih =>
      intro f hf hf'
      have hfk : (τ₀ ^ k) f ∈ O := (hτkO k f).mp hf
      have hfk' : τ₀ ((τ₀ ^ k) f) ∈ O := (hOτ _).mp hfk
      have e : (⟨(τ₀ ^ (k + 1)) f, hf'⟩ : ↥O) = ⟨τ₀ ((τ₀ ^ k) f), hfk'⟩ := Subtype.ext (by show (τ₀ ^ (k + 1)) f = τ₀ ((τ₀ ^ k) f); rw [pow_succ', AlgEquiv.mul_apply])
      rw [e, hpow_succ, hθ₀ _ hfk hfk', ih f hf hfk]

  obtain ⟨Φ, hΦ⟩ : ∃ Φ : S →+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)), ∀ s, Φ s = ι (Λ s) := ⟨(ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))).toRingHom.comp Λ, fun _ => rfl⟩
  have hΦcont : ∀ (N : ℕ) (s : S), s ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ N → Φ s ∈ (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ N := by
    intro N s hs
    rw [hΦ]
    refine RingEquiv.mem_maximalIdeal_pow_map ι N _ ?_
    exact (AdicCompletion.map_maximalIdeal_pow_eq' (R := ↥O) N).le (hΛcont N s hs)
  have hsepM : ∀ t : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)), (∀ N : ℕ, t ∈ (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ N) → t = 0 :=
    fun t ht => eq_zero_of_forall_mem_pow _ t ht

  have hEQV : ∀ (k : ℕ) (θ : S ≃+* S) (tC : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) → ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
      (htC : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), ((tC a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = (τ₀ ^ k) ((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K))
      (hcompat : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), θ (e₁ (toC (germY a))) = e₁ (toC (germY (tC a)))),
      ∀ s : S, Φ (θ s) = (θ₀ ^ k) (Φ s) := by
    intro k θ tC htC hcompat
    refine RingHom.eqOn_of_dense (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
      (Φ.comp θ.toRingHom) ((θ₀ ^ k).toRingHom.comp Φ) ?_ ?_ hsepM
      (fun a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) => (e₁ : CMP →+* S) (toC (germY a))) (fun N s => hdense N s) ?_
    · intro N s hs
      exact hΦcont N _ (RingEquiv.mem_pow_of_mem_of_unique_maximal θ _ hMmax hMuniq N s hs)
    · intro N s hs
      exact RingEquiv.mem_maximalIdeal_pow_of_mem (θ₀ ^ k) N _ (hΦcont N s hs)
    · intro a
      show Φ (θ (e₁ (toC (germY a)))) = (θ₀ ^ k) (Φ ((e₁ : CMP →+* S) (toC (germY a))))
      have h1 : Φ ((e₁ : CMP →+* S) (toC (germY (tC a)))) = ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨((tC a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K), hCO _⟩) := by
        rw [hΦ, hΛC]
      have h2 : Φ ((e₁ : CMP →+* S) (toC (germY a))) = ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K), hCO _⟩) := by
        rw [hΦ, hΛC]
      have hmem' : (τ₀ ^ k) ((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) ∈ O := (hτkO k _).mp (hCO a)
      have e3 : (⟨((tC a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K), hCO _⟩ : ↥O) = ⟨(τ₀ ^ k) ((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K), hmem'⟩ := Subtype.ext (htC a)
      rw [hcompat a]
      show Φ ((e₁ : CMP →+* S) (toC (germY (tC a)))) = _
      rw [h1, h2, e3, hθk k _ (hCO a) hmem']

  have hunit_of : ∀ (x : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (w : W₁), IsUnit w → ¬ IsUnit (x - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ w)) → IsUnit x := by
    intro x w hw hx
    by_contra hxu
    have h1 : x ∈ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := (IsLocalRing.mem_maximalIdeal _).mpr hxu
    have h2 : x - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ w) ∈ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := (IsLocalRing.mem_maximalIdeal _).mpr hx
    have h3 : UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ w) ∈ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := by
      have := sub_mem h1 h2; rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp h3 (by rw [show UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ w) = UVCrossingModel.constHom ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ w) from rfl]; exact (hw.map ρ).map _)
  obtain ⟨jb, b, hb, hΦXb⟩ : ∃ (jb : Fin 2) (b : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))), IsUnit b ∧ Φ (mkS (MvPowerSeries.X jb)) = UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b := by
    rcases hpdir with h0 | h1
    · refine ⟨0, α, hunit_of α p₀ ?_ hαp, by rw [hΦ, hιX0]⟩
      exact (IsLocalRing.mem_maximalIdeal _).not.mp h0 |> fun h => by rwa [mem_nonunits_iff, not_not] at h
    · refine ⟨1, β, hunit_of β p₁ ?_ hβp, by rw [hΦ, hιX1]⟩
      exact (IsLocalRing.mem_maximalIdeal _).not.mp h1 |> fun h => by rwa [mem_nonunits_iff, not_not] at h

  have hqW : ((q : ℕ) : W₁) ∈ maximalIdeal W₁ := by
    have : σ₁ (q : A) ∈ maximalIdeal W₁ := by
      rw [← Ideal.mem_comap, hσcomap]; exact hAq
    rwa [map_natCast] at this
  have hdvd0 : ∀ a : ℤ, ((a : ℤ) : ZMod q) = 0 → ((a : ℤ) : W₁) ∈ maximalIdeal W₁ := by
    intro a ha
    obtain ⟨t, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a q).mp ha
    rw [Int.cast_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ hqW
  have hdvd1 : ∀ a : ℤ, ((a : ℤ) : ZMod q) = 1 → ((a : ℤ) : W₁) - 1 ∈ maximalIdeal W₁ := by
    intro a ha
    have h' : (((a - 1 : ℤ)) : ZMod q) = 0 := by rw [Int.cast_sub, Int.cast_one, ha, sub_self]
    have := hdvd0 _ h'
    rwa [Int.cast_sub, Int.cast_one] at this
  have hΓ1 : ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma q →
      ∀ ii jj : Fin 2, ((γ ii jj : ℤ) : W₁) - (if ii = jj then 1 else 0) ∈ maximalIdeal W₁ := by
    intro γ hγ ii jj
    have h := CongruenceSubgroup.Gamma_mem.mp hγ
    obtain ⟨h00, h01, h10, h11⟩ := h
    fin_cases ii <;> fin_cases jj
    · simpa using hdvd1 _ h00
    · simpa using hdvd0 _ h01
    · simpa using hdvd0 _ h10
    · simpa using hdvd1 _ h11

  have hXmem : ∀ ii : Fin 2, mkS (MvPowerSeries.X ii) ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) := by
    intro ii; fin_cases ii
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
  have hπmem : mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) := Ideal.subset_span (by simp)
  have hCX : ∀ (w : W₁) (ii : Fin 2), w ∈ maximalIdeal W₁ → mkS (MvPowerSeries.C w) * mkS (MvPowerSeries.X ii) ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2 := by
    intro w ii hw
    rw [hσ₁, Ideal.mem_span_singleton] at hw
    obtain ⟨w', rfl⟩ := hw
    rw [map_mul, map_mul, mul_assoc, mul_comm (mkS (MvPowerSeries.C w')), ← mul_assoc, pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hπmem (hXmem ii))
  have hX2le : (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2 ≤ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2 := by
    refine Ideal.pow_right_mono ?_ 2
    refine Ideal.span_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

  have hCORE : ∀ (k : ℕ) (θ : S ≃+* S) (tC : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) → ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
      (htC : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), ((tC a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = (τ₀ ^ k) ((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K))
      (hcompat : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), θ (e₁ (toC (germY a))) = e₁ (toC (germY (tC a))))
      (c' : W₁) (Mx : Matrix (Fin 2) (Fin 2) W₁) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma q)
      (hlin : ∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
          mkS (∑ ii : Fin 2, MvPowerSeries.C (Mx ii jj) * MvPowerSeries.X ii) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2)
      (hMc : ∀ ii jj : Fin 2, Mx ii jj - c' * ((γ ii jj : ℤ) : W₁) ∈ maximalIdeal W₁),
      (θ₀ ^ k) (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ c') * (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) ∈ (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ 2 := by
    intro k θ tC htC hcompat c' Mx γ hγ hlin hMc

    have hcol : ∀ ii : Fin 2, Mx ii jb - c' * (if ii = jb then 1 else 0) ∈ maximalIdeal W₁ := by
      intro ii
      have h1 := hMc ii jb
      have h2 := Ideal.mul_mem_left _ c' (hΓ1 γ hγ ii jb)
      have : Mx ii jb - c' * (if ii = jb then 1 else 0) =
          (Mx ii jb - c' * ((γ ii jb : ℤ) : W₁)) + c' * (((γ ii jb : ℤ) : W₁) - (if ii = jb then 1 else 0)) := by ring
      rw [this]; exact add_mem h1 h2

    have hsum : mkS (∑ ii : Fin 2, MvPowerSeries.C (Mx ii jb) * MvPowerSeries.X ii) - mkS (MvPowerSeries.C c') * mkS (MvPowerSeries.X jb) =
        ∑ ii : Fin 2, mkS (MvPowerSeries.C (Mx ii jb - c' * (if ii = jb then 1 else 0))) * mkS (MvPowerSeries.X ii) := by
      have hsingle : mkS (MvPowerSeries.C c') * mkS (MvPowerSeries.X jb) =
          ∑ ii : Fin 2, mkS (MvPowerSeries.C (c' * (if ii = jb then 1 else 0))) * mkS (MvPowerSeries.X ii) := by
        rw [Finset.sum_eq_single jb]
        · simp
        · intro ii _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ jb) h
      rw [hsingle, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ii _ => ?_
      rw [map_mul, map_sub (MvPowerSeries.C (σ := Fin 2) (R := W₁)), map_sub, sub_mul]
    have hS : θ (mkS (MvPowerSeries.X jb)) - mkS (MvPowerSeries.C c') * mkS (MvPowerSeries.X jb) ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2 := by
      have : θ (mkS (MvPowerSeries.X jb)) - mkS (MvPowerSeries.C c') * mkS (MvPowerSeries.X jb) =
          (θ (mkS (MvPowerSeries.X jb)) - mkS (∑ ii : Fin 2, MvPowerSeries.C (Mx ii jb) * MvPowerSeries.X ii)) +
          (mkS (∑ ii : Fin 2, MvPowerSeries.C (Mx ii jb) * MvPowerSeries.X ii) - mkS (MvPowerSeries.C c') * mkS (MvPowerSeries.X jb)) := by ring
      rw [this]
      refine add_mem (hX2le (hlin jb)) ?_
      rw [hsum]
      exact Ideal.sum_mem _ fun ii _ => hCX _ ii (hcol ii)

    have h1 := hΦcont 2 _ hS
    rw [map_sub, map_mul, hEQV k θ tC htC hcompat, hΦXb] at h1
    have hC' : Φ (mkS (MvPowerSeries.C c')) = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ c') := by rw [hΦ, hιCw]
    rwa [hC'] at h1

  have hK : ∀ k : ℕ, ∃ ck : W₁, (0 < k → k < n →
      ((θ₀ ^ k) (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ ck) * (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) ∈ (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ 2 ∧
       IsUnit (ρ ck - 1))) := by
    intro k
    by_cases hk : 0 < k ∧ k < n
    · obtain ⟨hk0, hkn⟩ := hk
      obtain ⟨θk, ck, Mk, hcompk, -, hlink, -, hMck, -, hfaithk⟩ :=
        hEQlin (γ₀ ^ k) (pow_mem hγ₀M k) (τ₀ ^ k) (hτkLA k hk0) (hpresk k) (hfixk k)
      refine ⟨ck, fun _ _ => ⟨?_, ?_⟩⟩
      · exact hCORE k θk (fun a => ((((τ₀ ^ k : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
            (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (hpresk k)) a)) (fun a => rfl) hcompk ck Mk (γ₀ ^ k) (pow_mem hγ₀q k) hlink hMck
      · have hne : ¬ ∀ x : ↥K, (τ₀ ^ k) x = x := by
          obtain ⟨f, -, hf⟩ := hcyc2 k hk0 hkn
          exact fun h => hf (h f)
        have h1 : ck - 1 ∉ maximalIdeal W₁ := hfaithk (pow_mem hγ₀q k) hne
        have h2 : IsUnit (ck - 1) := by
          rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h1
        have := h2.map ρ
        rwa [map_sub, map_one] at this
    · exact ⟨1, fun h0 hn => absurd (And.intro h0 hn) hk⟩
  choose cW hcW using hK
  refine ⟨b, hb, fun k => ρ (cW k), ?_, ?_, ?_⟩
  · intro k hk hkn; exact (hcW k hk hkn).1
  · intro k hk hkn; exact (hcW k hk hkn).2
  ·
    intro c' θ Mx hpres hcompat hlinW hlin hMc a hca
    have h1 := hCORE 1 θ (fun x => (((τ₀ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
        (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) x)) (fun x => by rw [pow_one]; rfl) hcompat c' Mx γ₀ hγ₀q hlin
        (by intro ii jj; simpa using hMc ii jj)
    rw [pow_one] at h1

    have h2 : UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ c') - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a) ∈ maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := by
      have e : UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ c') - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
          UVCrossingModel.constHom ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ (c' - σ₁ a)) := by
        rw [map_sub, map_sub, hρσ a]; rfl
      rw [e]
      refine hconstmax _ ((IsLocalRing.mem_maximalIdeal _).mpr (hρloc _ ?_))
      exact (IsLocalRing.mem_maximalIdeal _).mp hca
    have : θ₀ (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a) * (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) =
        (θ₀ (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ c') * (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b)) +
        (UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (ρ c') - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) * (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) := by ring
    rw [this]
    refine add_mem h1 ?_
    rw [pow_two, ← mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul h2 hVmem)

end S_ModularCurve_FullLevel_AuxLevel_exists_isUnit_iterate_apply_V_mul_sub_const_mem_sq_of_ringEquiv_compat_levelAut_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isUnit_iterate_apply_V_mul_sub_const_mem_sq_of_ringEquiv_compat_levelAut_of_isEnd_blowupChart_of_drinfeldChartWitness_linked (solution)
