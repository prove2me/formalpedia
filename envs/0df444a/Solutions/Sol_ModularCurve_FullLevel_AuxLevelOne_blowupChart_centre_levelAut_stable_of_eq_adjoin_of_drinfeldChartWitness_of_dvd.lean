-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/6842ee33-7e2d-5bbc-9b95-da61c355c275

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
import Theorems.Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace BlowupEq

theorem map_mem_span_triple_of_linearPart {S F : Type} [CommRing S] [FunLike F S S] [RingHomClass F S S]
    (θ : F) (a : S) (x : Fin 2 → S)
    (ha : θ a = a) (l : Fin 2 → Fin 2 → S)
    (hlin : ∀ jj : Fin 2, θ (x jj) - ∑ ii : Fin 2, l ii jj * x ii ∈ (Ideal.span {x 0, x 1}) ^ 2) :
    ∀ s : S, s ∈ Ideal.span {a, x 0, x 1} → θ s ∈ Ideal.span {a, x 0, x 1} := by
  classical
  have hsub : Ideal.span ({x 0, x 1} : Set S) ≤ Ideal.span {a, x 0, x 1} :=
    Ideal.span_mono (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢; tauto)
  have hx : ∀ jj : Fin 2, θ (x jj) ∈ Ideal.span {a, x 0, x 1} := by
    intro jj
    have h1 : θ (x jj) = (θ (x jj) - ∑ ii : Fin 2, l ii jj * x ii) + ∑ ii : Fin 2, l ii jj * x ii := by ring
    rw [h1]
    refine Ideal.add_mem _ ?_ ?_
    · exact hsub (Ideal.pow_le_self two_ne_zero (hlin jj))
    · refine Ideal.sum_mem _ (fun ii _ => Ideal.mul_mem_left _ _ (hsub (Ideal.subset_span ?_)))
      fin_cases ii <;> simp
  intro s hs
  have : Ideal.map θ (Ideal.span {a, x 0, x 1}) ≤ Ideal.span {a, x 0, x 1} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [ha]; exact Ideal.subset_span (by simp)
    · exact hx 0
    · exact hx 1
  exact this (Ideal.mem_map_of_mem θ hs)

theorem map_mem_adjoin_div_of_forall_mem
    {A K F : Type} [CommRing A] [Field K] [Algebra A K] [FunLike F K K] [RingHomClass F K K]
    (C : Subalgebra A K) (J : Ideal ↥C) (t : A)
    (B : Subalgebra A K)
    (hB : B = (Algebra.adjoin ↥C
        {x : K | ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K)}).restrictScalars A)
    (σ : F)
    (hσt : σ (algebraMap A K t) = algebraMap A K t)
    (hσC : ∀ a : K, a ∈ C → σ a ∈ C)
    (hσJ : ∀ (i : ↥C) (hi : σ (i : K) ∈ C), i ∈ J → (⟨σ (i : K), hi⟩ : ↥C) ∈ J) :
    ∀ f : K, f ∈ B → σ f ∈ B := by
  intro f hf
  subst hB
  rw [Subalgebra.mem_restrictScalars] at hf ⊢
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, hiJ, hx⟩ := hx
      refine Algebra.subset_adjoin ?_
      refine ⟨⟨σ (i : K), hσC _ i.2⟩, hσJ i _ hiJ, ?_⟩
      simp only
      rw [← hσt, ← map_mul, hx]
  | algebraMap c =>
      have hc : σ ((c : ↥C) : K) ∈ C := hσC _ c.2
      have : σ (algebraMap (↥C) K c) = algebraMap (↥C) K ⟨σ (c : K), hc⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

end BlowupEq

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
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A) :
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

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
              (∀ a : ↥(chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y) →
              ∀ a : ↥(chartAlgFin A (↥K) j),
                (e₁ : CMP →+* S) (toC (germY a)) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ↔
                (e₁ : CMP →+* S) (toC (germY (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a))) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ (a : ↥(chartAlgFin A (↥K) j)) (ha : τ (a : ↥K) ∈ chartAlgFin A (↥K) j),
              a ∈ J ↔ (⟨τ (a : ↥K), ha⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ f : ↥K, f ∈ B → τ f ∈ B) := by
  intro STK CMP toC S mkS germY

  have hW := hW₁
  obtain ⟨-, hfin, hfix, hlin, -, -, -⟩ := hW

  have hCOMP := ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L ζ hζ hι H₁ hH₁ K hK
  obtain ⟨hU, hM, hI⟩ := hCOMP

  have hE := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L ζ hζ H₁ hH₁ K hK
  have hmul : ∀ γ δ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → δ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ σ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ → ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ δ⁻¹ K σ → ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ (γ * δ)⁻¹ K (τ * σ) := by
    intro γ δ hγ hδ τ σ hτ hσ
    have h := hM γ⁻¹ δ⁻¹ (inv_mem hγ) (inv_mem hδ) τ σ hτ hσ
    rw [← mul_inv_rev] at h
    exact h
  have hone : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ (1 : SL(2, ℤ))⁻¹ K 1 := by
    rw [inv_one]; exact hI 1 (one_mem _) (one_mem _) (by simp)
  have huniq : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ τ' : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ → ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ' → τ = τ' :=
    fun γ hγ τ τ' h h' => hU γ⁻¹ (inv_mem hγ) τ τ' h h'
  have hinv : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ → ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹⁻¹ K τ⁻¹ := by
    intro γ hγ τ hτ
    have hex := hE γ⁻¹ (inv_mem hγ)
    obtain ⟨τ', hτ'⟩ := hex
    have h1 := hmul γ⁻¹ γ (inv_mem hγ) hγ τ' τ hτ' hτ
    rw [inv_mul_cancel] at h1
    have h2 : τ' * τ = 1 := huniq 1 (one_mem _) _ _ h1 hone
    have h3 : τ' = τ⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [← h3]; exact hτ'
  have hi : (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
              (∀ a : ↥(chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y) →
              ∀ a : ↥(chartAlgFin A (↥K) j),
                (e₁ : CMP →+* S) (toC (germY a)) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ↔
                (e₁ : CMP →+* S) (toC (germY (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a))) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) := by

    have hfwd : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K) (hτ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
        (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)
        (hfixτ : ∀ a : ↥(chartAlgFin A (↥K) j), (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y)
        (a : ↥(chartAlgFin A (↥K) j)),
        (e₁ : CMP →+* S) (toC (germY a)) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} →
        (e₁ : CMP →+* S) (toC (germY (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a))) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
      intro γ hγ τ hτ hpres hfixτ a ha
      have hfix' : ∀ a : ↥(chartAlgFin A (↥K) j), (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal := by
        rw [hy'y]; exact hfixτ
      have hl := hlin γ hγ τ hτ hpres hfix'
      obtain ⟨θ, c, M, hθ, hθW, hθlin, -, -, -, -⟩ := hl
      have key : ∀ x : CMP, (e₁ : CMP →+* S) x = e₁ x := fun x => rfl
      rw [key] at ha ⊢
      rw [← hθ a]
      have hlin' : ∀ jj : Fin 2, θ ((fun i : Fin 2 => mkS (MvPowerSeries.X i)) jj) -
          ∑ ii : Fin 2, (fun i j : Fin 2 => mkS (MvPowerSeries.C (M i j))) ii jj * (fun i : Fin 2 => mkS (MvPowerSeries.X i)) ii ∈
          (Ideal.span {(fun i : Fin 2 => mkS (MvPowerSeries.X i)) 0, (fun i : Fin 2 => mkS (MvPowerSeries.X i)) 1}) ^ 2 := by
        intro jj
        have h := hθlin jj
        simp only [map_sum, map_mul] at h
        exact h
      exact BlowupEq.map_mem_span_triple_of_linearPart θ (mkS (MvPowerSeries.C (σ₁ ϖt))) (fun i => mkS (MvPowerSeries.X i))
        (hθW _) (fun i j => mkS (MvPowerSeries.C (M i j))) hlin' _ ha
    intro γ hγ τ hτ hpres hfixτ a
    constructor
    · exact hfwd γ hγ τ hτ hpres hfixτ a
    · intro hτa

      have hγ' : γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := inv_mem hγ
      have hτ' := hinv γ hγ τ hτ
      have hpres' : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ⁻¹ a ∈ chartAlgFin A (↥K) j := hfin γ⁻¹ hγ' τ⁻¹ hτ'
      have hcoe : ∀ (σ : ↥K ≃ₐ[L] ↥K) (hp : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → σ a ∈ chartAlgFin A (↥K) j)
          (b : ↥(chartAlgFin A (↥K) j)), ((((σ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hp) b : ↥(chartAlgFin A (↥K) j)) : ↥K) = σ (b : ↥K) :=
        fun σ hp b => rfl
      have hback : ∀ b : ↥(chartAlgFin A (↥K) j), (((τ⁻¹ : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres') (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) b) = b := by
        intro b; apply Subtype.ext; rw [hcoe, hcoe]
        show τ.symm (τ (b : ↥K)) = (b : ↥K)
        exact τ.symm_apply_apply _
      have hfix'' : ∀ b : ↥(chartAlgFin A (↥K) j), ((((τ⁻¹ : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres') b : ↥(chartAlgFin A (↥K) j)) - b ∈ y := by
        intro b
        have h1 := hfixτ ((((τ⁻¹ : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres') b)
        have h2 : ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) ((((τ⁻¹ : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres') b) = b := by
          apply Subtype.ext; rw [hcoe, hcoe]
          show τ (τ.symm (b : ↥K)) = (b : ↥K)
          exact τ.apply_symm_apply _
        rw [h2] at h1
        rw [← Ideal.neg_mem_iff, neg_sub]
        exact h1
      have h := hfwd γ⁻¹ hγ' τ⁻¹ hτ' hpres' hfix'' (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a) hτa
      rw [hback] at h
      exact h
  have hii : (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ (a : ↥(chartAlgFin A (↥K) j)) (ha : τ (a : ↥K) ∈ chartAlgFin A (↥K) j),
              a ∈ J ↔ (⟨τ (a : ↥K), ha⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J) := by

    have hJmem : ∀ x : ↥(chartAlgFin A (↥K) j), x ∈ J ↔
        ∀ (γ' : SL(2, ℤ)), γ' ∈ CongruenceSubgroup.Gamma q → γ' ∈ CongruenceSubgroup.Gamma0 M' → ∀ (τ' : ↥K ≃ₐ[L] ↥K), ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ'⁻¹ K τ' →
          ∀ (hpres' : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ' a ∈ chartAlgFin A (↥K) j),
            ((τ' : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres') x ∈ Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) := by
      intro x
      have hJ' := hJ
      rw [hJ', Ideal.mem_sInf]
      constructor
      · intro h γ' h1 h2 τ' h3 hpres'
        exact h (Set.mem_setOf.mpr ⟨γ', h1, h2, τ', h3, hpres', rfl⟩)
      · intro h I hI
        obtain ⟨γ', h1, h2, τ', h3, hpres', rfl⟩ := Set.mem_setOf.mp hI
        exact h γ' h1 h2 τ' h3 hpres'
    have hcoe : ∀ (σ : ↥K ≃ₐ[L] ↥K) (hp : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → σ a ∈ chartAlgFin A (↥K) j)
        (b : ↥(chartAlgFin A (↥K) j)), ((((σ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hp) b : ↥(chartAlgFin A (↥K) j)) : ↥K) = σ (b : ↥K) :=
      fun σ hp b => rfl

    have hfwd2 : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K) (hτ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
        (x : ↥(chartAlgFin A (↥K) j)) (hx : τ (x : ↥K) ∈ chartAlgFin A (↥K) j),
        x ∈ J → (⟨τ (x : ↥K), hx⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J := by
      intro γ hγ τ hτ x hx hxJ
      rw [hJmem] at hxJ ⊢
      intro γ' h1' h2' τ' h3' hpres'

      have hℓq : ℓ ≠ q := fun h => hqM' (h ▸ hℓM')
      have hK0 := CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd q M' hqM' ℓ hℓq (γ' * γ)
      obtain ⟨δ, hδℓ, hδ0, -, hδq⟩ := hK0
      have hga0 : δ⁻¹ * (γ' * γ) ∈ CongruenceSubgroup.Gamma0 M' := mul_mem (inv_mem hδ0) (mul_mem h2' hγ)
      have hexa := hE _ hga0
      obtain ⟨τa, hτa⟩ := hexa
      have hexb := hE δ hδ0
      obtain ⟨τb, hτb⟩ := hexb
      have hprod1 := hmul _ _ h2' hγ _ _ h3' hτ
      have hprod2 := hmul _ _ hδ0 hga0 _ _ hτb hτa
      rw [mul_inv_cancel_left] at hprod2
      have heq : τ' * τ = τb * τa := huniq _ (mul_mem h2' hγ) _ _ hprod1 hprod2
      have hpresa : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τa a ∈ chartAlgFin A (↥K) j := hfin _ hga0 τa hτa
      have hpresb : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τb a ∈ chartAlgFin A (↥K) j := hfin _ hδ0 τb hτb

      have h1 := hxJ _ hδq hga0 τa hτa hpresa
      rw [Ideal.mem_comap] at h1

      have hfixb : ∀ a : ↥(chartAlgFin A (↥K) j), (((τb : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpresb) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y := by

        intro a; rw [← hy'y]; exact hfix δ hδ0 (CongruenceSubgroup.Gamma_mem.mp hδℓ).2.2.2 τb hτb hpresb a
      have h2 := (hi δ hδ0 τb hτb hpresb hfixb (((τa : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpresa) x)).mp h1

      have hxeq : ((τ' : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres') (⟨τ (x : ↥K), hx⟩ : ↥(chartAlgFin A (↥K) j)) = ((τb : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpresb) (((τa : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpresa) x) := by
        apply Subtype.ext
        rw [hcoe, hcoe, hcoe]
        show (τ' * τ) (x : ↥K) = (τb * τa) (x : ↥K)
        rw [heq]
      rw [Ideal.mem_comap, hxeq]
      exact h2
    intro γ hγ τ hτ x hx
    constructor
    · exact hfwd2 γ hγ τ hτ x hx
    · intro h
      have hγ' : γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := inv_mem hγ
      have hτ' := hinv γ hγ τ hτ
      have hx' : τ⁻¹ (((⟨τ (x : ↥K), hx⟩ : ↥(chartAlgFin A (↥K) j)) : ↥K)) ∈ chartAlgFin A (↥K) j := by
        show τ.symm (τ (x : ↥K)) ∈ chartAlgFin A (↥K) j
        rw [τ.symm_apply_apply]; exact x.2
      have h' := hfwd2 γ⁻¹ hγ' τ⁻¹ hτ' ⟨τ (x : ↥K), hx⟩ hx' h
      have hxe : (⟨τ⁻¹ (((⟨τ (x : ↥K), hx⟩ : ↥(chartAlgFin A (↥K) j)) : ↥K)), hx'⟩ : ↥(chartAlgFin A (↥K) j)) = x := by
        apply Subtype.ext
        show τ.symm (τ (x : ↥K)) = (x : ↥K)
        exact τ.symm_apply_apply _
      rw [hxe] at h'
      exact h'
  have hiii : (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ f : ↥K, f ∈ B → τ f ∈ B) := by
    intro γ hγ τ hτ
    have hσt : τ (algebraMap A ↥K ϖt) = algebraMap A ↥K ϖt := by
      rw [IsScalarTower.algebraMap_apply A L ↥K ϖt]
      exact τ.commutes _
    exact BlowupEq.map_mem_adjoin_div_of_forall_mem (chartAlgFin A (↥K) j) J ϖt B hB τ hσt
      (hfin γ hγ τ hτ) (fun i hi hiJ => (hii γ hγ τ hτ i hi).mp hiJ)
  exact ⟨hi, hii, hiii⟩

end S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd (solution)
