-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_algEquiv_uvCrossingModel_compat_levelAut_pow_eq_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/0cedba0d-f863-572a-ae67-e1a1557a5508

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
import Theorems.Thm_IsLocalRing_exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_AdicCompletion_exists_ringEquiv_map_of_ringEquiv
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_algEquiv_uvCrossingModel_compat_levelAut_pow_eq_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace RingAut p2m_export "RingAut" "mul_apply one_apply" end RingAut
p2m_open_scoped "RingAut" in
private theorem RingAut.mul_apply' {R : Type} [Mul R] [Add R] (f g : RingAut R) (x : R) : (f * g) x = f (g x) := rfl

p2m_open_scoped "RingAut" in
private theorem RingAut.one_apply' {R : Type} [Mul R] [Add R] (x : R) : (1 : RingAut R) x = x := rfl

namespace AdicCompletion p2m_export "AdicCompletion" "map mk of incl module one_apply ext algebraMap_apply mul_apply isAdicComplete lift pi exists_eq_algebraMap_add maximalIdeal_fg maximalIdeal_eq_map exists_ringEquiv_map_of_ringEquiv" end AdicCompletion
p2m_open_scoped "AdicCompletion" in
private theorem AdicCompletion.exists_ringEquiv_of_eq {R : Type} [CommRing R] (I J : Ideal R) (h : I = J) :
    ∃ f : AdicCompletion I R ≃+* AdicCompletion J R,
      ∀ r : R, f (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion J R) r := by
  subst h; exact ⟨RingEquiv.refl _, fun _ => rfl⟩

namespace RingHom p2m_export "RingHom" "restrict FormallySmooth ext comp_apply mk ker id range comp FinitePresentation" end RingHom
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

namespace RingEquiv p2m_export "RingEquiv" "restrict symm_apply_apply mk coe_toRingHom toRingHom trans_apply toRingHom_eq_coe finite ext apply_symm_apply refl" end RingEquiv
p2m_open_scoped "RingEquiv" in

private theorem RingEquiv.mem_maximalIdeal_pow_of_mem {R : Type} [CommRing R] [IsLocalRing R] (e : R ≃+* R)
    (N : ℕ) (x : R) (hx : x ∈ (IsLocalRing.maximalIdeal R) ^ N) : e x ∈ (IsLocalRing.maximalIdeal R) ^ N := by
  have hmap : Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  have := Ideal.mem_map_of_mem e hx
  rwa [Ideal.map_pow, hmap] at this

private theorem eq_zero_of_forall_mem_pow {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T]
    (t : T) (ht : ∀ N : ℕ, t ∈ J ^ N) : t = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff J T) t fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact ht N

p2m_open_scoped "AdicCompletion" in

private theorem AdicCompletion.dense_maximalIdeal_pow' {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : ℕ) (s : AdicCompletion (IsLocalRing.maximalIdeal R) R) :
    ∃ f : R, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) f - s ∈
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ^ N := by
  obtain ⟨a, w, hw, hs⟩ := AdicCompletion.exists_eq_algebraMap_add (IsLocalRing.maximalIdeal R) AdicCompletion.maximalIdeal_fg N s
  refine ⟨a, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  have : algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) a - s = -w := by rw [hs]; ring
  rw [this]; exact neg_mem hw

p2m_open_scoped "AdicCompletion" in

private theorem AdicCompletion.sep_maximalIdeal_pow' {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (t : AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (ht : ∀ N : ℕ, t ∈ (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ^ N) : t = 0 := by
  haveI : IsAdicComplete ((IsLocalRing.maximalIdeal R).map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal R) (AdicCompletion (IsLocalRing.maximalIdeal R) R)).mpr
      (AdicCompletion.isAdicComplete AdicCompletion.maximalIdeal_fg)
  refine eq_zero_of_forall_mem_pow ((IsLocalRing.maximalIdeal R).map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))) t fun N => ?_
  rw [← AdicCompletion.maximalIdeal_eq_map]; exact ht N

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

    (n : ℕ) (hn1 : 1 ≤ n) (hnq : n ∣ q + 1)
    (γ₀ : SL(2, ℤ)) (hγ₀q : γ₀ ∈ CongruenceSubgroup.Gamma q) (hγ₀M : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (τ₀ : ↥K ≃ₐ[L] ↥K) (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ₀⁻¹ K τ₀)
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
    (hOτ : ∀ f : ↥K, f ∈ O ↔ τ₀ f ∈ O)

    (hOW : ∀ f : ↥K, f ∈ O → f ∈ W) (hOloc : IsLocalRing ↥O) (hOnoe : IsNoetherianRing ↥O)
    (hCO : ∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ O)
    (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
    (hιc : ∀ (a : A) (ha : algebraMap A ↥K a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a))
    (hϖO : algebraMap A ↥K ϖ ∈ O) (cx cy : ↥O)
    (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))ˣ)
    (hιx : ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))
    (hιy : ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))
    (hcyW : ∀ hcy : (cy : ↥K) ∈ W, (⟨(cy : ↥K), hcy⟩ : ↥W) ∈ maximalIdeal ↥W)
    (hcxW : ∀ hcx : (cx : ↥K) ∈ W, (⟨(cx : ↥K), hcx⟩ : ↥W) ∉ maximalIdeal ↥W) :
    ∃ θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal A) A)] (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)),

      (∀ (f : ↥K) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
        ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))) ∧

      θ₀ (UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ∉ Ideal.span {UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m), UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ)} ∧

      (∀ x : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)), ((θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ n) x = x) := by
  classical
  haveI := hOloc
  haveI := hOnoe

  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hAD := IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete A ϖ hirr
  obtain ⟨instDom, instDVR, instCpl, hirrhat, hisoA, hdensA⟩ := hAD
  have hmaxh : maximalIdeal (AdicCompletion (maximalIdeal A) A) = Ideal.span {(algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirrhat
  have hπu : ¬ IsUnit ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) := fun hu =>
    hirrhat.not_isUnit (isUnit_pow_iff (by omega) |>.mp hu)

  haveI iLM : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hπu
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

  obtain ⟨eO, heO⟩ : ∃ eO : ↥O ≃+* ↥O, ∀ f : ↥O, ((eO f : ↥O) : ↥K) = τ₀ (f : ↥K) :=
    ⟨{ toFun := fun f => ⟨τ₀ (f : ↥K), (hOτ _).mp f.2⟩
       invFun := fun f => ⟨τ₀.symm (f : ↥K), (hOτ _).mpr (by simpa using f.2)⟩
       left_inv := fun f => Subtype.ext (by simp)
       right_inv := fun f => Subtype.ext (by simp)
       map_mul' := fun f g => Subtype.ext (by simp)
       map_add' := fun f g => Subtype.ext (by simp) }, fun _ => rfl⟩
  have heOk : ∀ (k : ℕ) (f : ↥O), (((eO ^ k) f : ↥O) : ↥K) = (τ₀ ^ k) (f : ↥K) := by
    intro k; induction k with
    | zero => intro f; rw [pow_zero, pow_zero, AlgEquiv.one_apply, RingAut.one_apply']
    | succ k ih => intro f; rw [pow_succ', pow_succ', AlgEquiv.mul_apply, RingAut.mul_apply', heO, ih]
  have heOmax : Ideal.map eO (maximalIdeal ↥O) = maximalIdeal ↥O :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv eO)
  have hAC := AdicCompletion.exists_ringEquiv_map_of_ringEquiv (maximalIdeal ↥O) eO
  obtain ⟨T', hT'⟩ := hAC
  have hcast := AdicCompletion.exists_ringEquiv_of_eq (Ideal.map eO (maximalIdeal ↥O)) (maximalIdeal ↥O) heOmax
  obtain ⟨Tc, hTc⟩ := hcast
  obtain ⟨T, hT⟩ : ∃ T : AdicCompletion (maximalIdeal ↥O) ↥O ≃+* AdicCompletion (maximalIdeal ↥O) ↥O,
      ∀ f : ↥O, T (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) f) = algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) (eO f) :=
    ⟨T'.trans Tc, fun f => by rw [RingEquiv.trans_apply, hT', hTc]⟩
  have hTk : ∀ (k : ℕ) (f : ↥O), (T ^ k) (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) f)
      = algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ((eO ^ k) f) := by
    intro k; induction k with
    | zero => intro f; rw [pow_zero, pow_zero, RingAut.one_apply', RingAut.one_apply']
    | succ k ih => intro f; rw [pow_succ', pow_succ', RingAut.mul_apply', RingAut.mul_apply', ih, hT]
  obtain ⟨θ₀r, hθ₀r⟩ : ∃ θ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)), ∀ x, θ x = ι (T (ι.symm x)) := ⟨ι.symm.trans (T.trans ι), fun x => by simp only [RingEquiv.trans_apply]⟩
  have hθι : ∀ w, θ₀r (ι w) = ι (T w) := fun w =>
    (hθ₀r (ι w)).trans (congrArg ι (congrArg T (ι.symm_apply_apply w)))
  have hθιk : ∀ (k : ℕ) (w : AdicCompletion (maximalIdeal ↥O) ↥O), (θ₀r ^ k) (ι w) = ι ((T ^ k) w) := by
    intro k; induction k with
    | zero => intro w; simp only [pow_zero, RingAut.one_apply']
    | succ k ih => intro w; simp only [pow_succ', RingAut.mul_apply', ih, hθι]
  have hτA : ∀ a : A, τ₀ (algebraMap A ↥K a) = algebraMap A ↥K a := fun a => by simpa using hτkA 1 a
  have hτWmax : ∀ (x : ↥K) (hx : x ∈ W) (hx' : τ₀ x ∈ W),
      (⟨x, hx⟩ : ↥W) ∈ maximalIdeal ↥W ↔ (⟨τ₀ x, hx'⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro x hx hx'
    rw [hWmax_iff, hWmax_iff]
    refine not_congr (and_congr ?_ ?_)
    · rw [ne_eq, ne_eq, map_eq_zero_iff _ τ₀.injective]
    · rw [← map_inv₀]; exact hτ₀W _

  have hcompat : ∀ (f : ↥K) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀r (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩)) :=
    fun f hf hf' => by
      have h1 : eO ⟨f, hf⟩ = ⟨τ₀ f, hf'⟩ := Subtype.ext (heO ⟨f, hf⟩)
      exact ((hθι _).trans (congrArg ι ((hT ⟨f, hf⟩).trans (congrArg (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O)) h1)))).symm

  have hθcA : ∀ a : A, θ₀r (UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a))
      = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a) := by
    intro a
    have ha : algebraMap A ↥K a ∈ O := by
      have := hCO (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a); rwa [Subalgebra.coe_algebraMap] at this
    have h1 : eO ⟨algebraMap A ↥K a, ha⟩ = ⟨algebraMap A ↥K a, ha⟩ := Subtype.ext ((heO _).trans (hτA a))
    have h2 := hιc a ha
    calc θ₀r (UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a))
        = θ₀r (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩)) := by simp only [h2]
      _ = ι (T (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩)) := hθι _
      _ = ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) (eO ⟨_, ha⟩)) := congrArg ι (hT _)
      _ = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a) := by simp only [h1, h2]

  have hθc : ∀ w : (AdicCompletion (maximalIdeal A) A), θ₀r (UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) w)
      = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) w := by
    have hsp : ∀ N : ℕ, (maximalIdeal (AdicCompletion (maximalIdeal A) A)) ^ N = Ideal.span {(algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ N} := fun N => by
      rw [hmaxh, Ideal.span_singleton_pow]
    refine RingHom.eqOn_of_dense (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
      (θ₀r.toRingHom.comp (UVCrossingModel.constHom ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (UVCrossingModel.constHom ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))
      ?_ ?_ ?_ (fun a : A => algebraMap A (AdicCompletion (maximalIdeal A) A) a) ?_ ?_
    · intro N s hs
      exact RingEquiv.mem_maximalIdeal_pow_of_mem θ₀r N _ (Ideal.pow_right_mono hMmap N (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hs))
    · intro N s hs
      exact Ideal.pow_right_mono hMmap N (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hs)
    · exact fun t ht => eq_zero_of_forall_mem_pow _ t ht
    · intro N s
      obtain ⟨a, ha⟩ := hdensA N s
      refine ⟨a, ?_⟩
      rw [hsp, ← Ideal.neg_mem_iff, neg_sub]
      exact ha
    · intro a
      simp only [RingHom.comp_apply, UVCrossingModel.constHom_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      exact hθcA a
  let θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal A) A)] (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := AlgEquiv.ofRingEquiv (f := θ₀r) (fun w => hθc w)
  have hθ₀ : ∀ x, θ₀ x = θ₀r x := fun _ => rfl

  have hMB := ModularCurve.UVCrossingModel.exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow (AdicCompletion (maximalIdeal A) A) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) hirrhat m hm1
  obtain ⟨D, iDc, iDd, iDv, ψ, hψinj, hψU, hψV, hmD, hcen⟩ := hMB
  have hspanU : Ideal.span {UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ), UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)} =
      (maximalIdeal D).comap ψ := by
    ext x; rw [Ideal.mem_comap, hcen, Set.pair_comm]
  haveI hPUM : (Ideal.span {UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ), UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)}).IsPrime := by
    rw [hspanU]; exact Ideal.comap_isPrime _ _
  have hVnot : ∀ γ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))ˣ, (γ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∉
      Ideal.span {UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ), UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)} := by
    intro γ hγ
    rw [hspanU, Ideal.mem_comap, map_mul] at hγ
    exact (IsLocalRing.mem_maximalIdeal _).mp hγ (((Units.isUnit γ).map ψ).mul hψV)
  let φW : ↥O →+* ↥W :=
    { toFun := fun f => ⟨(f : ↥K), hOW _ f.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let PV : Ideal ↥O := (maximalIdeal ↥W).comap φW
  haveI hPVp : PV.IsPrime := Ideal.comap_isPrime _ _
  have memPV : ∀ f : ↥O, f ∈ PV ↔ (⟨(f : ↥K), hOW _ f.2⟩ : ↥W) ∈ maximalIdeal ↥W := fun _ => Iff.rfl
  have htPV : (⟨_, hϖO⟩ : ↥O) ∈ PV := by
    rw [memPV, hR3.2.1]; exact Ideal.mem_span_singleton_self _
  have hcyPV : cy ∈ PV := (memPV cy).mpr (hcyW _)
  have hcxPV : cx ∉ PV := fun hm => hcxW _ ((memPV cx).mp hm)
  let PU : Ideal ↥O := Ideal.comap ((ι : AdicCompletion (maximalIdeal ↥O) ↥O →+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))).comp (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O)))
    (Ideal.span {UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ), UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)})
  haveI hPUp : PU.IsPrime := Ideal.comap_isPrime _ _
  have memPU : ∀ f : ↥O, f ∈ PU ↔ ι ((algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O)) f) ∈
      Ideal.span {UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ), UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)} := fun _ => Iff.rfl
  have hconstmem : UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ∈
      Ideal.span {UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ), UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)} := Ideal.subset_span (by simp)
  have hUmem' : UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∈
      Ideal.span {UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ), UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)} := Ideal.subset_span (by simp)
  have htPU : (⟨_, hϖO⟩ : ↥O) ∈ PU := by rw [memPU, hιc ϖ hϖO]; exact hconstmem
  have hcxPU : cx ∈ PU := by rw [memPU, hιx]; exact Ideal.mul_mem_left _ _ hUmem'
  have hcyPU : cy ∉ PU := by rw [memPU, hιy]; exact hVnot γV
  have hBD := IsLocalRing.exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) hmaxh m hm1 ι ⟨_, hϖO⟩ (hιc ϖ hϖO) cx cy γU γV hιx hιy PV PU
    htPV hcyPV hcxPV htPU hcxPU hcyPU
  obtain ⟨hD1, -, -, -⟩ := hBD
  have hθU : θ₀r (UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ∉
      Ideal.span {UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m), UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ)} := by
    intro hmem

    have hU : UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) = ((γU⁻¹ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))ˣ) : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) := by
      rw [hιx, ← mul_assoc, Units.inv_mul, one_mul]
    simp only [hU, map_mul, hθι, hT] at hmem
    have h2 : ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) (eO cx)) ∈
        Ideal.span {UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m), UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ)} := by
      have hu : IsUnit (θ₀r ((γU⁻¹ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))ˣ) : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))) := (Units.isUnit _).map θ₀r
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      have := Ideal.mul_mem_left _ v hmem
      rwa [← mul_assoc, hv, one_mul] at this
    rw [Set.pair_comm] at h2
    have h2' : eO cx ∈ PV := (hD1 (eO cx)).mpr h2
    have ecx : (⟨((eO cx : ↥O) : ↥K), hOW _ (eO cx).2⟩ : ↥W) = ⟨τ₀ ((cx : ↥O) : ↥K), hOW _ ((hOτ _).mp cx.2)⟩ :=
      Subtype.ext (heO cx)
    have h3 : (⟨((cx : ↥O) : ↥K), hOW _ cx.2⟩ : ↥W) ∈ maximalIdeal ↥W :=
      (hτWmax _ (hOW _ cx.2) (hOW _ ((hOτ _).mp cx.2))).mpr (ecx ▸ (memPV _).mp h2')
    exact hcxW _ h3

  have hτnK : ∀ f : ↥K, (τ₀ ^ n) f = f := by
    intro f
    obtain ⟨g, h, hh0, hfh⟩ := hR1.2 f
    have hg := hcyc1 (g : ↥K) g.2
    have hh := hcyc1 (h : ↥K) h.2
    have h1 : (τ₀ ^ n) f * (h : ↥K) = (g : ↥K) := by
      have := congrArg (τ₀ ^ n) hfh
      rw [map_mul, hh, hg] at this; exact this
    exact mul_right_cancel₀ hh0 (h1.trans hfh.symm)
  have heOn : ∀ f : ↥O, (eO ^ n) f = f := fun f => Subtype.ext ((heOk n f).trans (hτnK _))
  have hsepO : ∀ t : (AdicCompletion (maximalIdeal ↥O) ↥O), (∀ N : ℕ, t ∈ (maximalIdeal (AdicCompletion (maximalIdeal ↥O) ↥O)) ^ N) → t = 0 :=
    fun t ht => AdicCompletion.sep_maximalIdeal_pow' t ht
  have hdensO : ∀ (N : ℕ) (s : (AdicCompletion (maximalIdeal ↥O) ↥O)), ∃ f : ↥O, algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) f - s ∈ (maximalIdeal (AdicCompletion (maximalIdeal ↥O) ↥O)) ^ N :=
    fun N s => AdicCompletion.dense_maximalIdeal_pow' N s
  have hTn : ∀ w : (AdicCompletion (maximalIdeal ↥O) ↥O), (T ^ n) w = w := by
    refine RingHom.eqOn_of_dense (maximalIdeal (AdicCompletion (maximalIdeal ↥O) ↥O)) (maximalIdeal (AdicCompletion (maximalIdeal ↥O) ↥O))
      ((T ^ n).toRingHom) (RingHom.id _) ?_ ?_ hsepO (fun f : ↥O => algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) f) hdensO ?_
    · intro N s hs; exact RingEquiv.mem_maximalIdeal_pow_of_mem (T ^ n) N s hs
    · intro N s hs; exact hs
    · intro f
      show (T ^ n) (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) f) = algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) f
      rw [hTk, heOn]
  have hθn : ∀ x : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)), (θ₀r ^ n) x = x := by
    intro x
    have h1 := hθιk n (ι.symm x)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [h1, hTn, RingEquiv.apply_symm_apply]
  have hθ₀coe : (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) = θ₀r := RingEquiv.ext fun _ => rfl

  refine ⟨θ₀, ?_, ?_, ?_⟩
  · intro f hf hf'; rw [hθ₀]; exact hcompat f hf hf'
  · intro h; apply hθU; rwa [hθ₀] at h
  · intro x; rw [hθ₀coe]; exact hθn x

end S_ModularCurve_FullLevel_AuxLevelOne_exists_algEquiv_uvCrossingModel_compat_levelAut_pow_eq_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_algEquiv_uvCrossingModel_compat_levelAut_pow_eq_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked_of_dvd (solution)
