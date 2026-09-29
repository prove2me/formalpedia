-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_coordRing_surjective_ker_eq_span_of_chartMap_of_localFibreMap_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a206beee-5fb3-59da-896f-a4e42865244a

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_coordRing_surjective_ker_eq_span_of_chartMap_of_localFibreMap_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace K4Ker

theorem exists_not_mem_and_mul_mem_of_flat {C S : Type*} [CommRing C] [CommRing S] [Algebra C S]
    [Module.Flat C S] (𝔪 : Ideal C) (h𝔪 : Ideal.map (algebraMap C S) 𝔪 ≠ ⊤) (𝔞 : Ideal C) (c : C)
    (hc : algebraMap C S c ∈ Ideal.map (algebraMap C S) 𝔞) :
    ∃ s : C, s ∉ 𝔪 ∧ s * c ∈ 𝔞 := by
  classical
  by_contra hcon
  push Not at hcon

  let M := C ⧸ 𝔞
  let m : M := Ideal.Quotient.mk 𝔞 c
  let τ : Ideal C := Ideal.torsionOf C M m
  have hτ : τ ≤ 𝔪 := by
    intro s hs
    rw [Ideal.mem_torsionOf_iff] at hs
    by_contra hsm
    apply hcon s hsm
    have : Ideal.Quotient.mk 𝔞 (s * c) = 0 := by
      rw [map_mul]
      have hs' : s • m = 0 := hs
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at hs'
      exact hs'
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  let N : Submodule C M := Submodule.span C {m}
  have hinj : Function.Injective (LinearMap.lTensor S N.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype

  have hzero : (1 : S) ⊗ₜ[C] m = 0 := by
    have h1 : (1 : S) ⊗ₜ[C] m = (algebraMap C S c) ⊗ₜ[C] (1 : M) := by
      have hm : m = c • (1 : M) := by
        show Ideal.Quotient.mk 𝔞 c = c • (1 : C ⧸ 𝔞)
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one]
      rw [hm, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rw [h1, ← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hc,
      map_zero]
  have hu : (1 : S) ⊗ₜ[C] (⟨m, Submodule.mem_span_singleton_self m⟩ : ↥N) = 0 := by
    apply hinj
    rw [LinearMap.lTensor_tmul, map_zero]
    exact hzero

  let e₁ : ↥N ≃ₗ[C] (C ⧸ τ) := (Ideal.quotTorsionOfEquivSpanSingleton C M m).symm
  have he₁ : e₁ ⟨m, Submodule.mem_span_singleton_self m⟩ = Ideal.Quotient.mk τ 1 := by
    apply (Ideal.quotTorsionOfEquivSpanSingleton C M m).injective
    rw [LinearEquiv.apply_symm_apply]
    show _ = Ideal.quotTorsionOfEquivSpanSingleton C M m (Submodule.Quotient.mk 1)
    rw [Ideal.quotTorsionOfEquivSpanSingleton_apply_mk, one_smul]
  have hu' : (1 : S) ⊗ₜ[C] (Ideal.Quotient.mk τ 1) = 0 := by
    have := congrArg (TensorProduct.congr (LinearEquiv.refl C S) e₁) hu
    rw [map_zero, TensorProduct.congr_tmul, LinearEquiv.refl_apply, he₁] at this
    exact this
  have hone : (Ideal.Quotient.mk (Ideal.map (algebraMap C S) τ) (1 : S)) = 0 := by
    have := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S τ).symm hu'
    rw [map_zero, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, one_smul] at this
    exact this
  rw [Ideal.Quotient.eq_zero_iff_mem] at hone
  have htop : Ideal.map (algebraMap C S) τ = ⊤ := (Ideal.eq_top_iff_one _).mpr hone
  exact h𝔪 (top_le_iff.mp (htop ▸ Ideal.map_mono hτ))

theorem exists_pow_mul_eq_of_mem_adjoin {C K : Type*} [CommRing C] [Field K] [Algebra C K]
    (J : Ideal C) (t : C) (ht : t ∈ J) (T : Set K)
    (hT : ∀ x ∈ T, ∃ i ∈ J, x * algebraMap C K t = algebraMap C K i)
    {b : K} (hb : b ∈ Algebra.adjoin C T) :
    ∃ N : ℕ, ∃ c ∈ J ^ N, b * algebraMap C K t ^ N = algebraMap C K c := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, hi, hx⟩ := hT x hx
      exact ⟨1, i, by rw [pow_one]; exact hi, by rw [pow_one]; exact hx⟩
  | algebraMap c =>
      exact ⟨0, c, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top, by rw [pow_zero, mul_one]⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨N, c, hc, hxc⟩ := ihx
      obtain ⟨M, d, hd, hyd⟩ := ihy
      refine ⟨N + M, c * t ^ M + d * t ^ N, ?_, ?_⟩
      · refine Ideal.add_mem _ ?_ ?_
        · rw [pow_add]; exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow ht M)
        · rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hd (Ideal.pow_mem_pow ht N)
      · rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hxc, ← hyd]
        ring
  | mul x y hx hy ihx ihy =>
      obtain ⟨N, c, hc, hxc⟩ := ihx
      obtain ⟨M, d, hd, hyd⟩ := ihy
      refine ⟨N + M, c * d, ?_, ?_⟩
      · rw [pow_add]; exact Ideal.mul_mem_mul hc hd
      · rw [map_mul, ← hxc, ← hyd]
        ring

theorem exists_pow_mul_eq_of_mem_closure {S L : Type*} [CommRing S] [CommRing L] [Algebra S L]
    (t : S) [IsLocalization.Away t L] (𝔑 : Ideal S) (ht : t ∈ 𝔑) (s₀ s₁ : S) (hs₀ : s₀ ∈ 𝔑) (hs₁ : s₁ ∈ 𝔑)
    {w : L} (hw : w ∈ Subring.closure (Set.range (algebraMap S L) ∪
      {algebraMap S L s₀ * IsLocalization.Away.invSelf (S := L) t,
       algebraMap S L s₁ * IsLocalization.Away.invSelf (S := L) t})) :
    ∃ M : ℕ, ∃ ν ∈ 𝔑 ^ M, w * algebraMap S L t ^ M = algebraMap S L ν := by
  have hinv : algebraMap S L t * IsLocalization.Away.invSelf (S := L) t = 1 :=
    IsLocalization.Away.mul_invSelf t
  induction hw using Subring.closure_induction with
  | mem x hx =>
      rcases hx with ⟨s, rfl⟩ | hx
      · exact ⟨0, s, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top, by rw [pow_zero, mul_one]⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · refine ⟨1, s₀, by rw [pow_one]; exact hs₀, ?_⟩
          rw [pow_one, mul_assoc, mul_comm (IsLocalization.Away.invSelf t), hinv, mul_one]
        · refine ⟨1, s₁, by rw [pow_one]; exact hs₁, ?_⟩
          rw [pow_one, mul_assoc, mul_comm (IsLocalization.Away.invSelf t), hinv, mul_one]
  | zero => exact ⟨0, 0, zero_mem _, by rw [map_zero, zero_mul]⟩
  | one => exact ⟨0, 1, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top, by rw [pow_zero, mul_one, map_one]⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨N, c, hc, hxc⟩ := ihx
      obtain ⟨M, d, hd, hyd⟩ := ihy
      refine ⟨N + M, c * t ^ M + d * t ^ N, ?_, ?_⟩
      · refine Ideal.add_mem _ ?_ ?_
        · rw [pow_add]; exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow ht M)
        · rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hd (Ideal.pow_mem_pow ht N)
      · rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hxc, ← hyd]
        ring
  | neg x hx ihx =>
      obtain ⟨N, c, hc, hxc⟩ := ihx
      exact ⟨N, -c, (𝔑 ^ N).neg_mem hc, by rw [map_neg, ← hxc]; ring⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨N, c, hc, hxc⟩ := ihx
      obtain ⟨M, d, hd, hyd⟩ := ihy
      refine ⟨N + M, c * d, ?_, ?_⟩
      · rw [pow_add]; exact Ideal.mul_mem_mul hc hd
      · rw [map_mul, ← hxc, ← hyd]
        ring

end K4Ker

theorem K4Ker.mem_nonZeroDivisors_of_flat {C S : Type*} [CommRing C] [IsDomain C] [CommRing S] (Ψ : C →+* S)
    (hflat : letI : Algebra C S := Ψ.toAlgebra; Module.Flat C S) (t : C) (ht : t ≠ 0) :
    Ψ t ∈ nonZeroDivisors S := by
  letI : Algebra C S := Ψ.toAlgebra
  haveI : Module.Flat C S := hflat
  have hreg : IsSMulRegular S t :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have h1 : t • x = t • (0 : S) := by
    rw [smul_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    exact hx
  exact hreg h1

theorem K4Ker.exists_not_mem_and_mul_mem_of_flat' {C S : Type*} [CommRing C] [CommRing S] (Ψ : C →+* S)
    (hflat : letI : Algebra C S := Ψ.toAlgebra; Module.Flat C S)
    (𝔪 : Ideal C) (h𝔪 : Ideal.map Ψ 𝔪 ≠ ⊤) (𝔞 : Ideal C) (c : C) (hc : Ψ c ∈ Ideal.map Ψ 𝔞) :
    ∃ s : C, s ∉ 𝔪 ∧ s * c ∈ 𝔞 := by
  letI : Algebra C S := Ψ.toAlgebra
  haveI : Module.Flat C S := hflat
  exact K4Ker.exists_not_mem_and_mul_mem_of_flat 𝔪 h𝔪 𝔞 c hc

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
    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hbridge :
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

        Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) = y ∧

        (∀ (n : ℕ) (s : S), ∃ a : ↥(chartAlgFin A (↥K) j), ((e₁ : CMP →+* S).comp (toC.comp germY)) a - s ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ n) ∧

        (∀ a : A, ((e₁ : CMP →+* S).comp (toC.comp germY)) (algebraMap A ↥(chartAlgFin A (↥K) j) a) = mkS (MvPowerSeries.C (σ₁ a))) ∧

        (∀ c : ↥(chartAlgFin A (↥K) j), ∃ a : A, c - algebraMap A ↥(chartAlgFin A (↥K) j) a ∈ y) ∧
        (∀ w : W₁, ∃ a : A, w - σ₁ a ∈ IsLocalRing.maximalIdeal W₁) ∧
        Ideal.comap σ₁ (IsLocalRing.maximalIdeal W₁) = IsLocalRing.maximalIdeal A ∧

        (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}).IsMaximal ∧ (∀ I : Ideal S, I.IsMaximal → I = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (letI : Algebra ↥(chartAlgFin A (↥K) j) S := (((e₁ : CMP →+* S).comp (toC.comp germY))).toAlgebra
         Module.Flat ↥(chartAlgFin A (↥K) j) S))

    (hcentre :
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

        Ideal.map ((e₁ : CMP →+* S).comp (toC.comp germY)) J = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ∧

        (∃ I : Ideal ↥(chartAlgFin A (↥K) j),
            J = Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ⊓ I ∧ I ⊔ y = ⊤) ∧
        J ≤ y ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ J)
    (inst : Algebra (GaloisField q 2) (ResidueField A)) :
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
        let Lloc := Localization.Away (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let ιS : S →+* Lloc := algebraMap S Lloc
        let x₀ : Lloc := ιS (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let x₁ : Lloc := ιS (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let Rloc : Subring Lloc := Subring.closure (Set.range ιS ∪ {x₀, x₁})
        ∀ (Φ : ↥B →+* Lloc) (hιR : ∀ s : S, ιS s ∈ Rloc) (hx₀ : x₀ ∈ Rloc) (hx₁ : x₁ ∈ Rloc) (hΦR : ∀ b : ↥B, Φ b ∈ Rloc)
          (tW : W₁ →+* ResidueField A) (cR : ResidueField A)
          (ρR : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A)),

          (∀ a : ↥(chartAlgFin A (↥K) j), Φ ⟨(a : ↥K), hCB a.2⟩ = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) a)) →
          (∀ (x : ↥B) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J → (x : ↥K) * algebraMap A ↥K ϖt = (i : ↥K) →
              Φ x * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) i)) →

          (∀ a : A, tW (σ₁ a) = residue A a) → (∀ w : W₁, w ∈ IsLocalRing.maximalIdeal W₁ → tW w = 0) →
          cR ≠ 0 →
          (∀ F : MvPowerSeries (Fin 2) W₁, ρR ⟨ιS (mkS F), hιR (mkS F)⟩ =
              algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F))) →
          ρR ⟨x₀, hx₀⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A) →
          ρR ⟨x₁, hx₁⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A) →
          Function.Surjective ρR →
          (∀ r : ↥Rloc, ρR r = 0 ↔ r ∈ Ideal.span {(⟨ιS (mkS (MvPowerSeries.C (σ₁ ϖ))), hιR (mkS (MvPowerSeries.C (σ₁ ϖ)))⟩ : ↥Rloc)}) →
          ∃ ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A),

            (∀ b : ↥B, ρ b = ρR ⟨Φ b, hΦR b⟩) ∧
            Function.Surjective ρ ∧
            (∀ b : ↥B, ρ b = 0 ↔ b ∈ Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hCB c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j)))) ∧
            (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) := by
  intro STK CMP toC S mkS germY Lloc ιS x₀ x₁ Rloc Φ hιR hx₀ hx₁ hΦR tW cR ρR hΦ1 hΦ2 htW1 htW2 hcR hρF hρx₀ hρx₁ hρsurj hρker
  classical

  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(chartAlgFin A (↥K) j) →+* S, Ψ = (e₁ : CMP →+* S).comp (toC.comp germY) := ⟨_, rfl⟩
  obtain ⟨𝔐, h𝔐⟩ : ∃ 𝔐 : Ideal S,
      𝔐 = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := ⟨_, rfl⟩
  obtain ⟨𝔑, h𝔑⟩ : ∃ 𝔑 : Ideal S,
      𝔑 = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := ⟨_, rfl⟩
  have hb := hbridge
  obtain ⟨hcen, -, hconst, hres, -, -, hmax, -, hflat⟩ := hb
  have hcen' : Ideal.comap Ψ 𝔐 = y := by rw [hΨ, h𝔐]; exact hcen
  have hconst' : ∀ a : A, Ψ (algebraMap A ↥(chartAlgFin A (↥K) j) a) = mkS (MvPowerSeries.C (σ₁ a)) := by rw [hΨ]; exact hconst
  have hflat' : (letI : Algebra ↥(chartAlgFin A (↥K) j) S := Ψ.toAlgebra; Module.Flat ↥(chartAlgFin A (↥K) j) S) := by rw [hΨ]; exact hflat
  have hc := hcentre
  obtain ⟨hmapJ, -, -, hϖtJ⟩ := hc
  have hmapJ' : Ideal.map Ψ J = 𝔑 := by rw [hΨ, h𝔑]; exact hmapJ
  have hΦ1' : ∀ a : ↥(chartAlgFin A (↥K) j), Φ ⟨(a : ↥K), hCB a.2⟩ = ιS (Ψ a) := by
    intro a; rw [hΨ]; exact hΦ1 a
  have hΦ2' : ∀ (x : ↥B) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J → (x : ↥K) * algebraMap A ↥K ϖt = (i : ↥K) →
      Φ x * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) = ιS (Ψ i) := by
    intro x i hi hx; rw [hΨ]; exact hΦ2 x i hi hx

  let ι : ↥(chartAlgFin A (↥K) j) →+* ↥B := (Subalgebra.inclusion hCB).toRingHom
  have hι : ∀ c : ↥(chartAlgFin A (↥K) j), ι c = ⟨(c : ↥K), hCB c.2⟩ := fun c => rfl
  let ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A) := ρR.comp (Φ.codRestrict Rloc hΦR)
  have hρ : ∀ b : ↥B, ρ b = ρR ⟨Φ b, hΦR b⟩ := fun b => rfl
  let ρS : S →+* DrinfeldCurve.CoordRing q (ResidueField A) := ρR.comp (ιS.codRestrict Rloc hιR)
  have hρS : ∀ s : S, ρS s = ρR ⟨ιS s, hιR s⟩ := fun s => rfl
  have hρι : ∀ c : ↥(chartAlgFin A (↥K) j), ρ (ι c) = ρS (Ψ c) := by
    intro c
    rw [hρ, hρS]
    congr 1
    exact Subtype.ext (hΦ1' c)

  have hϖ𝔪 : ϖ ∈ maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hρS𝔐 : ∀ s ∈ 𝔐, ρS s = 0 := by
    have hle : 𝔐 ≤ RingHom.ker ρS := by
      rw [h𝔐]
      refine Ideal.span_le.mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, RingHom.mem_ker, hρS]
      rcases hg with rfl | rfl | rfl
      · rw [hρF, MvPowerSeries.constantCoeff_C, htW1, (residue_eq_zero_iff ϖ).mpr hϖ𝔪, map_zero]
      · rw [hρF, MvPowerSeries.constantCoeff_X, map_zero, map_zero]
      · rw [hρF, MvPowerSeries.constantCoeff_X, map_zero, map_zero]
    intro s hs
    exact hle hs

  have hconstρ : ∀ a : A, ρ (algebraMap A ↥B a) =
      algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a) := by
    intro a
    have heq : algebraMap A ↥B a = ι (algebraMap A ↥(chartAlgFin A (↥K) j) a) := by
      apply Subtype.ext
      rw [hι, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
    rw [heq, hρι, hconst', hρS, hρF, MvPowerSeries.constantCoeff_C, htW1]

  have hker₁ : ∀ b : ↥B, b ∈ Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hCB c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j))) → ρ b = 0 := by
    have hle : Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hCB c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j))) ≤ RingHom.ker ρ := by
      refine Ideal.span_le.mpr ?_
      rintro b ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show ρ (ι c) = 0
      rw [hρι]
      apply hρS𝔐
      have hc' : c ∈ Ideal.comap Ψ 𝔐 := by rw [hcen']; exact hc
      exact Ideal.mem_comap.mp hc'
    intro b hb
    exact hle hb

  have hinv : ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) = 1 :=
    IsLocalization.Away.mul_invSelf _
  have hqp : q.Prime := Fact.out
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
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hϖtK : algebraMap A ↥K ϖt ≠ 0 := (map_ne_zero_iff _ hinjAK).mpr hϖt0
  have hAK : ∀ a : A, algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap A ↥(chartAlgFin A (↥K) j) a) = algebraMap A ↥K a :=
    fun a => (IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K) j) ↥K a).symm

  have hP : ∀ v ∈ Ideal.map Ψ J, ∃ b : ↥B,
      ∃ hv : ιS v * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) ∈ Rloc,
        ρR ⟨_, hv⟩ = ρ b := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨jj, hjj, rfl⟩ := hv
        have hbmem : (jj : ↥K) * (algebraMap A ↥K ϖt)⁻¹ ∈ B := by
          rw [hB, Subalgebra.mem_restrictScalars]
          refine Algebra.subset_adjoin ⟨jj, hjj, ?_⟩
          rw [mul_assoc, inv_mul_cancel₀ hϖtK, mul_one]
        have hΦb : Φ ⟨_, hbmem⟩ = ιS (Ψ jj) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) := by
          have h2 := hΦ2' ⟨_, hbmem⟩ jj hjj (by
            show (jj : ↥K) * (algebraMap A ↥K ϖt)⁻¹ * algebraMap A ↥K ϖt = (jj : ↥K)
            rw [mul_assoc, inv_mul_cancel₀ hϖtK, mul_one])
          rw [← h2, mul_assoc, hinv, mul_one]
        refine ⟨⟨_, hbmem⟩, by rw [← hΦb]; exact hΦR _, ?_⟩
        rw [hρ]
        congr 1
        exact Subtype.ext hΦb.symm
    | zero =>
        have hmem0 : ιS 0 * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) ∈ Rloc := by
          rw [map_zero, zero_mul]; exact Rloc.zero_mem
        refine ⟨0, hmem0, ?_⟩
        have h0 : (⟨_, hmem0⟩ : ↥Rloc) = 0 :=
          Subtype.ext (by show ιS 0 * _ = (0 : Lloc); rw [map_zero, zero_mul])
        rw [h0, map_zero, map_zero]
    | add v w hv hw ihv ihw =>
        obtain ⟨b, hbv, hb⟩ := ihv
        obtain ⟨b', hbw, hb'⟩ := ihw
        have hmem : ιS (v + w) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) ∈ Rloc := by
          rw [map_add, add_mul]; exact Rloc.add_mem hbv hbw
        refine ⟨b + b', hmem, ?_⟩
        have : (⟨_, hmem⟩ : ↥Rloc) = ⟨_, hbv⟩ + ⟨_, hbw⟩ := Subtype.ext (by show ιS (v + w) * _ = _; rw [map_add, add_mul]; rfl)
        rw [this, map_add, map_add, hb, hb']
    | smul s v hv ih =>
        obtain ⟨b, hbv, hb⟩ := ih
        have hmem : ιS (s • v) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) ∈ Rloc := by
          rw [smul_eq_mul, map_mul, mul_assoc]; exact Rloc.mul_mem (hιR s) hbv
        obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective s
        obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (tW (MvPowerSeries.constantCoeff F))
        refine ⟨algebraMap A ↥B a * b, hmem, ?_⟩
        have : (⟨_, hmem⟩ : ↥Rloc) = ⟨ιS (Ideal.Quotient.mk _ F), hιR _⟩ * ⟨_, hbv⟩ :=
          Subtype.ext (by show ιS (Ideal.Quotient.mk _ F • v) * _ = ιS (Ideal.Quotient.mk _ F) * (ιS v * _); rw [smul_eq_mul, map_mul, mul_assoc])
        rw [this, map_mul, map_mul, hb, hconstρ, ← hρS]
        congr 1
        rw [hρS, hρF]
        congr 1
        exact ha.symm
  have hx_mem : ∃ b : ↥B, ρ b = DrinfeldCurve.x q (ResidueField A) := by
    have hX0 : mkS (MvPowerSeries.X 0) ∈ Ideal.map Ψ J := by
      rw [hmapJ', h𝔑]; exact Ideal.subset_span (by simp)
    obtain ⟨b, hv, hb⟩ := hP _ hX0
    have hb' : ρ b = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A) := by
      rw [← hb, ← hρx₀]
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (cR⁻¹ : ResidueField A)
    refine ⟨algebraMap A ↥B a * b, ?_⟩
    rw [map_mul, hb', hconstρ, ← mul_assoc, ← map_mul]
    have : residue A a * cR = 1 := by
      rw [ha, inv_mul_cancel₀ hcR]
    rw [this, map_one, one_mul]
  have hy_mem : ∃ b : ↥B, ρ b = DrinfeldCurve.y q (ResidueField A) := by
    have hX1 : mkS (MvPowerSeries.X 1) ∈ Ideal.map Ψ J := by
      rw [hmapJ', h𝔑]; exact Ideal.subset_span (by simp)
    obtain ⟨b, hv, hb⟩ := hP _ hX1
    have hb' : ρ b = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A) := by
      rw [← hb, ← hρx₁]
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (cR⁻¹ : ResidueField A)
    refine ⟨algebraMap A ↥B a * b, ?_⟩
    rw [map_mul, hb', hconstρ, ← mul_assoc, ← map_mul]
    have : residue A a * cR = 1 := by
      rw [ha, inv_mul_cancel₀ hcR]
    rw [this, map_one, one_mul]
  have hsurjρ : Function.Surjective ρ := by
    intro z
    obtain ⟨p, rfl⟩ := DrinfeldCurve.mk_surjective q (ResidueField A) z
    induction p using MvPolynomial.induction_on with
    | C a =>
        obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
        refine ⟨algebraMap A ↥B a₀, ?_⟩
        rw [hconstρ]
        exact ((DrinfeldCurve.mk q (ResidueField A)).commutes _).symm
    | add p p' hp hp' =>
        obtain ⟨b, hb⟩ := hp
        obtain ⟨b', hb'⟩ := hp'
        exact ⟨b + b', by rw [map_add, hb, hb', map_add]⟩
    | mul_X p i hp =>
        obtain ⟨b, hb⟩ := hp
        fin_cases i
        · obtain ⟨bx, hbx⟩ := hx_mem
          exact ⟨b * bx, by rw [map_mul, hb, hbx, map_mul]; rfl⟩
        · obtain ⟨by', hby⟩ := hy_mem
          exact ⟨b * by', by rw [map_mul, hb, hby, map_mul]; rfl⟩

  have hϖtC0 : algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ≠ 0 := by
    intro h
    apply hϖt0
    apply hinjAK
    rw [← hAK, h, map_zero, map_zero]
  have hnzd : mkS (MvPowerSeries.C (σ₁ ϖt)) ∈ nonZeroDivisors S := by
    have h := K4Ker.mem_nonZeroDivisors_of_flat Ψ hflat' (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) hϖtC0
    rw [hconst' ϖt] at h
    exact h
  have hιSinj : Function.Injective ιS :=
    IsLocalization.injective (M := Submonoid.powers (mkS (MvPowerSeries.C (σ₁ ϖt)))) Lloc
      ((Submonoid.powers_le).mpr hnzd)
  have h𝔑gens : mkS (MvPowerSeries.C (σ₁ ϖt)) ∈ 𝔑 ∧ mkS (MvPowerSeries.X 0) ∈ 𝔑 ∧ mkS (MvPowerSeries.X 1) ∈ 𝔑 := by
    rw [h𝔑]
    exact ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩
  have hBmem : ∀ b : ↥B, (b : ↥K) ∈ Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} := by
    intro b
    have hb2 : (b : ↥K) ∈ (Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A := (le_of_eq hB) b.2
    exact (Subalgebra.mem_restrictScalars (R := A)).mp hb2
  have hT : ∀ x ∈ {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}, ∃ i ∈ J, x * algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) = algebraMap ↥(chartAlgFin A (↥K) j) ↥K i := by
    rintro x ⟨i, hi, hx⟩
    exact ⟨i, hi, by rw [hAK]; exact hx⟩

  have hJpow : ∀ (k : ℕ) (d : ↥(chartAlgFin A (↥K) j)), d ∈ J ^ k → ∃ bd : ↥B, (bd : ↥K) * algebraMap A ↥K ϖt ^ k = (d : ↥K) := by
    intro k
    induction k with
    | zero =>
        intro d hd
        exact ⟨ι d, by rw [pow_zero, mul_one]; rfl⟩
    | succ k ih =>
        intro d hd
        rw [pow_succ'] at hd
        refine Submodule.mul_induction_on hd ?_ ?_
        · intro i hi d' hd'
          obtain ⟨bd, hbd⟩ := ih d' hd'
          have hbi : (i : ↥K) * (algebraMap A ↥K ϖt)⁻¹ ∈ B := by
            rw [hB, Subalgebra.mem_restrictScalars]
            refine Algebra.subset_adjoin ⟨i, hi, ?_⟩
            rw [mul_assoc, inv_mul_cancel₀ hϖtK, mul_one]
          refine ⟨⟨_, hbi⟩ * bd, ?_⟩
          have hrw : (((⟨_, hbi⟩ * bd : ↥B)) : ↥K) * algebraMap A ↥K ϖt ^ (k + 1) =
              (i : ↥K) * ((bd : ↥K) * algebraMap A ↥K ϖt ^ k) * ((algebraMap A ↥K ϖt)⁻¹ * algebraMap A ↥K ϖt) := by
            rw [Subalgebra.coe_mul, pow_succ]
            show (i : ↥K) * (algebraMap A ↥K ϖt)⁻¹ * (bd : ↥K) * (algebraMap A ↥K ϖt ^ k * algebraMap A ↥K ϖt) = _
            ring
          rw [hrw, hbd, inv_mul_cancel₀ hϖtK, mul_one, Subalgebra.coe_mul]
        · intro x' y' ihx ihy
          obtain ⟨b₁, hb₁⟩ := ihx
          obtain ⟨b₂, hb₂⟩ := ihy
          exact ⟨b₁ + b₂, by rw [Subalgebra.coe_add, add_mul, hb₁, hb₂, Subalgebra.coe_add]⟩
  have hkerle : ∀ b : ↥B, ρ b = 0 →
      b ∈ Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hCB c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j))) := by
    intro b hb0

    obtain ⟨N, c, hcJ, hbc⟩ := K4Ker.exists_pow_mul_eq_of_mem_adjoin J (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) hϖtJ {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} hT (hBmem b)

    have hker0 : (⟨Φ b, hΦR b⟩ : ↥Rloc) ∈ Ideal.span {(⟨ιS (mkS (MvPowerSeries.C (σ₁ ϖ))), hιR (mkS (MvPowerSeries.C (σ₁ ϖ)))⟩ : ↥Rloc)} :=
      (hρker _).mp (by rw [← hρ]; exact hb0)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hker0
    have hΦb : Φ b = (w : Lloc) * ιS (mkS (MvPowerSeries.C (σ₁ ϖ))) := by
      have := congrArg Subtype.val hw
      exact this.symm

    obtain ⟨M, ν, hν, hwν⟩ := K4Ker.exists_pow_mul_eq_of_mem_closure (mkS (MvPowerSeries.C (σ₁ ϖt))) 𝔑
      h𝔑gens.1 (mkS (MvPowerSeries.X 0)) (mkS (MvPowerSeries.X 1)) h𝔑gens.2.1 h𝔑gens.2.2 w.2

    have hbcB : b * algebraMap A ↥B ϖt ^ N = ι c := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, hι]
      show (b : ↥K) * algebraMap A ↥K ϖt ^ N = (c : ↥K)
      rw [← hAK, hbc]
      rfl
    have hΦc : Φ b * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) ^ N = ιS (Ψ c) := by
      have h1 := congrArg Φ hbcB
      rw [map_mul, map_pow Φ (algebraMap A ↥B ϖt) N] at h1
      have h2 : Φ (algebraMap A ↥B ϖt) = ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) := by
        have heq : algebraMap A ↥B ϖt = ι (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) := by
          apply Subtype.ext
          rw [hι, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
        rw [heq, hι, hΦ1', hconst']
      rw [h2] at h1
      rw [h1, hι, hΦ1']

    have hS : Ψ c * mkS (MvPowerSeries.C (σ₁ ϖt)) ^ M =
        mkS (MvPowerSeries.C (σ₁ ϖ)) * (ν * mkS (MvPowerSeries.C (σ₁ ϖt)) ^ N) := by
      apply hιSinj
      rw [map_mul ιS, map_pow ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) M, ← hΦc, hΦb, map_mul ιS, map_mul ιS,
        map_pow ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) N, ← hwν]
      ring

    have hmem : Ψ (c * algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ^ M) ∈
        Ideal.map Ψ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ} * J ^ (M + N)) := by
      rw [map_mul Ψ, map_pow Ψ (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) M, hconst' ϖt, hS, Ideal.map_mul, Ideal.map_span,
        Set.image_singleton, hconst' ϖ, Ideal.map_pow, hmapJ', pow_add 𝔑 M N]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_mul hν (Ideal.pow_mem_pow h𝔑gens.1 N))

    have hy𝔐 : Ideal.map Ψ y ≠ ⊤ := by
      intro htop
      apply hmax.ne_top
      rw [← h𝔐]
      refine top_le_iff.mp ?_
      rw [← htop, Ideal.map_le_iff_le_comap, hcen']
    obtain ⟨s, hsy, hsc⟩ := K4Ker.exists_not_mem_and_mul_mem_of_flat' Ψ hflat' y hy𝔐 _ _ hmem
    obtain ⟨d, hd, hsd⟩ := Ideal.mem_span_singleton_mul.mp hsc
    obtain ⟨bd, hbd⟩ := hJpow (M + N) d hd

    have hK : ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) * (b : ↥K) = algebraMap A ↥K ϖ * (bd : ↥K) := by
      have hpow : (algebraMap A ↥K ϖt) ^ (M + N) ≠ 0 := pow_ne_zero _ hϖtK
      have e1 : (b : ↥K) * algebraMap A ↥K ϖt ^ N = (c : ↥K) := by
        rw [← hAK]; exact hbc
      have e2 : algebraMap A ↥K ϖ * (d : ↥K) = (s : ↥K) * ((c : ↥K) * algebraMap A ↥K ϖt ^ M) := by
        have h := congrArg (algebraMap ↥(chartAlgFin A (↥K) j) ↥K) hsd
        simp only [map_mul, map_pow, hAK] at h
        exact h
      apply mul_right_cancel₀ hpow
      calc (s : ↥K) * (b : ↥K) * algebraMap A ↥K ϖt ^ (M + N)
          = (s : ↥K) * ((b : ↥K) * algebraMap A ↥K ϖt ^ N) * algebraMap A ↥K ϖt ^ M := by rw [pow_add]; ring
        _ = (s : ↥K) * ((c : ↥K) * algebraMap A ↥K ϖt ^ M) := by rw [e1]; ring
        _ = algebraMap A ↥K ϖ * (d : ↥K) := e2.symm
        _ = algebraMap A ↥K ϖ * (bd : ↥K) * algebraMap A ↥K ϖt ^ (M + N) := by rw [← hbd]; ring
    have hsb : ι s * b = ι (algebraMap A ↥(chartAlgFin A (↥K) j) ϖ) * bd := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hι, hι, Subalgebra.coe_algebraMap]
      exact hK
    have hsb_mem : ι s * b ∈ Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hCB c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j))) := by
      rw [hsb]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, hϖy, rfl⟩)

    obtain ⟨a₀, ha₀⟩ := hres s
    have ha₀u : IsUnit a₀ := by
      by_contra hnu
      have hmemA : a₀ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      rw [hϖ] at hmemA
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmemA
      apply hsy
      have h1 : algebraMap A ↥(chartAlgFin A (↥K) j) a₀ ∈ y := by
        rw [← he, map_mul]; exact Ideal.mul_mem_left _ _ hϖy
      have h2 : s = (s - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) + algebraMap A ↥(chartAlgFin A (↥K) j) a₀ := by ring
      rw [h2]; exact Ideal.add_mem _ ha₀ h1
    obtain ⟨u, hu⟩ := ha₀u
    have hfinal : b = algebraMap A ↥B (↑u⁻¹ : A) * (ι s * b - ι (s - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) * b) := by
      have h3 : ι s * b - ι (s - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) * b = algebraMap A ↥B a₀ * b := by
        have heq : algebraMap A ↥B a₀ = ι (algebraMap A ↥(chartAlgFin A (↥K) j) a₀) := by
          apply Subtype.ext
          rw [hι, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
        rw [heq, map_sub]; ring
      rw [h3, ← mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, one_mul]
    rw [hfinal]
    refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hsb_mem ?_)
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, ha₀, rfl⟩)
  exact ⟨ρ, hρ, hsurjρ, fun b => ⟨hkerle b, hker₁ b⟩, hconstρ⟩

end S_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_coordRing_surjective_ker_eq_span_of_chartMap_of_localFibreMap_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_coordRing_surjective_ker_eq_span_of_chartMap_of_localFibreMap_of_dvd (solution)
