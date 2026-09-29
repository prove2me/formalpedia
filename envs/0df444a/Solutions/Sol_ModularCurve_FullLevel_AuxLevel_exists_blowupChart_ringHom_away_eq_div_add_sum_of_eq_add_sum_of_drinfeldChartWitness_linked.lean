-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_blowupChart_ringHom_away_eq_div_add_sum_of_eq_add_sum_of_drinfeldChartWitness_linked
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b752c690-1739-5556-88c9-4c2876a21847

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

import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_away_eq_div_add_sum_of_eq_add_sum_of_drinfeldChartWitness_linked
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace Transfer

open IsLocalRing

theorem exists_ringHom_adjoin {C K S L : Type*} [CommRing C] [Field K] [Algebra C K]
    (hinj : Function.Injective (algebraMap C K))
    (t : C) (ht : t ≠ 0)
    (T : Set K) (hT : ∀ x ∈ T, ∃ i : C, x * algebraMap C K t = algebraMap C K i)
    [CommRing S] (Ψ : C →+* S) (s : S) (hs : Ψ t = s) [CommRing L] [Algebra S L] [IsLocalization.Away s L] :
    ∃ Φ : ↥(Algebra.adjoin C T) →+* L,
      (∀ a : C, Φ (algebraMap C _ a) = algebraMap S L (Ψ a)) ∧
      (∀ (x : ↥(Algebra.adjoin C T)) (i : C), (x : K) * algebraMap C K t = algebraMap C K i →
          Φ x * algebraMap S L s = algebraMap S L (Ψ i)) := by
  classical
  have htK : algebraMap C K t ≠ 0 := (map_ne_zero_iff _ hinj).mpr ht

  let Cl := Localization.Away t
  let f₁ : Cl →+* K := IsLocalization.Away.lift t (g := algebraMap C K) (isUnit_iff_ne_zero.mpr htK)
  have hf₁ : ∀ c : C, f₁ (algebraMap C Cl c) = algebraMap C K c := fun c =>
    IsLocalization.Away.lift_eq t _ c
  let f₁A : Cl →ₐ[C] K := { toRingHom := f₁, commutes' := fun c => hf₁ c }
  let f₂ : Cl →+* L := IsLocalization.Away.lift t (g := (algebraMap S L).comp Ψ)
    (by rw [RingHom.comp_apply, hs]; exact IsLocalization.Away.algebraMap_isUnit (S := L) s)
  have hf₂ : ∀ c : C, f₂ (algebraMap C Cl c) = algebraMap S L (Ψ c) := fun c =>
    IsLocalization.Away.lift_eq t _ c

  have hf₁inj : Function.Injective f₁A := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨c, d⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) z
    have hspec := IsLocalization.mk'_spec Cl c d
    have h1 : f₁ (IsLocalization.mk' Cl c d) * f₁ (algebraMap C Cl d) = f₁ (algebraMap C Cl c) := by
      rw [← map_mul, hspec]
    have hz' : f₁ (IsLocalization.mk' Cl c d) = 0 := hz
    rw [hz', zero_mul, hf₁] at h1
    have hc : c = 0 := hinj (by rw [← h1, map_zero])
    show IsLocalization.mk' Cl c d = 0
    rw [hc, IsLocalization.mk'_zero]
  let e : Cl ≃ₐ[C] ↥(f₁A.range) := AlgEquiv.ofInjective f₁A hf₁inj
  have he : ∀ z : Cl, ((e z : ↥(f₁A.range)) : K) = f₁ z := fun z => rfl
  have he' : ∀ w : ↥(f₁A.range), f₁ (e.symm w) = (w : K) := fun w => by
    rw [← he, AlgEquiv.apply_symm_apply]

  have hle : Algebra.adjoin C T ≤ f₁A.range := by
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨i, hi⟩ := hT x hx
    refine ⟨IsLocalization.mk' Cl i (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t), ?_⟩
    apply mul_right_cancel₀ htK
    have hsp : (IsLocalization.mk' Cl i (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t)) * algebraMap C Cl t =
        algebraMap C Cl i := IsLocalization.mk'_spec Cl i ⟨t, Submonoid.mem_powers t⟩
    calc f₁A (IsLocalization.mk' Cl i (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t)) * algebraMap C K t
        = f₁ (IsLocalization.mk' Cl i (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t)) * f₁ (algebraMap C Cl t) := by
          rw [hf₁]; rfl
      _ = f₁ (algebraMap C Cl i) := by rw [← map_mul, hsp]
      _ = x * algebraMap C K t := by rw [hf₁, ← hi]
  let Φ : ↥(Algebra.adjoin C T) →+* L :=
    f₂.comp ((e.symm : ↥(f₁A.range) →ₐ[C] Cl).toRingHom.comp (Subalgebra.inclusion hle).toRingHom)
  have hΦ : ∀ x : ↥(Algebra.adjoin C T), Φ x = f₂ (e.symm (Subalgebra.inclusion hle x)) := fun x => rfl
  refine ⟨Φ, ?_, ?_⟩
  · intro a
    rw [hΦ, AlgHom.commutes, AlgEquiv.commutes, hf₂]
  · intro x i hxi
    have hz : e.symm (Subalgebra.inclusion hle x) * algebraMap C Cl t = algebraMap C Cl i := by
      apply hf₁inj
      show f₁ _ = f₁ _
      rw [map_mul, he', hf₁, hf₁, Subalgebra.coe_inclusion]
      exact hxi
    rw [hΦ, ← hs, ← hf₂ t, ← map_mul, hz, hf₂]

theorem mem_adjoin_of_forall {C K S L : Type*} [CommRing C] [Field K] [Algebra C K]
    (t : C) (T : Set K) [CommRing S] (Ψ : C →+* S) (s : S) [CommRing L] [Algebra S L] [IsLocalization.Away s L]
    (I : Ideal S)
    (hT : ∀ x ∈ T, ∃ i : C, Ψ i ∈ I ∧ x * algebraMap C K t = algebraMap C K i)
    (Φ : ↥(Algebra.adjoin C T) →+* L)
    (hΦ₁ : ∀ a : C, Φ (algebraMap C _ a) = algebraMap S L (Ψ a))
    (hΦ₂ : ∀ (x : ↥(Algebra.adjoin C T)) (i : C), (x : K) * algebraMap C K t = algebraMap C K i →
          Φ x * algebraMap S L s = algebraMap S L (Ψ i)) :
    ∀ b : ↥(Algebra.adjoin C T), Φ b ∈ Algebra.adjoin S {z : L | ∃ i ∈ I, z * algebraMap S L s = algebraMap S L i} := by
  intro b
  obtain ⟨b, hb⟩ := b
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, hi, hxi⟩ := hT x hx
      have h2 := hΦ₂ ⟨x, Algebra.subset_adjoin hx⟩ i hxi
      exact Algebra.subset_adjoin ⟨Ψ i, hi, h2⟩
  | algebraMap c =>
      change Φ (algebraMap C (Algebra.adjoin C T) c) ∈ _
      rw [hΦ₁]
      exact Subalgebra.algebraMap_mem _ (Ψ c)
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : ↥(Algebra.adjoin C T)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add]
      exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : ↥(Algebra.adjoin C T)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul]
      exact Subalgebra.mul_mem _ ihx ihy

theorem exists_pow_mul_eq_of_mem_adjoin' {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]
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

end Transfer

theorem Transfer.mem_nonZeroDivisors_of_flat {C S : Type*} [CommRing C] [IsDomain C] [CommRing S] (Ψ : C →+* S)
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

theorem Transfer.exists_not_mem_and_mul_mem_of_flat' {C S : Type*} [CommRing C] [CommRing S] (Ψ : C →+* S)
    (hflat : letI : Algebra C S := Ψ.toAlgebra; Module.Flat C S)
    (𝔪 : Ideal C) (h𝔪 : Ideal.map Ψ 𝔪 ≠ ⊤) (𝔞 : Ideal C) (c : C) (hc : Ψ c ∈ Ideal.map Ψ 𝔞) :
    ∃ s : C, s ∉ 𝔪 ∧ s * c ∈ 𝔞 := by
  letI : Algebra C S := Ψ.toAlgebra
  haveI : Module.Flat C S := hflat
  exact Transfer.exists_not_mem_and_mul_mem_of_flat 𝔪 h𝔪 𝔞 c hc

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
    (a : ↥(chartAlgFin A (↥K) j)) (haJ : a ∈ J) (ha0 : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0) :
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
        let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
        let Ψ : ↥(chartAlgFin A (↥K) j) →+* S := (e₁ : CMP →+* S).comp (toC.comp germY)
        let s : S := Ψ a
        let L := Localization.Away s
        let ι : S →+* L := algebraMap S L
        let I : Ideal S := Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}
        let 𝔐 : Ideal S := Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}
        let R : Subalgebra S L := Algebra.adjoin S {z : L | ∃ i ∈ I, z * ι s = ι i}
        ∃ Φ : ↥Ba →+* L,

          (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba), Φ ⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ = ι (Ψ c)) ∧
          (∀ (x : ↥Ba) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J →
              (x : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) → Φ x * ι s = ι (Ψ i)) ∧

          s ∈ nonZeroDivisors S ∧

          (∀ b : ↥Ba, Φ b ∈ R) ∧

          (∀ b : ↥Ba,
            (∃ (r : L) (_ : r ∈ R) (n : ℕ) (m : Fin n → S) (r' : Fin n → L),
                (∀ k, m k ∈ 𝔐) ∧ (∀ k, r' k ∈ R) ∧
                Φ b = (ι (mkS (MvPowerSeries.C (σ₁ ϖt))) * IsLocalization.Away.invSelf (S := L) s) * r + ∑ k, ι (m k) * r' k) →
            ∃ (b' : ↥K) (_ : b' ∈ Ba) (n : ℕ) (c : Fin n → ↥(chartAlgFin A (↥K) j)) (b'' : Fin n → ↥K),
              (∀ k, c k ∈ y) ∧ (∀ k, b'' k ∈ Ba) ∧
              (b : ↥K) = algebraMap A ↥K ϖt * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * b' + ∑ k, ((c k : ↥(chartAlgFin A (↥K) j)) : ↥K) * b'' k) := by
  intro STK CMP toC S mkS germY Ba Ψ s Lloc ι I 𝔐 R
  classical

  have hW := hW₁
  obtain ⟨hconst, -, -, -, -, -, -⟩ := hW
  have hK1 := ModularCurve.FullLevel.AuxLevel.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  obtain ⟨hK1i, -, -⟩ := hK1
  have hK2 := ModularCurve.FullLevel.AuxLevel.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hconst
  obtain ⟨hK2a, hK2b, hK2c, hK2d, hK2d2, hK2d3, hK2f, hK2f', hK2e⟩ := hK2
  have hK3 := ModularCurve.FullLevel.AuxLevel.map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ hK1i hK2a hK2b hK2d ⟨hK2f, hK2f'⟩
  obtain ⟨hmapJ, -, hJy, hϖtJ⟩ := hK3

  have hs : s = Ψ a := rfl
  have hι : ι = algebraMap S Lloc := rfl
  have hI : I = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := rfl
  have h𝔐 : 𝔐 = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := rfl
  have hcen : Ideal.comap Ψ 𝔐 = y := hK2a
  have hconst' : ∀ a₀ : A, Ψ (algebraMap A ↥(chartAlgFin A (↥K) j) a₀) = mkS (MvPowerSeries.C (σ₁ a₀)) := hK2c
  have hres : ∀ c : ↥(chartAlgFin A (↥K) j), ∃ a₀ : A, c - algebraMap A ↥(chartAlgFin A (↥K) j) a₀ ∈ y := hK2d
  have hmax : 𝔐.IsMaximal := hK2f
  have hflat : (letI : Algebra ↥(chartAlgFin A (↥K) j) S := Ψ.toAlgebra; Module.Flat ↥(chartAlgFin A (↥K) j) S) := hK2e
  have hmapJ' : Ideal.map Ψ J = I := hmapJ

  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hAK : ∀ a₀ : A, algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap A ↥(chartAlgFin A (↥K) j) a₀) = algebraMap A ↥K a₀ :=
    fun a₀ => (IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K) j) ↥K a₀).symm
  have hinj : Function.Injective (algebraMap ↥(chartAlgFin A (↥K) j) ↥K) := fun a b h => Subtype.ext h
  have haC0 : a ≠ 0 := fun h => ha0 (by rw [h]; rfl)
  have hnzd : s ∈ nonZeroDivisors S := Transfer.mem_nonZeroDivisors_of_flat Ψ hflat a haC0
  have hιinj : Function.Injective ι :=
    IsLocalization.injective (M := Submonoid.powers s) Lloc ((Submonoid.powers_le).mpr hnzd)

  have hT : ∀ x ∈ {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)},
      ∃ i : ↥(chartAlgFin A (↥K) j), x * algebraMap ↥(chartAlgFin A (↥K) j) ↥K a = algebraMap ↥(chartAlgFin A (↥K) j) ↥K i := by
    rintro x ⟨i, hi, hx⟩
    exact ⟨i, hx⟩
  have hT2 : ∀ x ∈ {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)},
      ∃ i : ↥(chartAlgFin A (↥K) j), Ψ i ∈ I ∧ x * algebraMap ↥(chartAlgFin A (↥K) j) ↥K a = algebraMap ↥(chartAlgFin A (↥K) j) ↥K i := by
    rintro x ⟨i, hi, hx⟩
    refine ⟨i, ?_, hx⟩
    rw [← hmapJ']
    exact Ideal.mem_map_of_mem Ψ hi
  have hgen := Transfer.exists_ringHom_adjoin hinj a haC0
    {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} hT Ψ s rfl (L := Lloc)
  obtain ⟨Φ₀, hΦ₀1, hΦ₀2⟩ := hgen
  have hcl := Transfer.mem_adjoin_of_forall a
    {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} Ψ s (L := Lloc) I hT2 Φ₀ hΦ₀1 hΦ₀2

  have hBmem : ∀ b : ↥Ba, (b : ↥K) ∈ Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} :=
    fun b => (Subalgebra.mem_restrictScalars (R := A)).mp b.2
  let ιB : ↥Ba →+* ↥(Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}) :=
    { toFun := fun b => ⟨(b : ↥K), hBmem b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hιB : ∀ b : ↥Ba, ((ιB b : ↥(Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)})) : ↥K) = (b : ↥K) :=
    fun b => rfl
  let Φ : ↥Ba →+* Lloc := Φ₀.comp ιB
  have hΦR : ∀ b : ↥Ba, Φ b ∈ R := fun b => hcl (ιB b)
  have hΦC : ∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba), Φ ⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ = ι (Ψ c) := by
    intro c hc
    have heq : ιB ⟨(c : ↥K), hc⟩ =
        algebraMap ↥(chartAlgFin A (↥K) j) ↥(Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}) c :=
      Subtype.ext rfl
    show Φ₀ (ιB ⟨(c : ↥K), hc⟩) = ι (Ψ c)
    rw [heq]
    exact hΦ₀1 c
  have hΦJ : ∀ (x : ↥Ba) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J →
      (x : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) → Φ x * ι s = ι (Ψ i) := by
    intro x i hi hx
    exact hΦ₀2 (ιB x) i (by rw [hιB]; exact hx)

  have hCB : ∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba := fun c =>
    (Subalgebra.mem_restrictScalars (R := A)).mpr (Subalgebra.algebraMap_mem _ c)
  let ιC : ↥(chartAlgFin A (↥K) j) →+* ↥Ba :=
    { toFun := fun c => ⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hCB c⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hιC : ∀ c : ↥(chartAlgFin A (↥K) j), ιC c = ⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hCB c⟩ := fun c => rfl
  have hΦι : ∀ c : ↥(chartAlgFin A (↥K) j), Φ (ιC c) = ι (Ψ c) := fun c => hΦC c (hCB c)
  refine ⟨Φ, hΦC, hΦJ, hnzd, hΦR, ?_⟩

  have hIgens : mkS (MvPowerSeries.C (σ₁ ϖt)) ∈ I ∧ mkS (MvPowerSeries.X 0) ∈ I ∧ mkS (MvPowerSeries.X 1) ∈ I := by
    rw [hI]; exact ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩
  have hsI : s ∈ I := by rw [← hmapJ']; exact Ideal.mem_map_of_mem Ψ haJ

  have h𝔐y : 𝔐 ≤ Ideal.map Ψ y := by
    rw [h𝔐, Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [SetLike.mem_coe, ← hconst' ϖ]; exact Ideal.mem_map_of_mem Ψ hϖy
    · exact Ideal.map_mono hJy (hmapJ'.symm ▸ hIgens.2.1)
    · exact Ideal.map_mono hJy (hmapJ'.symm ▸ hIgens.2.2)

  obtain ⟨𝔞, h𝔞⟩ : ∃ 𝔞 : ℕ → Ideal ↥(chartAlgFin A (↥K) j), 𝔞 = fun M => y * J ^ (M + 1) ⊔ Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖt} * J ^ M := ⟨_, rfl⟩
  have h𝔞mul : ∀ M k : ℕ, 𝔞 M * J ^ k ≤ 𝔞 (M + k) := by
    intro M k
    rw [h𝔞]
    simp only
    rw [Ideal.sup_mul, mul_assoc, mul_assoc, ← pow_add, ← pow_add, show M + 1 + k = M + k + 1 by omega]
  have hspow : ∀ k : ℕ, s ^ k ∈ Ideal.map Ψ (J ^ k) := by
    intro k
    have : Ψ (a ^ k) ∈ Ideal.map Ψ (J ^ k) := Ideal.mem_map_of_mem Ψ (Ideal.pow_mem_pow haJ k)
    rw [map_pow Ψ a k] at this
    exact this
  have hmapmul : ∀ (I₁ I₂ : Ideal ↥(chartAlgFin A (↥K) j)) (u₁ u₂ : S), u₁ ∈ Ideal.map Ψ I₁ → u₂ ∈ Ideal.map Ψ I₂ → u₁ * u₂ ∈ Ideal.map Ψ (I₁ * I₂) := by
    intro I₁ I₂ u₁ u₂ h₁ h₂
    rw [Ideal.map_mul]; exact Ideal.mul_mem_mul h₁ h₂

  obtain ⟨P, hP⟩ : ∃ P : Lloc → Prop, P = fun z => ∃ M : ℕ, ∃ ν : S, ν ∈ Ideal.map Ψ (𝔞 M) ∧ z * ι s ^ (M + 1) = ι ν := ⟨_, rfl⟩
  have hP0 : P 0 := by rw [hP]; exact ⟨0, 0, zero_mem _, by rw [map_zero]; simp⟩
  have hPadd : ∀ z₁ z₂ : Lloc, P z₁ → P z₂ → P (z₁ + z₂) := by
    intro z₁ z₂ h₁ h₂
    rw [hP] at h₁ h₂ ⊢
    obtain ⟨M₁, ν₁, h₁, e₁⟩ := h₁
    obtain ⟨M₂, ν₂, h₂, e₂⟩ := h₂
    refine ⟨M₁ + M₂ + 1, ν₁ * s ^ (M₂ + 1) + ν₂ * s ^ (M₁ + 1), ?_, ?_⟩
    · refine Ideal.add_mem _ ?_ ?_
      · have := hmapmul _ _ _ _ h₁ (hspow (M₂ + 1))
        exact Ideal.map_mono (h𝔞mul M₁ (M₂ + 1)) this
      · have := hmapmul _ _ _ _ h₂ (hspow (M₁ + 1))
        have h' := Ideal.map_mono (f := Ψ) (h𝔞mul M₂ (M₁ + 1)) this
        rw [show M₂ + (M₁ + 1) = M₁ + M₂ + 1 by omega] at h'
        exact h'
    · rw [add_mul, map_add, map_mul ι, map_mul ι, map_pow ι, map_pow ι, ← e₁, ← e₂]
      ring

  have hRpow : ∀ r : Lloc, r ∈ R → ∃ M : ℕ, ∃ ν : S, ν ∈ Ideal.map Ψ (J ^ M) ∧ r * ι s ^ M = ι ν := by
    intro r hr
    have hT3 : ∀ z ∈ {z : Lloc | ∃ i ∈ I, z * ι s = ι i}, ∃ i ∈ I, z * algebraMap S Lloc s = algebraMap S Lloc i := by
      rintro z ⟨i, hi, hz⟩; exact ⟨i, hi, hz⟩
    obtain ⟨M, ν, hν, e⟩ := Transfer.exists_pow_mul_eq_of_mem_adjoin' I s hsI {z : Lloc | ∃ i ∈ I, z * ι s = ι i} hT3 hr
    refine ⟨M, ν, ?_, e⟩
    rw [Ideal.map_pow, hmapJ']; exact hν

  have hPt : ∀ r : Lloc, r ∈ R → P ((ι (mkS (MvPowerSeries.C (σ₁ ϖt))) * IsLocalization.Away.invSelf (S := Lloc) s) * r) := by
    intro r hr
    obtain ⟨M, ν, hν, e⟩ := hRpow r hr
    rw [hP]
    refine ⟨M, mkS (MvPowerSeries.C (σ₁ ϖt)) * ν, ?_, ?_⟩
    · rw [← hconst' ϖt, h𝔞]
      refine Ideal.map_mono le_sup_right ?_
      exact hmapmul _ _ _ _ (Ideal.mem_map_of_mem Ψ (Ideal.mem_span_singleton_self _)) hν
    · have hinv : ι s * IsLocalization.Away.invSelf (S := Lloc) s = 1 := IsLocalization.Away.mul_invSelf s
      rw [map_mul ι, ← e, pow_succ (ι s) M]
      calc ι (mkS (MvPowerSeries.C (σ₁ ϖt))) * IsLocalization.Away.invSelf (S := Lloc) s * r * (ι s ^ M * ι s)
          = ι (mkS (MvPowerSeries.C (σ₁ ϖt))) * (r * ι s ^ M) * (ι s * IsLocalization.Away.invSelf (S := Lloc) s) := by ring
        _ = ι (mkS (MvPowerSeries.C (σ₁ ϖt))) * (r * ι s ^ M) := by rw [hinv, mul_one]
  have hPm : ∀ (m₀ : S) (r : Lloc), m₀ ∈ 𝔐 → r ∈ R → P (ι m₀ * r) := by
    intro m₀ r hm₀ hr
    obtain ⟨M, ν, hν, e⟩ := hRpow r hr
    rw [hP]
    refine ⟨M, m₀ * ν * s, ?_, ?_⟩
    · have h1 : m₀ * ν * s ∈ Ideal.map Ψ (y * J ^ M * J) :=
        hmapmul _ _ _ _ (hmapmul _ _ _ _ (h𝔐y hm₀) hν) (Ideal.mem_map_of_mem Ψ haJ)
      rw [h𝔞]
      refine Ideal.map_mono ?_ h1
      rw [mul_assoc, ← pow_succ]
      exact le_sup_left
    · rw [map_mul ι, map_mul ι, ← e, pow_succ (ι s) M]
      ring

  intro x hx0
  obtain ⟨r, hr, n, m, r', hm, hr', hΦeq⟩ := hx0
  have hPx : P (Φ x) := by
    rw [hΦeq]
    refine hPadd _ _ (hPt r hr) ?_
    refine Finset.sum_induction _ (fun z => P z) (fun z₁ z₂ h₁ h₂ => hPadd z₁ z₂ h₁ h₂) hP0 ?_
    intro k _
    exact hPm (m k) (r' k) (hm k) (hr' k)
  rw [hP] at hPx
  obtain ⟨M, ν, hν, hΦx⟩ := hPx
  have hT' : ∀ x ∈ {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)},
      ∃ i ∈ J, x * algebraMap ↥(chartAlgFin A (↥K) j) ↥K a = algebraMap ↥(chartAlgFin A (↥K) j) ↥K i := by
    rintro x ⟨i, hi, hx⟩; exact ⟨i, hi, hx⟩
  obtain ⟨N, c, hcJ, hxc⟩ := Transfer.exists_pow_mul_eq_of_mem_adjoin J a haJ
    {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} hT' (hBmem x)

  have hxcB : x * ιC a ^ N = ιC c := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, hιC, hιC]
    exact hxc
  have hΦc : Φ x * ι s ^ N = ι (Ψ c) := by
    have h1 := congrArg Φ hxcB
    rw [map_mul Φ, map_pow Φ (ιC a) N, hΦι a, hΦι c] at h1
    exact h1

  have hS : Ψ (c * a ^ (M + 1)) = ν * s ^ N := by
    apply hιinj
    rw [map_mul Ψ, map_pow Ψ a (M + 1), ← hs, map_mul ι, map_pow ι s (M + 1), ← hΦc, map_mul ι, map_pow ι s N, ← hΦx]
    ring
  have hmem : Ψ (c * a ^ (M + 1)) ∈ Ideal.map Ψ (𝔞 (M + N)) := by
    rw [hS]
    exact Ideal.map_mono (h𝔞mul M N) (hmapmul _ _ _ _ hν (hspow N))

  have hy𝔐 : Ideal.map Ψ y ≠ ⊤ := by
    intro htop
    apply hmax.ne_top
    refine top_le_iff.mp ?_
    rw [← htop, Ideal.map_le_iff_le_comap]
    exact le_of_eq hcen.symm
  obtain ⟨u, huy, huc⟩ := Transfer.exists_not_mem_and_mul_mem_of_flat' Ψ hflat y hy𝔐 _ _ hmem
  have huc' : u * (c * a ^ (M + 1)) ∈ y * J ^ (M + N + 1) ⊔ Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖt} * J ^ (M + N) := by
    rw [h𝔞] at huc; exact huc
  obtain ⟨d₁, hd₁, d₂, hd₂, hd⟩ := Submodule.mem_sup.mp huc'

  have hJpow : ∀ (k : ℕ) (d : ↥(chartAlgFin A (↥K) j)), d ∈ J ^ k → ∃ bd : ↥Ba, (bd : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ k = (d : ↥K) := by
    intro k
    induction k with
    | zero =>
        intro d hd
        exact ⟨ιC d, by rw [pow_zero, mul_one]; rfl⟩
    | succ k ih =>
        intro d hd
        rw [pow_succ'] at hd
        refine Submodule.mul_induction_on hd ?_ ?_
        · intro i hi d' hd'
          obtain ⟨bd, hbd⟩ := ih d' hd'
          have hbi : (i : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ Ba :=
            (Subalgebra.mem_restrictScalars (R := A)).mpr (Algebra.subset_adjoin ⟨i, hi, inv_mul_cancel_right₀ ha0 _⟩)
          refine ⟨⟨_, hbi⟩ * bd, ?_⟩
          have hrw : (((⟨_, hbi⟩ * bd : ↥Ba)) : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ (k + 1) =
              (i : ↥K) * ((bd : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ k) * ((((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) := by
            rw [Subalgebra.coe_mul, pow_succ]
            show (i : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * (bd : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ k * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) = _
            ring
          rw [hrw, hbd, inv_mul_cancel₀ ha0, mul_one, Subalgebra.coe_mul]
        · intro x' y' ihx ihy
          obtain ⟨b₁, hb₁⟩ := ihx
          obtain ⟨b₂, hb₂⟩ := ihy
          exact ⟨b₁ + b₂, by rw [Subalgebra.coe_add, add_mul, hb₁, hb₂, Subalgebra.coe_add]⟩

  obtain ⟨Q, hQ⟩ : ∃ Q : ↥Ba → Prop, Q = fun (b : ↥Ba) => ∃ (b' : ↥K) (_ : b' ∈ Ba) (n : ℕ) (c : Fin n → ↥(chartAlgFin A (↥K) j)) (b'' : Fin n → ↥K),
      (∀ k, c k ∈ y) ∧ (∀ k, b'' k ∈ Ba) ∧
      ((b : ↥Ba) : ↥K) = algebraMap A ↥K ϖt * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * b' + ∑ k, ((c k : ↥(chartAlgFin A (↥K) j)) : ↥K) * b'' k := ⟨_, rfl⟩
  have hQadd : ∀ b₁ b₂ : ↥Ba, Q b₁ → Q b₂ → Q (b₁ + b₂) := by
    intro b₁ b₂ h₁ h₂
    rw [hQ] at h₁ h₂ ⊢
    obtain ⟨b'₁, hb'₁, n₁, c₁, b''₁, hc₁, hb''₁, e₁⟩ := h₁
    obtain ⟨b'₂, hb'₂, n₂, c₂, b''₂, hc₂, hb''₂, e₂⟩ := h₂
    refine ⟨b'₁ + b'₂, Ba.add_mem hb'₁ hb'₂, n₁ + n₂, Fin.append c₁ c₂, Fin.append b''₁ b''₂, ?_, ?_, ?_⟩
    · intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]; exact hc₁ i
      · rw [Fin.append_right]; exact hc₂ i
    · intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]; exact hb''₁ i
      · rw [Fin.append_right]; exact hb''₂ i
    · rw [Subalgebra.coe_add, e₁, e₂, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      ring
  have hQmul : ∀ (e : ↥Ba) (b : ↥Ba), Q b → Q (e * b) := by
    intro e b h
    rw [hQ] at h ⊢
    obtain ⟨b', hb', n, c, b'', hc, hb'', eq⟩ := h
    refine ⟨(e : ↥K) * b', Ba.mul_mem e.2 hb', n, c, fun k => (e : ↥K) * b'' k, hc, fun k => Ba.mul_mem e.2 (hb'' k), ?_⟩
    rw [Subalgebra.coe_mul, eq, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
  have hQy : ∀ (y₀ : ↥(chartAlgFin A (↥K) j)) (hy₀ : y₀ ∈ y) (b : ↥Ba), Q (ιC y₀ * b) := by
    intro y₀ hy₀ b
    rw [hQ]
    refine ⟨0, Ba.zero_mem, 1, fun _ => y₀, fun _ => (b : ↥K), fun _ => hy₀, fun _ => b.2, ?_⟩
    rw [Subalgebra.coe_mul, hιC]
    simp
  have htBa : ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ Ba :=
    (Subalgebra.mem_restrictScalars (R := A)).mpr (Algebra.subset_adjoin ⟨_, hϖtJ, inv_mul_cancel_right₀ ha0 _⟩)
  obtain ⟨bt, hbt⟩ : ∃ bt : ↥Ba, (bt : ↥K) = ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ :=
    ⟨⟨_, htBa⟩, rfl⟩
  have hϖtK : ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K) = algebraMap A ↥K ϖt := hAK ϖt
  have hQt : ∀ b : ↥Ba, Q (bt * b) := by
    intro b
    rw [hQ]
    refine ⟨(b : ↥K), b.2, 0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, fun k => Fin.elim0 k, ?_⟩
    rw [Subalgebra.coe_mul, Fin.sum_univ_zero, add_zero, hbt, hϖtK]

  have hNB1 : ∀ (T : ℕ) (d : ↥(chartAlgFin A (↥K) j)), d ∈ y * J ^ T → ∃ b : ↥Ba, Q b ∧ (b : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ T = (d : ↥K) := by
    intro T d hd
    refine Submodule.mul_induction_on hd ?_ ?_
    · intro y₀ hy₀ jj hjj
      obtain ⟨bd, hbd⟩ := hJpow T jj hjj
      refine ⟨ιC y₀ * bd, hQy y₀ hy₀ bd, ?_⟩
      rw [Subalgebra.coe_mul, hιC, mul_assoc, hbd, Subalgebra.coe_mul]
    · intro x' y' ihx ihy
      obtain ⟨b₁, hb₁, e₁⟩ := ihx
      obtain ⟨b₂, hb₂, e₂⟩ := ihy
      exact ⟨b₁ + b₂, hQadd _ _ hb₁ hb₂, by rw [Subalgebra.coe_add, add_mul, e₁, e₂, Subalgebra.coe_add]⟩
  have hNB2 : ∀ (T : ℕ) (d : ↥(chartAlgFin A (↥K) j)), d ∈ Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖt} * J ^ T →
      ∃ b : ↥Ba, Q b ∧ (b : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ (T + 1) = (d : ↥K) := by
    intro T d hd
    refine Submodule.mul_induction_on hd ?_ ?_
    · intro r₀ hr₀ jj hjj
      obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.mp hr₀
      obtain ⟨bd, hbd⟩ := hJpow T jj hjj
      refine ⟨ιC e * (bt * bd), hQmul (ιC e) (bt * bd) (hQt bd), ?_⟩
      have key : (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = 1 := inv_mul_cancel₀ ha0
      have c1 : ((ιC e * (bt * bd) : ↥Ba) : ↥K) = (e : ↥K) * ((bt : ↥K) * (bd : ↥K)) := by
        rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hιC]
      have c2 : ((e * algebraMap A ↥(chartAlgFin A (↥K) j) ϖt * jj : ↥(chartAlgFin A (↥K) j)) : ↥K) =
          (e : ↥K) * ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K) * (jj : ↥K) := by
        rw [Subalgebra.coe_mul, Subalgebra.coe_mul]
      rw [c1, c2, hbt, ← hbd, pow_succ]
      linear_combination ((e : ↥K) * ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K) * (bd : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ T) * key
    · intro x' y' ihx ihy
      obtain ⟨b₁, hb₁, e₁⟩ := ihx
      obtain ⟨b₂, hb₂, e₂⟩ := ihy
      exact ⟨b₁ + b₂, hQadd _ _ hb₁ hb₂, by rw [Subalgebra.coe_add, add_mul, e₁, e₂, Subalgebra.coe_add]⟩
  obtain ⟨b₁, hb₁, e₁⟩ := hNB1 (M + N + 1) d₁ hd₁
  obtain ⟨b₂, hb₂, e₂⟩ := hNB2 (M + N) d₂ hd₂

  have hpow : (((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ (M + N + 1) ≠ 0 := pow_ne_zero _ ha0
  have hux : ιC u * x = b₁ + b₂ := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_add, hιC]
    apply mul_right_cancel₀ hpow
    have hd' : ((u * (c * a ^ (M + 1)) : ↥(chartAlgFin A (↥K) j)) : ↥K) = (d₁ : ↥K) + (d₂ : ↥K) := by
      rw [← hd]; rfl
    have hxc' : (x : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ N = (c : ↥K) := hxc
    calc (u : ↥K) * (x : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ (M + N + 1)
        = (u : ↥K) * (((x : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ N) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ (M + 1)) := by ring
      _ = (u : ↥K) * ((c : ↥K) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ (M + 1)) := by rw [hxc']
      _ = ((u * (c * a ^ (M + 1)) : ↥(chartAlgFin A (↥K) j)) : ↥K) := by push_cast; ring
      _ = (d₁ : ↥K) + (d₂ : ↥K) := hd'
      _ = ((b₁ : ↥K) + (b₂ : ↥K)) * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ^ (M + N + 1) := by rw [add_mul, e₁, ← e₂]
  have hQux : Q (ιC u * x) := by rw [hux]; exact hQadd _ _ hb₁ hb₂

  obtain ⟨a₀, ha₀⟩ := hres u
  have ha₀u : IsUnit a₀ := by
    by_contra hnu
    have hmemA : a₀ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    rw [hϖ] at hmemA
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmemA
    apply huy
    have h1 : algebraMap A ↥(chartAlgFin A (↥K) j) a₀ ∈ y := by
      rw [← he, map_mul]; exact Ideal.mul_mem_left _ _ hϖy
    have h2 : u = (u - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) + algebraMap A ↥(chartAlgFin A (↥K) j) a₀ := by ring
    rw [h2]; exact Ideal.add_mem _ ha₀ h1
  obtain ⟨w, hw⟩ := ha₀u
  have hιA : ∀ a₁ : A, algebraMap A ↥Ba a₁ = ιC (algebraMap A ↥(chartAlgFin A (↥K) j) a₁) := by
    intro a₁; apply Subtype.ext; rw [hιC]; exact (hAK a₁).symm
  have hfinal : x = algebraMap A ↥Ba (↑w⁻¹ : A) * (ιC u * x + ιC (algebraMap A ↥(chartAlgFin A (↥K) j) a₀ - u) * x) := by
    have h3 : ιC u * x + ιC (algebraMap A ↥(chartAlgFin A (↥K) j) a₀ - u) * x = algebraMap A ↥Ba a₀ * x := by
      rw [hιA, map_sub]; ring
    rw [h3, ← mul_assoc, ← map_mul, ← hw, Units.inv_mul, map_one, one_mul]
  have hQx : Q x := by
    rw [hfinal]
    refine hQmul _ _ (hQadd _ _ hQux ?_)
    have hneg : algebraMap A ↥(chartAlgFin A (↥K) j) a₀ - u ∈ y := by
      have : algebraMap A ↥(chartAlgFin A (↥K) j) a₀ - u = -(u - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) := by ring
      rw [this]; exact y.neg_mem ha₀
    exact hQy _ hneg x
  rw [hQ] at hQx
  exact hQx

end S_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_away_eq_div_add_sum_of_eq_add_sum_of_drinfeldChartWitness_linked
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_away_eq_div_add_sum_of_eq_add_sum_of_drinfeldChartWitness_linked (solution)
