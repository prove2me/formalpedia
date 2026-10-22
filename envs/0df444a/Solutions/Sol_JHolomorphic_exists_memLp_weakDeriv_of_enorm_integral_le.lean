-- Prove2me | solution 1 for JHolomorphic.exists_memLp_weakDeriv_of_enorm_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T20:57:27.611561+00:00
-- url     : https://prove2.me/submissions/8d3af09a-69b2-43b7-bd2a-dc35595fdc44

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Theorems.Thm_JHolomorphic_exists_memLp_eq_integral_inner
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations



namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal

/-- Real `C^∞` functions with compact support in `U`. -/
def testSub (U : Set ℂ) : Submodule ℝ (ℂ → ℝ) where
  carrier := {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U}
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    exact ⟨h1.add k1, h2.add k2, (tsupport_add φ ψ).trans (Set.union_subset h3 k3)⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  smul_mem' := by
    rintro a φ ⟨h1, h2, h3⟩
    refine ⟨h1.const_smul a, h2.smul_left, ?_⟩
    exact (tsupport_smul_subset_right (fun _ => a) φ).trans h3

lemma integrableOn_of_memLp_restrict {E : Type*} [NormedAddCommGroup E] {μ : Measure ℂ}
    [IsFiniteMeasureOnCompacts μ] {U : Set ℂ}
    {P : ℝ≥0∞} (hP : 1 ≤ P) {g : ℂ → E} (hg : MemLp g P (μ.restrict U)) :
    ∀ K ⊆ U, IsCompact K → IntegrableOn g K μ := by
  intro K hK hKc
  have h1 : MemLp g P (μ.restrict K) := hg.mono_measure (Measure.restrict_mono hK le_rfl)
  haveI : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
  exact h1.integrable hP

theorem exists_memLp_weakDeriv_real {U : Set ℂ} (hU : IsOpen U) (p : ℝ) (hp : 1 < p)
    {f : ℂ → ℝ} (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K) (v : ℂ) (C : ℝ)
    (hC : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ‖∫ z, fderiv ℝ φ z v • f z‖ₑ ≤
        ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict U)) :
    ∃ g : ℂ → ℝ, MemLp g (ENNReal.ofReal p) (volume.restrict U) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ z, fderiv ℝ φ z v • f z = -∫ z, φ z • g z := by
  set μ := volume.restrict U
  set P := ENNReal.ofReal p
  set Q := ENNReal.ofReal (p / (p - 1))
  have hp1 : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hpq : (p / (p - 1)).HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  haveI : Q.HolderConjugate P := hpq.ennrealOfReal
  haveI : Fact (1 ≤ Q) := ⟨ENNReal.one_le_ofReal.2 hp1.le⟩
  have hQ1 : 1 < Q := ENNReal.one_lt_ofReal.2 hp1
  have hQt : Q ≠ ⊤ := ENNReal.ofReal_ne_top
  set T := testSub U
  have hmem : ∀ φ : T, MemLp (φ : ℂ → ℝ) Q μ := fun φ =>
    (φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1)
  have hint : ∀ φ : T, Integrable fun z => fderiv ℝ (φ : ℂ → ℝ) z v • f z := by
    intro φ
    obtain ⟨h1, h2, h3⟩ := fderiv_apply_isTestFunction φ.2.1 φ.2.2.1 φ.2.2.2 v
    exact integrable_smul_of_integrableOn_compact hf h1.continuous.continuousOn h2 h3
  -- the embedding of test functions into `L^q`
  let A : T →ₗ[ℝ] Lp ℝ Q μ :=
    { toFun := fun φ => (hmem φ).toLp φ
      map_add' := fun φ ψ => by
        rw [← MemLp.toLp_add]; rfl
      map_smul' := fun a φ => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]; rfl }
  -- the functional
  let Λ : T →ₗ[ℝ] ℝ :=
    { toFun := fun φ => ∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • f z
      map_add' := fun φ ψ => by
        have hd1 := (φ.2.1.differentiable (by simp))
        have hd2 := (ψ.2.1.differentiable (by simp))
        have : (fun z => fderiv ℝ ((φ + ψ : T) : ℂ → ℝ) z v • f z) =
            fun z => fderiv ℝ (φ : ℂ → ℝ) z v • f z + fderiv ℝ (ψ : ℂ → ℝ) z v • f z := by
          funext z
          rw [Submodule.coe_add, fderiv_add (hd1 z) (hd2 z)]
          simp [add_smul, add_mul]
        rw [this, integral_add (hint φ) (hint ψ)]
      map_smul' := fun a φ => by
        have : (fun z => fderiv ℝ ((a • φ : T) : ℂ → ℝ) z v • f z) =
            fun z => a • (fderiv ℝ (φ : ℂ → ℝ) z v • f z) := by
          funext z
          rw [Submodule.coe_smul, fderiv_const_smul_field]
          simp [smul_smul, mul_assoc]
        rw [this, integral_smul]; rfl }
  set C' := max C 0
  have hbound : ∀ φ : T, ‖Λ φ‖ ≤ C' * ‖A φ‖ := by
    intro φ
    have h := hC φ φ.2.1 φ.2.2.1 φ.2.2.2
    have hA : ‖A φ‖ = (eLpNorm (φ : ℂ → ℝ) Q μ).toReal := Lp.norm_toLp _ (hmem φ)
    rw [hA]
    have hfin : eLpNorm (φ : ℂ → ℝ) Q μ ≠ ⊤ := (hmem φ).eLpNorm_ne_top
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    show ‖∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • f z‖ ≤ _
    simpa [Real.norm_eq_abs, toReal_enorm] using this
  have hker : LinearMap.ker A ≤ LinearMap.ker Λ := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have := hbound φ
    rw [hφ, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let ℓ0 : LinearMap.range A →ₗ[ℝ] ℝ :=
    ((LinearMap.ker A).liftQ Λ hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hℓ0 : ∀ φ : T, ℓ0 ⟨A φ, LinearMap.mem_range_self A φ⟩ = Λ φ := by
    intro φ
    have : A.quotKerEquivRange.symm ⟨A φ, LinearMap.mem_range_self A φ⟩ =
        Submodule.Quotient.mk φ := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk A φ).symm
    simp only [ℓ0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, this,
      Submodule.liftQ_apply]
  have hℓ0b : ∀ y, ‖ℓ0 y‖ ≤ C' * ‖y‖ := by
    rintro ⟨y, φ, rfl⟩
    rw [hℓ0]
    exact hbound φ
  obtain ⟨ℓ, hℓ, -⟩ := exists_extension_norm_eq (LinearMap.range A) (ℓ0.mkContinuous C' hℓ0b)
  obtain ⟨G, hG, hrep⟩ := exists_memLp_eq_integral_inner μ Q P hQ1 hQt ℓ
  refine ⟨fun z => -G z, hG.neg, fun φ hφ hφc hφU => ?_⟩
  set φT : T := ⟨φ, hφ, hφc, hφU⟩
  have e1 : ∫ z, fderiv ℝ φ z v • f z = ℓ (A φT) := by
    have := hℓ ⟨A φT, LinearMap.mem_range_self A φT⟩
    rw [this, LinearMap.mkContinuous_apply, hℓ0]; rfl
  have e2 : ℓ (A φT) = ∫ z in U, φ z * G z := by
    rw [hrep]
    refine integral_congr_ae ?_
    filter_upwards [(hmem φT).coeFn_toLp] with z hz
    show inner ℝ ((A φT) z) (G z) = φ z * G z
    have : (A φT) z = φ z := hz
    rw [this]
    simp [mul_comm]
  have hsupp : ∀ z ∉ U, φ z * G z = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφU h)), zero_mul]
  rw [e1, e2, setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, ← integral_neg]
  congr 1; funext z; simp [smul_eq_mul]

theorem exists_memLp_weakDeriv_of_enorm_integral_le_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → E} (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K) (v : ℂ) (C : ℝ)
    (hC : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ‖∫ z, fderiv ℝ φ z v • f z‖ₑ ≤
        ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict U)) :
    ∃ g : ℂ → E, MemLp g (ENNReal.ofReal p) (volume.restrict U) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ z, fderiv ℝ φ z v • f z = -∫ z, φ z • g z := by
  set b := Module.finBasis ℝ E
  set L : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hL : ∀ i x, L i x = b.repr x i := fun i x => rfl
  have hint : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      Integrable fun z => fderiv ℝ φ z v • f z := by
    intro φ hφ hφc hφU
    obtain ⟨h1, h2, h3⟩ := fderiv_apply_isTestFunction hφ hφc hφU v
    exact integrable_smul_of_integrableOn_compact hf h1.continuous.continuousOn h2 h3
  have hcomm : ∀ i (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, fderiv ℝ φ z v • L i (f z) = L i (∫ z, fderiv ℝ φ z v • f z) := by
    intro i φ hφ hφc hφU
    rw [← (L i).integral_comp_comm (hint φ hφ hφc hφU)]
    simp only [map_smul]
  have key : ∀ i, ∃ g : ℂ → ℝ, MemLp g (ENNReal.ofReal p) (volume.restrict U) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ z, fderiv ℝ φ z v • L i (f z) = -∫ z, φ z • g z := by
    intro i
    refine exists_memLp_weakDeriv_real hU p hp (fun K hK hKc => (L i).integrable_comp
      (hf K hK hKc)) v (‖L i‖ * C) (fun φ hφ hφc hφU => ?_)
    rw [hcomm i φ hφ hφc hφU]
    calc _ ≤ ‖L i‖ₑ * ‖∫ z, fderiv ℝ φ z v • f z‖ₑ := (L i).le_opENorm _
      _ ≤ ‖L i‖ₑ * (ENNReal.ofReal C *
            eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict U)) := by
          gcongr; exact hC φ hφ hφc hφU
      _ = _ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, mul_assoc]
  choose g hg hg' using key
  have hP : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  refine ⟨fun z => ∑ i, g i z • b i, ?_, fun φ hφ hφc hφU => ?_⟩
  · refine memLp_finsetSum _ fun i _ => ?_
    have := (ContinuousLinearMap.toSpanSingleton ℝ (b i)).comp_memLp' (hg i)
    exact this
  have hgi : ∀ i, Integrable fun z => φ z • g i z := fun i => by
    have h1 := integrableOn_of_memLp_restrict (μ := volume) (U := U) (g := g i) hP
    exact integrable_smul_of_integrableOn_compact (h1 (hg i)) hφ.continuous.continuousOn hφc hφU
  have e1 : ∫ z, φ z • ∑ i, g i z • b i = ∑ i, (∫ z, φ z • g i z) • b i := by
    have : (fun z => φ z • ∑ i, g i z • b i) = fun z => ∑ i, (φ z • g i z) • b i := by
      funext z; rw [Finset.smul_sum]; simp only [smul_assoc]
    rw [this, integral_finset_sum _ fun i _ => (hgi i).smul_const (b i)]
    simp only [integral_smul_const]
  rw [e1]
  have e2 : ∀ i, ∫ z, φ z • g i z = -(b.repr (∫ z, fderiv ℝ φ z v • f z) i) := by
    intro i
    rw [← hL, ← hcomm i φ hφ hφc hφU, hg' i φ hφ hφc hφU, neg_neg]
  simp only [e2, neg_smul, Finset.sum_neg_distrib, neg_neg]
  exact (b.sum_repr _).symm

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ContDiff ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → E} (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K) (v : ℂ) (C : ℝ)
    (hC : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ‖∫ z, fderiv ℝ φ z v • f z‖ₑ ≤
        ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict U)) :
    ∃ g : ℂ → E, MemLp g (ENNReal.ofReal p) (volume.restrict U) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ z, fderiv ℝ φ z v • f z = -∫ z, φ z • g z :=
  exists_memLp_weakDeriv_of_enorm_integral_le_aux p hp hU hf v C hC
