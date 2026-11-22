-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_reflection_with_conductor
-- status  : ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T20:16:22.163599+00:00
-- url     : https://prove2.me/submissions/1a62a74e-9a18-4883-8744-aa0840bc0dd1

import Mathlib.Algebra.Field.Shrink
import Theorems.Thm_MasulloGRH_completedHeckeLFunction_eq_of_ringEquiv
import Theorems.Thm_MasulloGRH_completedHeckeLFunction_functional_equation_explicit

set_option autoImplicit false

open MasulloGRH NumberField

private theorem const_cpow_analytic {b : ℂ} (hb : b ≠ 0) {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) : AnalyticAt ℂ (fun z => b ^ g z) s := by
  simpa only [Complex.cpow_def_of_ne_zero hb] using
    ((analyticAt_const (v := Complex.log b)).fun_mul hg).cexp'

private theorem scaledGamma_regular {b : ℂ} (hb : b ≠ 0) {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) (him : (g s).im ≠ 0) :
    AnalyticAt ℂ (fun z => b ^ (-g z) * Complex.Gamma (g z)) s ∧
      b ^ (-g s) * Complex.Gamma (g s) ≠ 0 := by
  have hGamma : Complex.Gamma (g s) ≠ 0 := Complex.Gamma_ne_zero fun n h =>
    him (by simpa using congrArg Complex.im h)
  have hAnalytic : AnalyticAt ℂ Complex.Gamma (g s) := by
    rcases meromorphicNFAt_iff_analyticAt_or.mp
        (MeromorphicNFOn.Gamma (Set.mem_univ (g s))) with h | ⟨_, _, hzero⟩
    · exact h
    · exact (hGamma hzero).elim
  exact ⟨(const_cpow_analytic hb hg.neg).fun_mul (hAnalytic.comp hg),
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hb)) hGamma⟩

private theorem gammaFactor_meromorphic {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter F) : MeromorphicOn χ.gammaFactor Set.univ := by
  classical
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  unfold HeckeCharacter.gammaFactor
  apply MeromorphicOn.fun_prod
  intro w _ s _
  unfold HeckeCharacter.archLFactor
  split
  · exact (const_cpow_analytic hπ (by fun_prop)).meromorphicAt.fun_mul
      ((Meromorphic.Gamma _).comp_analyticAt (by fun_prop))
  · exact (const_cpow_analytic h2π (by fun_prop)).meromorphicAt.fun_mul
      ((Meromorphic.Gamma _).comp_analyticAt (by fun_prop))

private theorem gammaFactor_regular {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ T : ℝ, ∀ s : ℂ, T ≤ |s.im| → AnalyticAt ℂ χ.gammaFactor s ∧ χ.gammaFactor s ≠ 0 := by
  classical
  refine ⟨1 + ∑ w : InfinitePlace F, |χ.archExponent w|, ?_⟩
  intro s hs
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  have hlocal (w : InfinitePlace F) :
      AnalyticAt ℂ (χ.archLFactor w) s ∧ χ.archLFactor w s ≠ 0 := by
    have hbound : |χ.archExponent w| ≤ ∑ v : InfinitePlace F, |χ.archExponent v| :=
      Finset.single_le_sum (fun v _ => abs_nonneg (χ.archExponent v)) (Finset.mem_univ w)
    have hshift : s.im + χ.archExponent w ≠ 0 := by
      intro heq
      have him : s.im = -χ.archExponent w := by linarith
      rw [him, abs_neg] at hs
      linarith
    unfold HeckeCharacter.archLFactor
    split
    · apply scaledGamma_regular hπ (by fun_prop)
      simpa [Complex.mul_im] using
        (div_ne_zero hshift (by norm_num : (2 : ℝ) ≠ 0))
    · apply scaledGamma_regular h2π (by fun_prop)
      simpa [Complex.mul_im] using hshift
  exact ⟨Finset.analyticAt_fun_prod _ (fun w _ => (hlocal w).1),
    Finset.prod_ne_zero_iff.mpr (fun w _ => (hlocal w).2)⟩

private theorem completed_eq_product {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    {s : ℂ} (hγ : AnalyticAt ℂ χ.gammaFactor s) (hγ₀ : χ.gammaFactor s ≠ 0) :
    completedHeckeLFunction χ s = χ.gammaFactor s * heckeLFunction χ s := by
  have hL : MeromorphicNFOn (heckeLFunction χ) Set.univ := by
    unfold heckeLFunction
    split
    · rename_i h
      exact h.choose_spec.1
    · exact analyticOnNhd_const.meromorphicNFOn
  have hprod : MeromorphicOn (fun z => χ.gammaFactor z * heckeLFunction χ z) Set.univ :=
    (gammaFactor_meromorphic χ).fun_mul hL.meromorphicOn
  have hnormal : MeromorphicNFAt (fun z => χ.gammaFactor z * heckeLFunction χ z) s :=
    (hL (Set.mem_univ s)).smul_analytic hγ hγ₀
  unfold completedHeckeLFunction
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hprod (Set.mem_univ s),
    toMeromorphicNFAt_eq_self.mpr hnormal]

theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ (A : ℝ) (W : ℂ), 0 < A ∧ ‖W‖ = 1 ∧
      ∀ σ : ℝ, ∃ T : ℝ, ∀ s : ℂ, s.re = σ → T ≤ |s.im| →
        heckeLFunction χ s =
          W * (A : ℂ) ^ ((1 / 2 : ℂ) - s) *
            ((χ⁻¹).gammaFactor (1 - s) / χ.gammaFactor s) *
            heckeLFunction χ⁻¹ (1 - s) := by
  let : Small.{0} F := small_of_injective (Module.finBasis ℚ F).equivFun.injective
  let K := Shrink.{0} F
  let e : F ≃+* K := (Shrink.ringEquiv (α := F)).symm
  let : NumberField K := NumberField.of_ringEquiv F K e
  obtain ⟨transport, htransport⟩ := completedHeckeLFunction_eq_of_ringEquiv F K e
  obtain ⟨ε, A, hε, hA, hFE⟩ := completedHeckeLFunction_functional_equation_explicit K (transport χ)
  obtain ⟨T₁, h₁⟩ := gammaFactor_regular χ
  obtain ⟨T₂, h₂⟩ := gammaFactor_regular χ⁻¹
  refine ⟨A, ε⁻¹, hA, by simp [norm_inv, hε], fun _ => ⟨max T₁ T₂, ?_⟩⟩
  intro s _ hs
  obtain ⟨hγ, hγ₀⟩ := h₁ s ((le_max_left _ _).trans hs)
  have hreflectedHeight : |(1 - s).im| = |s.im| := by simp
  have hs₂ : T₂ ≤ |(1 - s).im| := by
    rw [hreflectedHeight]
    exact (le_max_right _ _).trans hs
  obtain ⟨hγ', hγ₀'⟩ := h₂ (1 - s) hs₂
  have hreflection := hFE s
  rw [← map_inv, ← htransport χ⁻¹, ← htransport χ,
    completed_eq_product χ⁻¹ hγ' hγ₀', completed_eq_product χ hγ hγ₀] at hreflection
  have hε₀ : ε ≠ 0 := by
    intro he
    simp [he] at hε
  have hA₀ : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hpow : (A : ℂ) ^ (s - 1 / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hA₀)
  calc
    heckeLFunction χ s =
        ((χ⁻¹).gammaFactor (1 - s) * heckeLFunction χ⁻¹ (1 - s)) /
          (ε * (A : ℂ) ^ (s - 1 / 2) * χ.gammaFactor s) :=
      (eq_div_iff (mul_ne_zero (mul_ne_zero hε₀ hpow) hγ₀)).2 (by rw [hreflection]; ring)
    _ = _ := by
      rw [show (1 / 2 : ℂ) - s = -(s - 1 / 2) by ring, Complex.cpow_neg]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
