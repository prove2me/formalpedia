-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnits2_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dae3dfd7-d831-545f-a3fd-a6abbc53e470

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnits2_ne_zero

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

noncomputable section

namespace OffConeVanishing

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_ratPrimeAt_lt_one : Valued.v (ratPrimeAt v) < 1 := by
  have h1 : v.valuation ℚ (Ideal.absNorm v.asIdeal : ℚ) < 1 := by
    have h := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ℚ) v
      (Ideal.absNorm v.asIdeal : 𝓞 ℚ)).mpr (Ideal.absNorm_mem v.asIdeal)
    simpa using h
  have h2 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := ℚ) v
    (Ideal.absNorm v.asIdeal : ℚ)
  have h3 := map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) (Ideal.absNorm v.asIdeal)
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at h3
  simp only [Function.comp_apply, Algebra.algebraMap_self_apply] at h3
  show Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) < 1
  rw [← h3, h2]
  exact h1

private theorem iotaGL_diagUnits2_mul_upperUnipotent3 (t₁ t₂ : (v.adicCompletion ℚ)ˣ)
    (x y z : v.adicCompletion ℚ) :
    iotaGL (diagUnits2 t₁ t₂) * upperUnipotent3 x y z =
      upperUnipotent3 ((t₁ : v.adicCompletion ℚ) * (t₂ : v.adicCompletion ℚ)⁻¹ * x)
        ((t₂ : v.adicCompletion ℚ) * y) ((t₁ : v.adicCompletion ℚ) * z) * iotaGL (diagUnits2 t₁ t₂) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, embedMat2, upperUnipotent3]
  field_simp

private theorem mem_integers_of_forall_psi_mul_eq_one (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (a : v.adicCompletion ℚ) (ha0 : a ≠ 0)
    (h : ∀ y : v.adicCompletion ℚ, y ∈ v.adicCompletionIntegers ℚ → ψv (a * y) = 1) :
    a ∈ v.adicCompletionIntegers ℚ := by
  by_contra ha
  obtain ⟨x₀, hx₀, hψ⟩ := hψ1
  have ha' : ¬ Valued.v a ≤ 1 := ha
  have hlt : 1 < Valued.v a := not_le.mp ha'
  have hv0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
  have hexp : WithZero.exp (1 : ℤ) ≤ Valued.v a := by
    rw [← WithZero.exp_log hv0] at hlt ⊢
    rw [WithZero.exp_le_exp]
    have h0 : (0 : ℤ) < WithZero.log (Valued.v a) := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_zero]
      exact hlt
    omega
  have hy : a⁻¹ * x₀ ∈ v.adicCompletionIntegers ℚ := by
    show Valued.v (a⁻¹ * x₀) ≤ 1
    rw [map_mul, map_inv₀]
    calc (Valued.v a)⁻¹ * Valued.v x₀ ≤ (Valued.v a)⁻¹ * Valued.v a := mul_le_mul_right (hx₀.trans hexp) _
      _ = 1 := inv_mul_cancel₀ hv0
  have hx := h (a⁻¹ * x₀) hy
  rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul] at hx
  exact hψ hx

end OffConeVanishing

open OffConeVanishing

theorem solution (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hinv : ∀ (g : LocalGL3 v) (x y z : v.adicCompletion ℚ),
      x ∈ v.adicCompletionIntegers ℚ → y ∈ v.adicCompletionIntegers ℚ → z ∈ v.adicCompletionIntegers ℚ →
        W (g * upperUnipotent3 x y z) = W g)
    (t₁ t₂ : (v.adicCompletion ℚ)ˣ) (hW0 : W (iotaGL (diagUnits2 t₁ t₂)) ≠ 0) :
    (t₁ : v.adicCompletion ℚ) * (t₂ : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ ∧
      (t₂ : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  have hW' : ∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v),
      W (upperUnipotent3 x y z * g) = ψv (x + y) * W g := hW
  have key : ∀ x y : v.adicCompletion ℚ, x ∈ v.adicCompletionIntegers ℚ → y ∈ v.adicCompletionIntegers ℚ →
      ψv ((t₁ : v.adicCompletion ℚ) * (t₂ : v.adicCompletion ℚ)⁻¹ * x + (t₂ : v.adicCompletion ℚ) * y) = 1 := by
    intro x y hx hy
    have h := hinv (iotaGL (diagUnits2 t₁ t₂)) x y 0 hx hy (zero_mem _)
    rw [iotaGL_diagUnits2_mul_upperUnipotent3, hW'] at h
    exact (mul_eq_right₀ hW0).mp h
  constructor
  · refine mem_integers_of_forall_psi_mul_eq_one v ψv hψ1 _ (mul_ne_zero t₁.ne_zero (inv_ne_zero t₂.ne_zero)) ?_
    intro y hy
    simpa using key y 0 hy (zero_mem _)
  · refine mem_integers_of_forall_psi_mul_eq_one v ψv hψ1 _ t₂.ne_zero ?_
    intro y hy
    simpa using key 0 y (zero_mem _) hy

end

end S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnits2_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnits2_ne_zero (solution)
