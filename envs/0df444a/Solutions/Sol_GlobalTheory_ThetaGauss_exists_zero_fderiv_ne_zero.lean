-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.exists_zero_fderiv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:25:53.324555+00:00
-- url     : https://prove2.me/submissions/cb7cb170-884d-4ebb-a1cd-1975930688c5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaGauss_hasDerivAt_line
import Theorems.Thm_GlobalTheory_ThetaGauss_frequently_ne_zero
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_fderiv_sq_quot
import Theorems.Thm_GlobalTheory_ThetaGauss_differentiable_fderiv_apply
import Theorems.Thm_GlobalTheory_ThetaGauss_fderiv_translate
import Theorems.Thm_GlobalTheory_ThetaGauss_eq_exp_of_ode
import Theorems.Thm_GlobalTheory_ThetaGauss_eq_zero_of_tendsto
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_eq_smul
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_herm_swap
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_span_eq_top
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ v : Fin g → ℂ, v ≠ 0 → ∃ a, θ a = 0 ∧ fderiv ℂ θ a v ≠ 0 := by
  intro g Hm hH Λ hd hΛ χ θ hθ h0 hχ hθt v hv
  by_contra hm
  push_neg at hm
  have hD := differentiable_fderiv_apply hθ v
  obtain ⟨ψ, hψ, hψ'⟩ := exists_fderiv_sq_quot hθ h0 v hD hm
  set D : (Fin g → ℂ) → ℂ := fun z => fderiv ℂ θ z v with hDdef
  have hD₂ := differentiable_fderiv_apply hD v
  obtain ⟨c, hc⟩ := ThetaTranslSpan.exists_eq_smul hH Λ hΛ χ θ (fun z => fderiv ℂ D z v - ψ z) hχ
    hθ h0 hθt (hD₂.sub hψ) (fun a ha z => by
      set j : (Fin g → ℂ) → ℂ := fun z => χ a * Complex.exp
        (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) with hjdef
      set l : ℂ := Real.pi * (star a ⬝ᵥ Hm.mulVec v)
      have hj : ∀ z (t : ℂ), j (z + t • v) = j z * Complex.exp (t * l) := fun z t => by
        simp only [j, l, mulVec_add, dotProduct_add, mulVec_smul, dotProduct_smul, smul_eq_mul]
        rw [mul_assoc (χ a), ← Complex.exp_add]; congr 2; ring
      have hj0 : ∀ z, j z ≠ 0 := fun z =>
        mul_ne_zero (fun h => by simpa [h] using hχ a ha) (Complex.exp_ne_zero _)
      have hjc : Continuous j := by
        simp only [j, dotProduct, mulVec]
        fun_prop
      have e0 : ∀ z, θ (z + a) = j z * θ z := hθt a ha
      have e1 : ∀ z, D (z + a) = j z * (D z + l * θ z) := fderiv_translate hθ hθ a v j l hj e0
      have e2 := fderiv_translate hD (hD.add (hθ.const_mul l)) a v j l hj e1 z
      have e3 : fderiv ℂ (D + fun y => l * θ y) z v = fderiv ℂ D z v + l * D z := by
        rw [((hD z).hasFDerivAt.add ((hθ z).hasFDerivAt.const_mul l)).fderiv]; rfl
      have e4 : ψ (z + a) = j z * (ψ z + 2 * l * D z + l ^ 2 * θ z) := by
        haveI := frequently_ne_zero hθ h0 z
        have c1 : Continuous fun z => ψ (z + a) := hψ.continuous.comp (by fun_prop)
        have c2 : Continuous fun z => j z * (ψ z + 2 * l * D z + l ^ 2 * θ z) := by
          have := hψ.continuous; have := hD.continuous; have := hθ.continuous
          fun_prop
        refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[{x | θ x ≠ 0}] z)
          ((c1.tendsto z).mono_left nhdsWithin_le_nhds)
          ((c2.tendsto z).mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        refine mul_right_cancel₀ (mul_ne_zero (hj0 y) hy) ?_
        have a1 : ψ (y + a) * θ (y + a) = D (y + a) ^ 2 := hψ' _
        have a2 : ψ y * θ y = D y ^ 2 := hψ' _
        rw [e0, e1] at a1
        linear_combination a1 - j y ^ 2 * a2
      change _ = j z * _
      rw [e2, e3, e4]
      simp only [Pi.add_apply]
      ring)
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h0
  obtain ⟨α, hα⟩ := eq_exp_of_ode (hasDerivAt_line hθ z v) (hasDerivAt_line hD z v) c
    (fun t => by
      have a1 := congrFun hc (z + t • v)
      have a2 := hψ' (z + t • v)
      simp only [Pi.smul_apply, smul_eq_mul] at a1
      linear_combination θ (z + t • v) * a1 + a2) (by simpa using hz)
  simp only [zero_smul, add_zero] at hα
  obtain ⟨t₀, ht₀, hc₀⟩ : ∃ t₀ : ℂ, t₀ ≠ 0 ∧ (c / 2 * t₀ ^ 2).re ≤ 0 := by
    rcases le_total (c / 2).re 0 with h | h
    · exact ⟨1, one_ne_zero, by simpa using h⟩
    · exact ⟨Complex.I, Complex.I_ne_zero, by
        rw [Complex.I_sq, mul_neg_one, Complex.neg_re]; linarith⟩
  let B : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun x y => (star x ⬝ᵥ Hm.mulVec y).re
  have hB : ∀ x y, B x y = B y x := fun x y => by
    simp only [B]; rw [ThetaTranslSpan.herm_swap hH]; rfl
  have hBadd : ∀ x y, B (x + y) (x + y) = B x x + 2 * B y x + B y y := fun x y => by
    have := hB x y
    simp only [B, star_add, mulVec_add, add_dotProduct, dotProduct_add, Complex.add_re] at this ⊢
    linarith
  let u : (Fin g → ℂ) → ℝ := fun x => ‖θ x‖ * Real.exp (-(Real.pi / 2 * B x x))
  have huc : Continuous u := by
    have := hθ.continuous
    simp only [u, B, dotProduct, mulVec]
    fun_prop
  have hup : ∀ a ∈ Λ, ∀ x, u (x + a) = u x := fun a ha x => by
    simp only [u]
    rw [hθt a ha, norm_mul, norm_mul, hχ a ha, one_mul, Complex.norm_exp, hBadd, mul_right_comm,
      ← Real.exp_add, mul_comm]
    congr 2
    simp [B]
    ring
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ
  haveI hL : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨ThetaTranslSpan.span_eq_top hH Λ fun v => (hΛ v).1⟩
  set w := t₀ • v with hw
  have hw0 : w ≠ 0 := smul_ne_zero ht₀ hv
  have hpos : 0 < B w w := (Complex.pos_iff.1 (hH.dotProduct_mulVec_pos hw0)).1
  set A : ℝ := (α * t₀).re - Real.pi * B w z
  set β : ℝ := Real.pi / 2 * B w w - (c / 2 * t₀ ^ 2).re with hβ
  have hβ0 : 0 < β := by have := Real.pi_pos; have : 0 < Real.pi / 2 * B w w := by positivity
                         linarith
  have hun : ∀ n : ℕ, u (z + n • w) = u z * Real.exp (n * (A - β * n)) := fun n => by
    have hre : ∀ x : ℂ, ((n : ℂ) * x).re = n * x.re := fun x => by simp
    have b1 : B (n • w) z = n * B w z := by
      simp only [B]
      rw [star_nsmul, smul_dotProduct, nsmul_eq_mul, hre]
    have b2 : B (n • w) (n • w) = n * (n * B w w) := by
      simp only [B]
      rw [star_nsmul, smul_dotProduct, mulVec_smul, dotProduct_smul, nsmul_eq_mul, nsmul_eq_mul,
        hre, hre]
    have b3 : θ (z + n • w) = θ z * Complex.exp (n * (α * t₀) + n * (n * (c / 2 * t₀ ^ 2))) := by
      rw [hw, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hα]; congr 2; ring
    simp only [u]
    rw [hBadd, b1, b2, b3, norm_mul, Complex.norm_exp, mul_assoc, mul_assoc, ← Real.exp_add,
      ← Real.exp_add, Complex.add_re, hre, hre, hre]
    congr 2
    simp only [A, β]
    ring
  have hzero := eq_zero_of_tendsto L huc hup z w (by
    simp only [hun]
    rw [← mul_zero (u z)]
    refine Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)
    refine tendsto_natCast_atTop_atTop.atTop_mul_atBot₀ ?_
    exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hβ0)))
  exact absurd hzero (mul_pos (norm_pos_iff.2 hz) (Real.exp_pos _)).ne'
end GlobalTheory.ThetaGauss
