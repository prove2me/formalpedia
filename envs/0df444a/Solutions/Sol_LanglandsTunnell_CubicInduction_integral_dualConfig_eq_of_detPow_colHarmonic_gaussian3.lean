-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_detPow_colHarmonic_gaussian3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d6d40beb-a55b-55e0-8508-b2f2cf0fa641

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_detPow_colHarmonic_gaussian3

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.StandardKernel LanglandsTunnell.Converse

noncomputable section

namespace Ws14D30

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

private theorem _root_.Ws14D30.ofReal_mul (r s : ℝ) : ofReal (r * s) = ofReal r * ofReal s := by
  rw [← ofRealHom_apply, ← ofRealHom_apply, ← ofRealHom_apply, map_mul]

p2m_export "Ws14D30" "ofReal_mul"
theorem algebraMap_eq_ofReal (q : ℚ) : algebraMap ℚ (InfiniteAdeleRing ℚ) q = ofReal (q : ℝ) := by
  funext v
  apply (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).injective
  rw [InfiniteAdeleRing.algebraMap_apply,
    show ofReal (q : ℝ) v = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm (q : ℝ)
      from rfl,
    RingEquiv.apply_symm_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  exact eq_ratCast (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)) q

theorem psiArch_ofReal (r : ℝ) :
    NumberField.StandardAddChar.psiArch (ofReal r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) := by
  rw [NumberField.StandardAddChar.psiArch_apply, finprod_unique, NumberField.StandardAddChar.psiArchPlace_apply]
  congr 2
  show (((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ)))
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm r) : ℝ) : ℂ)
    = (r : ℂ)
  rw [RingEquiv.apply_symm_apply]

theorem psiInf_ofReal (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (t : ℝ) :
    psiInf (ofReal t) = Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * t : ℝ) : ℂ)) := by
  rw [hpsiInf, algebraMap_eq_ofReal, ← ofReal_mul, psiArch_ofReal]

section Matrix23
variable (E : Matrix (Fin 2) (Fin 2) ℝ) (a₁ a₂ : ℝ) (v : Fin 2 → ℝ)

def MD (a₁ a₂ : ℝ) (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]

theorem mul_MD_zero (i : Fin 2) : (E * MD a₁ a₂ v) i 0 = (E.mulVec v) i / a₁ := by
  fin_cases i <;> simp [MD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;> ring

theorem mul_MD_one (i : Fin 2) : (E * MD a₁ a₂ v) i 1 = E i 1 * a₂⁻¹ := by
  fin_cases i <;> simp [MD, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_MD_two (i : Fin 2) : (E * MD a₁ a₂ v) i 2 = E i 0 := by
  fin_cases i <;> simp [MD, Matrix.mul_apply, Fin.sum_univ_two]

theorem sumsq_mul_MD :
    ∑ i : Fin 2, ∑ b : Fin 3, (E * MD a₁ a₂ v) i b ^ 2 =
      (a₂⁻¹ ^ 2 * (E 0 1 ^ 2 + E 1 1 ^ 2) + (E 0 0 ^ 2 + E 1 0 ^ 2)) +
        ∑ i : Fin 2, ((E.mulVec v) i / a₁) ^ 2 := by
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, mul_MD_zero, mul_MD_one, mul_MD_two]
  ring

end Matrix23

theorem integral_comp_mulVec (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : E.det ≠ 0) (f : (Fin 2 → ℝ) → ℂ) :
    ∫ v : Fin 2 → ℝ, f (E.mulVec v) = (|E.det|)⁻¹ * ∫ u : Fin 2 → ℝ, f u := by
  classical
  haveI : Invertible E := Matrix.invertibleOfIsUnitDet E (isUnit_iff_ne_zero.2 hE)
  let L : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLinearEquiv' E ‹_›
  let T : (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) := L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hT : (T : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = fun v => E.mulVec v := by
    funext v
    rfl
  have hTl : (T : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = ⇑(Matrix.toLin' E) := by
    rw [hT]; funext v; exact (Matrix.toLin'_apply E v).symm
  have hmap : Measure.map (T : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume = ENNReal.ofReal |(E.det)⁻¹| • volume := by
    have h := Measure.map_linearMap_addHaar_pi_eq_smul_addHaar (f := Matrix.toLin' E)
      (by rw [LinearMap.det_toLin']; exact hE) (volume : Measure (Fin 2 → ℝ))
    rw [LinearMap.det_toLin'] at h
    rw [hTl]
    exact h
  calc ∫ v : Fin 2 → ℝ, f (E.mulVec v) = ∫ v : Fin 2 → ℝ, f (T v) := by rw [hT]
    _ = ∫ u, f u ∂(Measure.map (T : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume) := (integral_map_equiv T f).symm
    _ = (|E.det|)⁻¹ * ∫ u : Fin 2 → ℝ, f u := by
        rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, Complex.real_smul,
          Complex.ofReal_inv]

theorem integral_comp_mulVec_div (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : E.det ≠ 0) (a₁ : ℝ) (ha₁ : a₁ ≠ 0)
    (f : (Fin 2 → ℝ) → ℂ) :
    ∫ v : Fin 2 → ℝ, f (fun i => (E.mulVec v) i / a₁) =
      (((a₁ ^ 2 * |E.det|⁻¹ : ℝ)) : ℂ) * ∫ u : Fin 2 → ℝ, f u := by
  have hE' : (a₁⁻¹ • E).det ≠ 0 := by
    rw [Matrix.det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha₁)) hE
  have h := integral_comp_mulVec (a₁⁻¹ • E) hE' f
  have hfun : (fun v : Fin 2 → ℝ => f (fun i => (E.mulVec v) i / a₁)) = fun v => f ((a₁⁻¹ • E).mulVec v) := by
    funext v; congr 1; funext i
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]; ring
  rw [hfun, h, Matrix.det_smul, Fintype.card_fin]
  congr 1
  have : |a₁⁻¹ ^ 2 * E.det| = (a₁ ^ 2)⁻¹ * |E.det| := by
    rw [abs_mul, abs_of_nonneg (by positivity), inv_pow]
  rw [this]
  push_cast
  rw [mul_inv, inv_inv]

end Ws14D30

open Ws14D30 LanglandsTunnell.CubicInduction in
theorem solution
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : a₂ ≠ 0) :
    (∫ v : Fin 2 → ℝ,
        S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
          psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
      = (((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ n *
          (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
          (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
          ((-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((e 1 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) - ((e 0 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)))) ^ δ) *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ) := by
  set E : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of e with hEdef
  have hdetU : IsUnit E.det := isUnit_iff_ne_zero.2 he
  set ρ₀ : ℝ := E⁻¹ 1 0 with hρ₀
  set ρ₁ : ℝ := E⁻¹ 1 1 with hρ₁
  have hrow : ∀ v : Fin 2 → ℝ, ρ₀ * (E.mulVec v) 0 + ρ₁ * (E.mulVec v) 1 = v 1 := by
    intro v
    have h : (E⁻¹.mulVec (E.mulVec v)) 1 = v 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetU, Matrix.one_mulVec]
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  set ξ : Fin 2 → ℝ := ![(a : ℝ) * a₁ * ρ₀, (a : ℝ) * a₁ * ρ₁] with hξ

  set f0 : (Fin 2 → ℝ) → ℂ := fun u =>
    (((u 0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) ^ 0 *
      (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ))) with hf0
  set fp : (Fin 2 → ℝ) → ℂ := fun u =>
    (((u 0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) ^ 1 *
      (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ))) with hfp
  set fm : (Fin 2 → ℝ) → ℂ := fun u =>
    (((u 0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) ^ 1 *
      (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ))) with hfm
  have hHB0 := LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two 0 1 (Or.inl rfl) ξ
  have hHBp := LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two 1 1 (Or.inl rfl) ξ
  have hHBm := LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two 1 (-1) (Or.inr rfl) ξ
  set Cst : ℂ := (((E 0 0 : ℝ) : ℂ) - Complex.I * ((E 1 0 : ℝ) : ℂ)) ^ n *
      (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (E 0 1 ^ 2 + E 1 1 ^ 2) + (E 0 0 ^ 2 + E 1 0 ^ 2)))) : ℂ) with hCst

  set α : ℂ := ((a₂⁻¹ : ℝ) : ℂ) * (((E 1 1 : ℝ) : ℂ) + Complex.I * ((E 0 1 : ℝ) : ℂ)) / 2 with hα
  set β : ℂ := ((a₂⁻¹ : ℝ) : ℂ) * (((E 1 1 : ℝ) : ℂ) - Complex.I * ((E 0 1 : ℝ) : ℂ)) / 2 with hβ
  have hg : ∀ v : Fin 2 → ℝ, gaussian3 (E * MD a₁ a₂ v) =
      (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (E 0 1 ^ 2 + E 1 1 ^ 2) + (E 0 0 ^ 2 + E 1 0 ^ 2)))) : ℂ) *
        (Real.exp (-(Real.pi * ∑ i : Fin 2, ((E.mulVec v) i / a₁) ^ 2)) : ℂ) := by
    intro v
    rw [gaussian3, sumsq_mul_MD, mul_add, neg_add, Real.exp_add, Complex.ofReal_mul]
  have hchar : ∀ v : Fin 2 → ℝ, psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) =
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * ((E.mulVec v) i / a₁) : ℝ) : ℂ))) := by
    intro v
    rw [psiInf_ofReal a psiInf hpsiInf, Fin.sum_univ_two]
    simp only [hξ, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (a : ℝ) * a₁ * ρ₀ * ((E.mulVec v) 0 / a₁) + (a : ℝ) * a₁ * ρ₁ * ((E.mulVec v) 1 / a₁) =
        (a : ℝ) * (ρ₀ * (E.mulVec v) 0 + ρ₁ * (E.mulVec v) 1) by first | (field_simp; ring) | field_simp, hrow]
    congr 1
    first | (push_cast; ring) | push_cast
  have hMD : ∀ v : Fin 2 → ℝ, (!![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0] : Matrix (Fin 2) (Fin 3) ℝ) = MD a₁ a₂ v := fun v => rfl
  have hexp : Real.exp (-(Real.pi * (((a : ℝ) * a₁ * (Matrix.of e)⁻¹ 1 0) ^ 2 + ((a : ℝ) * a₁ * (Matrix.of e)⁻¹ 1 1) ^ 2))) =
      Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) := by
    congr 1; ring
  rcases hδ with rfl | rfl
  ·
    have hpt : ∀ v : Fin 2 → ℝ,
        S (E * MD a₁ a₂ v) * psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) =
          Cst * f0 (fun i => (E.mulVec v) i / a₁) := by
      intro v
      rw [hS]
      beta_reduce
      rw [hg, hchar]
      simp only [mul_MD_zero, mul_MD_one, mul_MD_two, hCst, hf0, pow_zero, one_mul]
      push_cast
      ring
    calc (∫ v : Fin 2 → ℝ, S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
            psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
        = ∫ v : Fin 2 → ℝ, Cst * f0 (fun i => (E.mulVec v) i / a₁) := by
            congr 1; funext v; rw [hMD]; exact hpt v
      _ = Cst * ((((a₁ ^ 2 * |E.det|⁻¹ : ℝ)) : ℂ) * ∫ u : Fin 2 → ℝ, f0 u) := by
            rw [integral_const_mul, integral_comp_mulVec_div E he a₁ ha₁ f0]
      _ = _ := by
            rw [hf0, hHB0.2, hCst]
            simp only [hξ, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, hρ₀, hρ₁, hEdef,
              Matrix.of_apply, pow_zero, one_mul, mul_one]
            rw [hexp]
            push_cast
            ring
  ·
    have hpt : ∀ v : Fin 2 → ℝ,
        S (E * MD a₁ a₂ v) * psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) =
          Cst * (fun u : Fin 2 → ℝ => α * fp u + β * fm u) (fun i => (E.mulVec v) i / a₁) := by
      intro v
      rw [hS]
      beta_reduce
      rw [hg, hchar]
      simp only [mul_MD_zero, mul_MD_one, mul_MD_two, hCst, hfp, hfm, hα, hβ, pow_one]
      push_cast
      have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_three, Complex.I_mul_I]; ring
      ring_nf
      simp only [Complex.I_sq, hI3]
      ring_nf
    calc (∫ v : Fin 2 → ℝ, S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
            psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
        = ∫ v : Fin 2 → ℝ, Cst * (fun u : Fin 2 → ℝ => α * fp u + β * fm u) (fun i => (E.mulVec v) i / a₁) := by
            congr 1; funext v; rw [hMD]; exact hpt v
      _ = Cst * ((((a₁ ^ 2 * |E.det|⁻¹ : ℝ)) : ℂ) * ∫ u : Fin 2 → ℝ, (α * fp u + β * fm u)) := by
            rw [integral_const_mul, integral_comp_mulVec_div E he a₁ ha₁ (fun u => α * fp u + β * fm u)]
      _ = Cst * ((((a₁ ^ 2 * |E.det|⁻¹ : ℝ)) : ℂ) * (α * (∫ u : Fin 2 → ℝ, fp u) + β * ∫ u : Fin 2 → ℝ, fm u)) := by
            rw [integral_add (hHBp.1.const_mul α) (hHBm.1.const_mul β), integral_const_mul, integral_const_mul]
      _ = _ := by
            rw [hfp, hfm, hHBp.2, hHBm.2, hCst, hα, hβ]
            simp only [hξ, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, hρ₀, hρ₁, hEdef,
              Matrix.of_apply, pow_one, mul_one]
            rw [hexp]
            push_cast
            have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_three, Complex.I_mul_I]; ring
            ring_nf
            simp only [Complex.I_sq, hI3]
            ring_nf

#print axioms solution

end
end S_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_detPow_colHarmonic_gaussian3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_detPow_colHarmonic_gaussian3 (solution)
