-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e60c9e7b-60a7-5228-a462-30effe8102fd

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.StandardKernel LanglandsTunnell.Converse

noncomputable section

namespace Ws23TateMLin

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

private theorem _root_.Ws23TateMLin.ofReal_mul (r s : ℝ) : ofReal (r * s) = ofReal r * ofReal s := by
  rw [← ofRealHom_apply, ← ofRealHom_apply, ← ofRealHom_apply, map_mul]

p2m_export "Ws23TateMLin" "ofReal_mul"
private theorem _root_.Ws23TateMLin.ofReal_neg (r : ℝ) : ofReal (-r) = -ofReal r := by
  rw [← ofRealHom_apply, ← ofRealHom_apply, map_neg]

p2m_export "Ws23TateMLin" "ofReal_neg"

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

theorem psiInf_mulShift_ofReal (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (y t : ℝ) :
    (psiInf.mulShift (ofReal y)) (ofReal t) = Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (y * t) : ℝ) : ℂ)) := by
  rw [AddChar.mulShift_apply, hpsiInf, algebraMap_eq_ofReal, ← ofReal_mul, ← ofReal_mul, psiArch_ofReal]

section Matrix23
variable (E : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ)

def N23 (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of ![fun b => (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 b + v 0 * (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 b,
              fun b => (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 b + v 1 * (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 b]

theorem mul_N23_zero (i : Fin 2) : (E * N23 v) i 0 = E i 0 := by
  simp [N23, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem mul_N23_one (i : Fin 2) : (E * N23 v) i 1 = E i 1 := by
  simp [N23, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem mul_N23_two (i : Fin 2) : (E * N23 v) i 2 = (E.mulVec v) i := by
  simp [N23, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.mulVec, dotProduct]

theorem mul_N23_castSucc (i j : Fin 2) : (E * N23 v) i (Fin.castSucc j) = E i j := by
  fin_cases j
  · exact mul_N23_zero E v i
  · exact mul_N23_one E v i

theorem sumsq_mul_N23 :
    ∑ i : Fin 2, ∑ b : Fin 3, (E * N23 v) i b ^ 2 =
      (∑ i : Fin 2, ∑ j : Fin 2, E i j ^ 2) + ∑ i : Fin 2, (E.mulVec v) i ^ 2 := by
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, mul_N23_zero, mul_N23_one, mul_N23_two]
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

theorem integral_cpow_mul_exp_neg_mul_sq {z : ℂ} (hz : -1 < z.re) {c : ℝ} (hc : 0 < c) :
    ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ z * Complex.exp (-((c : ℂ) * ((y : ℝ) : ℂ) ^ 2)) =
      (1 / 2 : ℂ) * ((c : ℝ) : ℂ) ^ (-((z + 1) / 2)) * Complex.Gamma ((z + 1) / 2) := by

  set g : ℝ → ℂ := fun s => (1 / 2 : ℂ) * (((s : ℝ) : ℂ) ^ ((z - 1) / 2) * Complex.exp (-((c : ℂ) * ((s : ℝ) : ℂ)))) with hg
  have hsub := MeasureTheory.integral_comp_rpow_Ioi g (p := 2) two_ne_zero
  have hlhs : ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ z * Complex.exp (-((c : ℂ) * ((y : ℝ) : ℂ) ^ 2)) =
      ∫ y in Set.Ioi (0 : ℝ), (|(2 : ℝ)| * y ^ ((2 : ℝ) - 1)) • g (y ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy : 0 < y := hy
    simp only [hg]
    rw [abs_of_pos two_pos, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Complex.real_smul]
    have h2 : ((y ^ (2 : ℝ) : ℝ) : ℂ) = ((y : ℝ) : ℂ) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; ring
    have hpow : ((y ^ (2 : ℝ) : ℝ) : ℂ) ^ ((z - 1) / 2) = ((y : ℝ) : ℂ) ^ (z - 1) := by
      rw [show (y ^ (2 : ℝ) : ℝ) = y * y by rw [Real.rpow_two]; ring, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hy.le hy.le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hy.ne')]
      congr 1; ring
    rw [hpow, h2]
    have hy0 : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
    have hz1 : ((y : ℝ) : ℂ) ^ z = ((y : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ (z - 1) := by
      rw [show z = 1 + (z - 1) by ring, Complex.cpow_add _ _ hy0, Complex.cpow_one]
      ring_nf
    rw [hz1]; push_cast; ring
  rw [hlhs, hsub, hg]
  simp only []
  rw [integral_const_mul]
  have hre : 0 < ((z + 1) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith
  have key := Complex.integral_cpow_mul_exp_neg_mul_Ioi hre hc
  have hI : ∫ s in Set.Ioi (0 : ℝ), ((s : ℝ) : ℂ) ^ ((z - 1) / 2) * Complex.exp (-((c : ℂ) * ((s : ℝ) : ℂ))) =
      (1 / (c : ℂ)) ^ ((z + 1) / 2) * Complex.Gamma ((z + 1) / 2) := by
    rw [← key]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    congr 2; ring
  rw [hI, one_div (c : ℂ), Complex.inv_cpow _ _ ?_, ← Complex.cpow_neg]
  · ring
  · rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_ne_zero.symm

theorem fourier_linear (c₀ c₁ : ℂ) (ξ : Fin 2 → ℝ) :
    (∫ u : Fin 2 → ℝ, (c₀ * ((u 0 : ℝ) : ℂ) + c₁ * ((u 1 : ℝ) : ℂ)) *
        (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ)))) =
      -Complex.I * (c₀ * ((ξ 0 : ℝ) : ℂ) + c₁ * ((ξ 1 : ℝ) : ℂ)) *
        (Real.exp (-(Real.pi * ∑ i : Fin 2, ξ i ^ 2)) : ℂ) := by
  have hp := LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two 1 1 (Or.inl rfl) ξ
  have hm := LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two 1 (-1) (Or.inr rfl) ξ
  simp only [pow_one] at hp hm
  obtain ⟨ip, ep⟩ := hp
  obtain ⟨im, em⟩ := hm
  set α : ℂ := (c₀ - Complex.I * c₁) / 2 with hα
  set β : ℂ := (c₀ + Complex.I * c₁) / 2 with hβ
  have hsplit : (fun u : Fin 2 → ℝ => (c₀ * ((u 0 : ℝ) : ℂ) + c₁ * ((u 1 : ℝ) : ℂ)) *
        (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ)))) =
      fun u => α * ((((u 0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ)))) +
        β * ((((u 0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ)))) := by
    funext u
    simp only [hα, hβ, Complex.ofReal_one, Complex.ofReal_neg]
    linear_combination (c₁ * ((u 1 : ℝ) : ℂ) * (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ)))) * Complex.I_sq
  rw [hsplit, integral_add (ip.const_mul α) (im.const_mul β), integral_const_mul, integral_const_mul, ep, em]
  simp only [hα, hβ, Complex.ofReal_one, Complex.ofReal_neg]
  linear_combination (Complex.I * c₁ * ((ξ 1 : ℝ) : ℂ) * (Real.exp (-(Real.pi * ∑ i : Fin 2, ξ i ^ 2)) : ℂ)) * Complex.I_sq

private theorem _root_.Ws23TateMLin.ofReal_one : ofReal (1 : ℝ) = 1 := (ofRealHom_apply 1).symm.trans (map_one ofRealHom)

p2m_export "Ws23TateMLin" "ofReal_one"
theorem mulShift_ofReal_one (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) : ψ.mulShift (ofReal (1 : ℝ)) = ψ := by
  rw [ofReal_one, AddChar.mulShift_one]

end Ws23TateMLin

open Ws23TateMLin LanglandsTunnell.CubicInduction in

theorem solution
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p₀ p₁ : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
      (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p₀ * ((M 0 2 : ℝ) : ℂ) +
        MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p₁ * ((M 1 2 : ℝ) : ℂ)) *
        gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    godementInner3 psiInf S (Matrix.of e) 1
      = (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p₀ * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) +
          MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p₁ * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) *
          (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ) := by
  set E : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of e with hEdef
  have hdetU : IsUnit E.det := isUnit_iff_ne_zero.2 he
  set ρ₀ : ℝ := E⁻¹ 1 0 with hρ₀
  set ρ₁ : ℝ := E⁻¹ 1 1 with hρ₁
  have hrow : ∀ v : Fin 2 → ℝ, ρ₀ * (E.mulVec v) 0 + ρ₁ * (E.mulVec v) 1 = v 1 := by
    intro v
    have h : (E⁻¹.mulVec (E.mulVec v)) 1 = v 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetU, Matrix.one_mulVec]
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  set c₀ : ℂ := MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((E v.1 v.2 : ℝ) : ℂ)) p₀ with hc₀
  set c₁ : ℂ := MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((E v.1 v.2 : ℝ) : ℂ)) p₁ with hc₁
  set ξ : Fin 2 → ℝ := ![(a : ℝ) * ρ₀, (a : ℝ) * ρ₁] with hξ
  set f : (Fin 2 → ℝ) → ℂ := fun u =>
    (c₀ * ((u 0 : ℝ) : ℂ) + c₁ * ((u 1 : ℝ) : ℂ)) *
      (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ))) with hf
  set Cst : ℂ := (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, E i j ^ 2)) : ℂ) with hCst
  have hpt : ∀ v : Fin 2 → ℝ,
      S (E * N23 v) * psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) = Cst * f (E.mulVec v) := by
    intro v
    have hev : (fun w : Fin 2 × Fin 2 => (((E * N23 v) w.1 (Fin.castSucc w.2) : ℝ) : ℂ)) =
        fun w : Fin 2 × Fin 2 => ((E w.1 w.2 : ℝ) : ℂ) := by
      funext w; rw [mul_N23_castSucc]
    have hg : gaussian3 (E * N23 v) =
        (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, E i j ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, (E.mulVec v) i ^ 2)) : ℂ) := by
      rw [gaussian3, sumsq_mul_N23, mul_add, neg_add, Real.exp_add, Complex.ofReal_mul]
    have hchar : psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) =
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * (E.mulVec v) i : ℝ) : ℂ))) := by
      rw [← mulShift_ofReal_one psiInf, psiInf_mulShift_ofReal a psiInf hpsiInf, Fin.sum_univ_two]
      simp only [hξ, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show (a : ℝ) * ρ₀ * (E.mulVec v) 0 + (a : ℝ) * ρ₁ * (E.mulVec v) 1 =
          (a : ℝ) * (ρ₀ * (E.mulVec v) 0 + ρ₁ * (E.mulVec v) 1) by ring, hrow]
      congr 1
      push_cast
      ring
    rw [hS]
    beta_reduce
    rw [hev, mul_N23_two, mul_N23_two, hg, hchar, hCst, hf, ← hc₀, ← hc₁]
    ring
  calc godementInner3 psiInf S E 1
      = ∫ v : Fin 2 → ℝ, S (E * N23 v) * psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) := rfl
    _ = ∫ v : Fin 2 → ℝ, Cst * f (E.mulVec v) := by simp_rw [hpt]
    _ = Cst * ((|E.det|)⁻¹ * ∫ u : Fin 2 → ℝ, f u) := by
        rw [integral_const_mul, integral_comp_mulVec E he]
    _ = _ := by
        simp only [hf]
        rw [fourier_linear c₀ c₁ ξ, hCst, hc₀, hc₁]
        simp only [hξ, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, hρ₀, hρ₁, hEdef, Matrix.of_apply]
        have hexp : Real.exp (-(Real.pi * (((a : ℝ) * (Matrix.of e)⁻¹ 1 0) ^ 2 + ((a : ℝ) * (Matrix.of e)⁻¹ 1 1) ^ 2))) =
            Real.exp (-(Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) := by
          congr 1; ring
        rw [hexp]
        push_cast
        ring

#print axioms solution

end
end S_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3 (solution)
