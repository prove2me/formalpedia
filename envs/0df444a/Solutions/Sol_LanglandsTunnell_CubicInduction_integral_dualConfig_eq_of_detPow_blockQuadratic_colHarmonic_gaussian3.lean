-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_detPow_blockQuadratic_colHarmonic_gaussian3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8ce32759-dced-5f07-aba6-38508a5f82ac

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_detPow_blockQuadratic_colHarmonic_gaussian3

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.StandardKernel LanglandsTunnell.Converse

noncomputable section

namespace Ws14D3Q

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

private theorem _root_.Ws14D3Q.ofReal_mul (r s : ℝ) : ofReal (r * s) = ofReal r * ofReal s := by
  rw [← ofRealHom_apply, ← ofRealHom_apply, ← ofRealHom_apply, map_mul]

p2m_export "Ws14D3Q" "ofReal_mul"
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

open Real Complex in

noncomputable def Gc (x : ℝ) : ℂ := (Real.exp (-(Real.pi * x ^ 2)) : ℂ)

theorem Gc_def : Gc = fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := rfl

noncomputable def D (k : ℕ) (x : ℝ) : ℂ := iteratedDeriv k Gc x

theorem contDiff_Gc : ContDiff ℝ (⊤ : ℕ∞) Gc := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have : Gc = fun x : ℝ => Complex.exp (-((Real.pi : ℂ) * (x : ℂ) ^ 2)) := by
    funext x; simp [Gc, Complex.ofReal_exp]
  rw [this]
  exact Complex.contDiff_exp.comp ((contDiff_const.mul (h1.pow 2)).neg)

theorem hasDerivAt_Gc (x : ℝ) : HasDerivAt Gc (-(2 * Real.pi * x) * Gc x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2)) (-(Real.pi * (2 * x))) x := by
    have := ((hasDerivAt_pow 2 x).const_mul Real.pi).neg
    simp [pow_one] at this
    exact this
  have h2 := (Real.hasDerivAt_exp _).comp x h1
  have h3 := h2.ofReal_comp
  refine h3.congr_deriv ?_
  simp only [Gc]
  push_cast
  ring

theorem hasDerivAt_D (k : ℕ) (x : ℝ) : HasDerivAt (D k) (D (k + 1) x) x := by
  have hd : Differentiable ℝ (iteratedDeriv k Gc) :=
    contDiff_Gc.differentiable_iteratedDeriv k (by exact_mod_cast (WithTop.coe_lt_top (k : ℕ)))
  have := (hd x).hasDerivAt
  rw [D, iteratedDeriv_succ]
  exact this

theorem D_zero (x : ℝ) : D 0 x = Gc x := by simp [D]

noncomputable def ech (ξ x : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)))

theorem norm_ech (ξ x : ℝ) : ‖ech ξ x‖ = 1 := by
  rw [ech, Complex.norm_exp]
  have : (-(2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem continuous_ech (ξ : ℝ) : Continuous (ech ξ) := by
  unfold ech; fun_prop

noncomputable def term (k : ℕ) (ξ : ℝ) (x : ℝ) : ℂ := ((x : ℂ) ^ k * Gc x) * ech ξ x

theorem integrable_pow_mul_Gc (k : ℕ) : Integrable (fun x : ℝ => (x : ℂ) ^ k * Gc x) := by
  have h0 := (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := k)
    (by have := k.cast_nonneg (α := ℝ); linarith)).ofReal (𝕜 := ℂ)
  have h : Integrable (fun x : ℝ => (((x ^ (k : ℝ) * Real.exp (-Real.pi * x ^ 2) : ℝ)) : ℂ)) := h0
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Gc, Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]

theorem integrable_term (k : ℕ) (ξ : ℝ) : Integrable (term k ξ) := by
  unfold term
  exact (integrable_pow_mul_Gc k).mul_bdd (c := 1) (continuous_ech ξ).aestronglyMeasurable (ae_of_all _ fun x => (norm_ech ξ x).le)

noncomputable def cst : ℂ := (-(2 * Real.pi * Complex.I))⁻¹

theorem integral_term (k : ℕ) (ξ : ℝ) : ∫ x, term k ξ x = cst ^ k * D k ξ := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv k (-ξ)
  have hfun : (fun x : ℝ => ((x : ℝ) : ℂ) ^ k * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((-ξ : ℝ) : ℂ) * (x : ℂ))) = term k ξ := by
    funext x
    simp only [term, Gc, ech]
    congr 1
    push_cast
    ring_nf
  rw [hfun] at h
  rw [h, ← Gc_def]

  have hev : (fun x : ℝ => Gc (-x)) = Gc := by funext x; simp [Gc]
  have h2 := iteratedDeriv_comp_neg k Gc ξ
  rw [hev] at h2

  have h3 : iteratedDeriv k Gc (-ξ) = (-1 : ℂ) ^ k * iteratedDeriv k Gc ξ := by
    rw [h2, Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_mul]
  rw [h3, D, ← mul_assoc, ← mul_pow]
  congr 2
  rw [cst, show (-(2 * (Real.pi : ℂ) * Complex.I)) = -(2 * Real.pi * Complex.I) by ring, inv_neg]
  ring

theorem cst_mul : cst * (-(2 * Real.pi) : ℂ) = -Complex.I := by
  rw [cst]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

theorem deriv_D (k : ℕ) (x : ℝ) : deriv (D k) x = D (k + 1) x := (hasDerivAt_D k x).deriv

theorem hasDerivAt_ofReal' (x : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
  simpa using (hasDerivAt_id x).ofReal_comp

theorem D_one (x : ℝ) : D 1 x = -(2 * (Real.pi : ℂ) * (x : ℂ)) * Gc x := by
  rw [show D 1 x = deriv (D 0) x from (deriv_D 0 x).symm, show D 0 = Gc from funext D_zero]
  exact (hasDerivAt_Gc x).deriv

theorem D_two (x : ℝ) : D 2 x = ((2 * (Real.pi : ℂ) * (x : ℂ)) ^ 2 - 2 * (Real.pi : ℂ)) * Gc x := by
  have h := (((hasDerivAt_ofReal' x).const_mul (2 * (Real.pi : ℂ))).neg).mul (hasDerivAt_Gc x)
  have hfun : D 1 = fun y : ℝ => -(2 * (Real.pi : ℂ) * (y : ℂ)) * Gc y := funext fun y => D_one y
  have h2 : deriv (D 1) x = -(2 * (Real.pi : ℂ) * 1) * Gc x + -(2 * (Real.pi : ℂ) * (x : ℂ)) * (-(2 * Real.pi * x) * Gc x) := by
    rw [hfun]; exact h.deriv
  rw [show D 2 x = deriv (D 1) x from (deriv_D 1 x).symm, h2]
  ring

theorem D_three (x : ℝ) :
    D 3 x = (-(2 * (Real.pi : ℂ) * (x : ℂ)) ^ 3 + 3 * (2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ) * (x : ℂ))) * Gc x := by
  have hq : HasDerivAt (fun y : ℝ => (2 * (Real.pi : ℂ) * (y : ℂ)) ^ 2 - 2 * (Real.pi : ℂ))
      ((2 : ℕ) * (2 * (Real.pi : ℂ) * (x : ℂ)) ^ (2 - 1) * (2 * (Real.pi : ℂ) * 1)) x :=
    (((hasDerivAt_ofReal' x).const_mul (2 * (Real.pi : ℂ))).pow 2).sub_const _
  have h := hq.mul (hasDerivAt_Gc x)
  have hfun : D 2 = fun y : ℝ => ((2 * (Real.pi : ℂ) * (y : ℂ)) ^ 2 - 2 * (Real.pi : ℂ)) * Gc y := funext fun y => D_two y
  have h2 : deriv (D 2) x = (2 : ℕ) * (2 * (Real.pi : ℂ) * (x : ℂ)) ^ (2 - 1) * (2 * (Real.pi : ℂ) * 1) * Gc x +
      ((2 * (Real.pi : ℂ) * (x : ℂ)) ^ 2 - 2 * (Real.pi : ℂ)) * (-(2 * Real.pi * x) * Gc x) := by
    rw [hfun]; exact h.deriv
  rw [show D 3 x = deriv (D 2) x from (deriv_D 2 x).symm, h2]
  push_cast
  ring

theorem cst_eq : cst = Complex.I * (2 * (Real.pi : ℂ))⁻¹ := by
  rw [cst]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  try rw [Complex.I_sq]
  try ring

noncomputable def T (j k : ℕ) (ξ : Fin 2 → ℝ) (u : Fin 2 → ℝ) : ℂ := term j (ξ 0) (u 0) * term k (ξ 1) (u 1)

theorem T_eq_prod (j k : ℕ) (ξ : Fin 2 → ℝ) (u : Fin 2 → ℝ) :
    T j k ξ u = ∏ i : Fin 2, (![term j (ξ 0), term k (ξ 1)] : Fin 2 → ℝ → ℂ) i (u i) := by
  rw [T, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem integrable_T (j k : ℕ) (ξ : Fin 2 → ℝ) : Integrable (T j k ξ) := by
  have : T j k ξ = fun u => ∏ i : Fin 2, (![term j (ξ 0), term k (ξ 1)] : Fin 2 → ℝ → ℂ) i (u i) := funext (T_eq_prod j k ξ)
  rw [this]
  refine Integrable.fintype_prod (f := ![term j (ξ 0), term k (ξ 1)]) (μ := fun _ => volume) fun i => ?_
  fin_cases i
  · exact integrable_term j (ξ 0)
  · exact integrable_term k (ξ 1)

theorem integral_T (j k : ℕ) (ξ : Fin 2 → ℝ) :
    ∫ u : Fin 2 → ℝ, T j k ξ u = (cst ^ j * D j (ξ 0)) * (cst ^ k * D k (ξ 1)) := by
  have : T j k ξ = fun u => ∏ i : Fin 2, (![term j (ξ 0), term k (ξ 1)] : Fin 2 → ℝ → ℂ) i (u i) := funext (T_eq_prod j k ξ)
  rw [this, integral_fintype_prod_volume_eq_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_term, integral_term]

end Ws14D3Q

open Ws14D3Q LanglandsTunnell.CubicInduction in
theorem solution
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : a₂ ≠ 0) :
    (∫ v : Fin 2 → ℝ,
        S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
          psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
      = (((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ n *
          (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
          (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
          ((-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((e 1 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) - ((e 0 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)))) ^ δ *
              (((a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ))) ^ 2 - ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ))) ^ 2) -
            (δ : ℂ) * ((a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ))) * ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ))) / (Real.pi : ℂ)) *
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
  set Cst : ℂ := (((E 0 0 : ℝ) : ℂ) - Complex.I * ((E 1 0 : ℝ) : ℂ)) ^ n *
      (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (E 0 1 ^ 2 + E 1 1 ^ 2) + (E 0 0 ^ 2 + E 1 0 ^ 2)))) : ℂ) with hCst

  have hg : ∀ v : Fin 2 → ℝ, gaussian3 (E * MD a₁ a₂ v) =
      (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (E 0 1 ^ 2 + E 1 1 ^ 2) + (E 0 0 ^ 2 + E 1 0 ^ 2)))) : ℂ) *
        (Gc ((E.mulVec v) 0 / a₁) * Gc ((E.mulVec v) 1 / a₁)) := by
    intro v
    rw [gaussian3, sumsq_mul_MD, mul_add, neg_add, Real.exp_add, Complex.ofReal_mul]
    congr 1
    simp only [Fin.sum_univ_two, Gc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 1; ring
  have hchar : ∀ v : Fin 2 → ℝ, psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) =
      ech (ξ 0) ((E.mulVec v) 0 / a₁) * ech (ξ 1) ((E.mulVec v) 1 / a₁) := by
    intro v
    rw [psiInf_ofReal a psiInf hpsiInf, ech, ech, ← Complex.exp_add]
    congr 1
    simp only [hξ, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : (a : ℝ) * -(v 1) = -((a : ℝ) * a₁ * ρ₀ * ((E.mulVec v) 0 / a₁) + (a : ℝ) * a₁ * ρ₁ * ((E.mulVec v) 1 / a₁)) := by
      rw [← hrow v]; field_simp; try ring
    rw [this]
    push_cast
    ring
  have hMD : ∀ v : Fin 2 → ℝ, (!![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0] : Matrix (Fin 2) (Fin 3) ℝ) = MD a₁ a₂ v := fun v => rfl
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_three, Complex.I_mul_I]; ring
  have hI4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have hI5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, hI4, one_mul]
  have hI6 : Complex.I ^ 6 = -1 := by rw [pow_succ, hI5, Complex.I_mul_I]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ha₁' : (a₁ : ℂ) ≠ 0 := by exact_mod_cast ha₁
  have ha₂' : (a₂ : ℂ) ≠ 0 := by exact_mod_cast ha₂

  set κ : ℂ := ((a₂⁻¹ : ℝ) : ℂ) * (((E 0 1 : ℝ) : ℂ) + Complex.I * ((E 1 1 : ℝ) : ℂ)) with hκ
  set l0 : ℂ := ((a₂⁻¹ : ℝ) : ℂ) * ((E 1 1 : ℝ) : ℂ) with hl0
  set l1 : ℂ := -(((a₂⁻¹ : ℝ) : ℂ) * ((E 0 1 : ℝ) : ℂ)) with hl1
  rcases hδ with rfl | rfl
  ·
    set Q : (Fin 2 → ℝ) → ℂ := fun u => T 2 0 ξ u + (2 * Complex.I) * T 1 1 ξ u + (-1) * T 0 2 ξ u + κ ^ 2 * T 0 0 ξ u with hQ
    have hpt : ∀ v : Fin 2 → ℝ,
        S (E * MD a₁ a₂ v) * psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) = Cst * Q (fun i => (E.mulVec v) i / a₁) := by
      intro v
      rw [hS]
      beta_reduce
      rw [hg, hchar]
      simp only [mul_MD_zero, mul_MD_one, mul_MD_two, hCst, hQ, hκ, T, term, pow_zero, pow_one, one_mul]
      push_cast
      ring_nf
      simp only [Complex.I_sq, hI3, hI4]
      ring_nf
    have hQint : Integrable Q := by
      rw [hQ]
      exact (((integrable_T 2 0 ξ).add ((integrable_T 1 1 ξ).const_mul _)).add ((integrable_T 0 2 ξ).const_mul _)).add
        ((integrable_T 0 0 ξ).const_mul _)
    have hQval : ∫ u : Fin 2 → ℝ, Q u = (cst ^ 2 * D 2 (ξ 0)) * (cst ^ 0 * D 0 (ξ 1)) +
        (2 * Complex.I) * ((cst ^ 1 * D 1 (ξ 0)) * (cst ^ 1 * D 1 (ξ 1))) +
        (-1) * ((cst ^ 0 * D 0 (ξ 0)) * (cst ^ 2 * D 2 (ξ 1))) + κ ^ 2 * ((cst ^ 0 * D 0 (ξ 0)) * (cst ^ 0 * D 0 (ξ 1))) := by
      rw [hQ]
      rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_T, integral_T, integral_T, integral_T]
      · exact integrable_T 2 0 ξ
      · exact (integrable_T 1 1 ξ).const_mul _
      · exact (integrable_T 2 0 ξ).add ((integrable_T 1 1 ξ).const_mul _)
      · exact (integrable_T 0 2 ξ).const_mul _
      · exact ((integrable_T 2 0 ξ).add ((integrable_T 1 1 ξ).const_mul _)).add ((integrable_T 0 2 ξ).const_mul _)
      · exact (integrable_T 0 0 ξ).const_mul _
    calc (∫ v : Fin 2 → ℝ, S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
            psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
        = ∫ v : Fin 2 → ℝ, Cst * Q (fun i => (E.mulVec v) i / a₁) := by
            congr 1; funext v; rw [hMD]; exact hpt v
      _ = Cst * ((((a₁ ^ 2 * |E.det|⁻¹ : ℝ)) : ℂ) * ∫ u : Fin 2 → ℝ, Q u) := by
            rw [integral_const_mul, integral_comp_mulVec_div E he a₁ ha₁ Q]
      _ = _ := by
            rw [hQval]
            simp only [D_zero, D_one, D_two, cst_eq]
            rw [hCst, hκ]
            simp only [hξ, Matrix.cons_val_zero, Matrix.cons_val_one, hρ₀, hρ₁, hEdef, Matrix.of_apply, Gc, pow_zero,
              Nat.cast_zero]
            have hdet' : (((|(Matrix.of e).det| : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.mpr he)
            have hexp : Real.exp (-(Real.pi * ((a : ℝ) * a₁ * (Matrix.of e)⁻¹ 1 0) ^ 2)) * Real.exp (-(Real.pi * ((a : ℝ) * a₁ * (Matrix.of e)⁻¹ 1 1) ^ 2)) =
                Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [← hexp]
            push_cast
            field_simp
            ring_nf
            simp only [Complex.I_sq, hI3, hI4, hI5, hI6]
            ring_nf
  ·
    set Q : (Fin 2 → ℝ) → ℂ := fun u =>
      l0 * T 3 0 ξ u + (2 * Complex.I * l0 + l1) * T 2 1 ξ u + (-l0 + 2 * Complex.I * l1) * T 1 2 ξ u + (-l1) * T 0 3 ξ u +
        (l0 * κ ^ 2) * T 1 0 ξ u + (l1 * κ ^ 2) * T 0 1 ξ u with hQ
    have hpt : ∀ v : Fin 2 → ℝ,
        S (E * MD a₁ a₂ v) * psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))) = Cst * Q (fun i => (E.mulVec v) i / a₁) := by
      intro v
      rw [hS]
      beta_reduce
      rw [hg, hchar]
      simp only [mul_MD_zero, mul_MD_one, mul_MD_two, hCst, hQ, hκ, hl0, hl1, T, term, pow_zero, pow_one, one_mul]
      push_cast
      ring_nf
      simp only [Complex.I_sq, hI3, hI4]
      ring_nf
    have i30 := (integrable_T 3 0 ξ).const_mul l0
    have i21 := (integrable_T 2 1 ξ).const_mul (2 * Complex.I * l0 + l1)
    have i12 := (integrable_T 1 2 ξ).const_mul (-l0 + 2 * Complex.I * l1)
    have i03 := (integrable_T 0 3 ξ).const_mul (-l1)
    have i10 := (integrable_T 1 0 ξ).const_mul (l0 * κ ^ 2)
    have i01 := (integrable_T 0 1 ξ).const_mul (l1 * κ ^ 2)
    have hQval : ∫ u : Fin 2 → ℝ, Q u =
        l0 * ((cst ^ 3 * D 3 (ξ 0)) * (cst ^ 0 * D 0 (ξ 1))) +
        (2 * Complex.I * l0 + l1) * ((cst ^ 2 * D 2 (ξ 0)) * (cst ^ 1 * D 1 (ξ 1))) +
        (-l0 + 2 * Complex.I * l1) * ((cst ^ 1 * D 1 (ξ 0)) * (cst ^ 2 * D 2 (ξ 1))) +
        (-l1) * ((cst ^ 0 * D 0 (ξ 0)) * (cst ^ 3 * D 3 (ξ 1))) +
        (l0 * κ ^ 2) * ((cst ^ 1 * D 1 (ξ 0)) * (cst ^ 0 * D 0 (ξ 1))) +
        (l1 * κ ^ 2) * ((cst ^ 0 * D 0 (ξ 0)) * (cst ^ 1 * D 1 (ξ 1))) := by
      rw [hQ]
      rw [integral_add, integral_add, integral_add, integral_add, integral_add,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_T, integral_T, integral_T, integral_T, integral_T, integral_T]
      all_goals first | exact i30 | exact i21 | exact i12 | exact i03 | exact i10 | exact i01 | exact i30.add i21 | exact (i30.add i21).add i12 | exact ((i30.add i21).add i12).add i03 | exact (((i30.add i21).add i12).add i03).add i10
    have hQint : Integrable Q := by
      rw [hQ]; exact ((((i30.add i21).add i12).add i03).add i10).add i01
    calc (∫ v : Fin 2 → ℝ, S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
            psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
        = ∫ v : Fin 2 → ℝ, Cst * Q (fun i => (E.mulVec v) i / a₁) := by
            congr 1; funext v; rw [hMD]; exact hpt v
      _ = Cst * ((((a₁ ^ 2 * |E.det|⁻¹ : ℝ)) : ℂ) * ∫ u : Fin 2 → ℝ, Q u) := by
            rw [integral_const_mul, integral_comp_mulVec_div E he a₁ ha₁ Q]
      _ = _ := by
            rw [hQval]
            simp only [D_zero, D_one, D_two, D_three, cst_eq]
            rw [hCst, hκ, hl0, hl1]
            simp only [hξ, Matrix.cons_val_zero, Matrix.cons_val_one, hρ₀, hρ₁, hEdef, Matrix.of_apply, Gc, pow_zero, pow_one,
              Nat.cast_one]
            have hdet' : (((|(Matrix.of e).det| : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.mpr he)
            have hexp : Real.exp (-(Real.pi * ((a : ℝ) * a₁ * (Matrix.of e)⁻¹ 1 0) ^ 2)) * Real.exp (-(Real.pi * ((a : ℝ) * a₁ * (Matrix.of e)⁻¹ 1 1) ^ 2)) =
                Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [← hexp]
            push_cast
            field_simp
            ring_nf
            simp only [Complex.I_sq, hI3, hI4, hI5, hI6]
            ring_nf

end
end S_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_detPow_blockQuadratic_colHarmonic_gaussian3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_detPow_blockQuadratic_colHarmonic_gaussian3 (solution)
