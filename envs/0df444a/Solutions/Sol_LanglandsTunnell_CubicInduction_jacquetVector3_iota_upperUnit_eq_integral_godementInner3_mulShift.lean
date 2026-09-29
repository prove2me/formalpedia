-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/73c33c8f-0e50-512c-b79f-439a4c52f5be

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace PWUNFOLD

open AutomorphicForm.StandardKernel MeasureTheory LanglandsTunnell.Converse.ArchR

section CoV
open MeasureTheory

theorem integral_comp_linearEquiv_eq_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E ≃ₗ[ℝ] E) (f : E → ℂ) :
    ∫ x, f (L x) ∂μ = ((|(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| : ℝ) : ℂ) * ∫ x, f x ∂μ := by
  have hdet : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' L).ne_zero
  let e : E ≃ᵐ E := L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have h1 : ∫ x, f (L x) ∂μ = ∫ y, f y ∂(Measure.map e μ) := (integral_map_equiv e f).symm
  have h2 : (e : E → E) = (L : E →ₗ[ℝ] E) := rfl
  rw [h1, h2, Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), Complex.real_smul]

theorem integral_comp_diag_mul (c : Fin 2 → ℝ) (hc : ∀ i, c i ≠ 0) (f : (Fin 2 → ℝ) → ℂ) :
    ∫ v : Fin 2 → ℝ, f (fun i => c i * v i) = (((|∏ i, c i|)⁻¹ : ℝ) : ℂ) * ∫ v : Fin 2 → ℝ, f v := by
  have hd : (Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hc i
  let L : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    (Matrix.diagonal c).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hd))
  have hL : ∀ v, L v = fun i => c i * v i := fun v => by
    funext i
    show (Matrix.toLin' (Matrix.diagonal c)) v i = c i * v i
    rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hdetL : LinearMap.det (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = ∏ i, c i := by
    rw [Matrix.toLinearEquiv'_apply, LinearMap.det_toLin', Matrix.det_diagonal]
  have := integral_comp_linearEquiv_eq_mul volume L f
  simp only [hL] at this
  rw [this, hdetL, abs_inv]

theorem integral_comp_mul_right (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (f : (Fin 2 → Fin 2 → ℝ) → ℂ) :
    ∫ e : Fin 2 → Fin 2 → ℝ, f (fun i j => (Matrix.of e * Q) i j) =
      (((|Q.det| ^ 2)⁻¹ : ℝ) : ℂ) * ∫ e : Fin 2 → Fin 2 → ℝ, f e := by
  haveI : (volume : Measure (Fin 2 → Fin 2 → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hT : Q.transpose.det ≠ 0 := by rwa [Matrix.det_transpose]
  let L₀ : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    Q.transpose.toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hT))
  let L : (Fin 2 → Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → Fin 2 → ℝ) := LinearEquiv.piCongrRight fun _ : Fin 2 => L₀
  have hL : ∀ e, L e = fun i j => (Matrix.of e * Q) i j := fun e => by
    funext i j
    show (Matrix.toLin' Q.transpose) (e i) j = (Matrix.of e * Q) i j
    rw [Matrix.toLin'_apply, Matrix.mulVec_transpose, Matrix.mul_apply]
    rfl
  have hpi : (L : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ)) =
      LinearMap.pi fun i => (L₀ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)).comp (LinearMap.proj i) := rfl
  have hL₀ : LinearMap.det (L₀ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = Q.det := by
    rw [Matrix.toLinearEquiv'_apply, LinearMap.det_toLin', Matrix.det_transpose]
  have hdetL : LinearMap.det (L : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ)) = Q.det ^ 2 := by
    rw [hpi, LinearMap.det_pi, Fin.prod_const, hL₀]
  have := integral_comp_linearEquiv_eq_mul volume L f
  simp only [hL] at this
  rw [this, hdetL, abs_inv, abs_pow]

end CoV

theorem realCoord_archRealGLAt_entry (q : GL (Fin 2) ℝ) (i j : Fin 2) :
    realCoord ((((archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q : AdelicGL2 (𝓞 ℚ) ℚ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1) = (q : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  rw [realCoord_apply]
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
      ((((adelicArchGLIncl ℚ (archGLIncl ℚ default (glEquivOfRingEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm q)) :
          AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 default) = _
  rw [← glArch_apply, glArch_adelicArchGLIncl, ← archComponent_apply (K := ℚ) default,
    archComponent_archGLIncl_self, glEquivOfRingEquiv_apply_entry,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  exact RingEquiv.apply_symm_apply _ _

theorem realMat_iota_archRealGLAt (q : GL (Fin 2) ℝ) :
    realMat (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q))) =
      embedMat2 (q : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  rw [realMat_eq, Matrix.map_apply]
  show realCoord ((embedMat2 ((archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q : AdelicGL2 (𝓞 ℚ) ℚ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1) = _
  fin_cases i <;> fin_cases j <;> simp [embedMat2, realCoord_archRealGLAt_entry] <;>
    first | exact map_zero realCoord | exact map_one realCoord

theorem ofReal_mul' (r s : ℝ) : ofReal (r * s) = ofReal r * ofReal s := by
  funext v
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm (r * s) =
    ofReal r v * ofReal s v
  rw [map_mul]
  rfl

theorem ofReal_neg' (r : ℝ) : ofReal (-r) = -ofReal r := by
  funext v
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm (-r) = -ofReal r v
  rw [map_neg]
  rfl

theorem quasiChar_mul (u : ℂ) (a : ZMod 2) {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    quasiChar u a (x * y) = quasiChar u a x * quasiChar u a y := by
  unfold quasiChar
  rw [abs_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg x) (abs_nonneg y)]
  split_ifs with ha
  · ring
  · rw [sign_mul]
    push_cast
    ring

theorem quasiChar_one (u : ℂ) (a : ZMod 2) : quasiChar u a 1 = 1 := by
  unfold quasiChar
  simp

theorem quasiChar_ne_zero (u : ℂ) (a : ZMod 2) {x : ℝ} (hx : x ≠ 0) : quasiChar u a x ≠ 0 := by
  unfold quasiChar
  refine mul_ne_zero ?_ ?_
  · intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact (abs_pos.mpr hx).ne' (by exact_mod_cast h.1)
  · split_ifs with ha
    · exact one_ne_zero
    · rcases lt_or_gt_of_ne hx with h | h
      · rw [sign_neg h]; norm_num
      · rw [sign_pos h]; norm_num

theorem quasiChar_add_one_mul_abs (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : y ≠ 0) :
    quasiChar (u + 1) a y * ((|y| : ℝ) : ℂ) = quasiChar (u + 2) a y := by
  unfold quasiChar
  have h0 : ((|y| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hy).ne'
  conv_rhs => rw [show u + 2 = (u + 1) + 1 by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]
  ring

theorem scalar_cancel (u : ℂ) (a : ZMod 2) (x d : ℝ) (hd : d ≠ 0) :
    quasiChar (u + 1) a d * (((|d| : ℝ) : ℂ) * ((((|d| ^ 2)⁻¹ : ℝ) : ℂ) *
      (quasiChar (u + 2) a (x * d⁻¹) * ((((|x * d⁻¹| ^ 2)⁻¹ : ℝ)) : ℂ)))) =
    quasiChar (u + 2) a x * (((|x| ^ 2)⁻¹ : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hq : quasiChar (u + 2) a d ≠ 0 := quasiChar_ne_zero _ _ hd
    have hinv : quasiChar (u + 2) a d⁻¹ = (quasiChar (u + 2) a d)⁻¹ := by
      have h := quasiChar_mul (u + 2) a (x := d) (y := d⁻¹) hd (inv_ne_zero hd)
      rw [mul_inv_cancel₀ hd, quasiChar_one] at h
      exact (eq_inv_of_mul_eq_one_right h.symm)
    rw [quasiChar_mul (u + 2) a hx (inv_ne_zero hd), hinv, ← quasiChar_add_one_mul_abs u a hd]
    have h1 : quasiChar (u + 1) a d ≠ 0 := quasiChar_ne_zero _ _ hd
    have h2 : ((|d| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hd).ne'
    have h3 : ((|x| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hx).ne'
    rw [abs_mul, abs_inv]
    push_cast
    field_simp

theorem embedMat2_diag_det (a₁ a₂ : ℝ) :
    (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)).det = a₁ * a₂ := by
  simp [embedMat2, Matrix.det_fin_three]

theorem inner_matrix (a₁ a₂ : ℝ) (w : Fin 2 → ℝ) :
    (Matrix.of ![fun b => (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) 0 b +
                  (![a₁, a₂] 0 * w 0) * (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) 2 b,
                fun b => (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) 1 b +
                  (![a₁, a₂] 1 * w 1) * (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) 2 b] :
        Matrix (Fin 2) (Fin 3) ℝ) =
      (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ) *
        Matrix.of ![fun b => (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 b + w 0 * (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 b,
                    fun b => (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 b + w 1 * (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 b] := by
  ext i b
  fin_cases i <;> fin_cases b <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem inner_eq (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (E : Matrix (Fin 2) (Fin 2) ℝ) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    godementInner3 ψ S E (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) =
      ((|a₁ * a₂| : ℝ) : ℂ) *
        godementInner3 (ψ.mulShift (ofReal a₂)) S (E * !![a₁, 0; 0, a₂]) 1 := by
  unfold godementInner3
  set g : (Fin 2 → ℝ) → ℂ := fun v =>
    S (E * Matrix.of ![fun b => (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) 0 b +
          v 0 * (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) 2 b,
        fun b => (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) 1 b +
          v 1 * (embedMat2 (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ)) 2 b]) *
      ψ (ofReal (-(v 1))) with hg
  have hc : ∀ i : Fin 2, (![a₁, a₂] : Fin 2 → ℝ) i ≠ 0 := by
    intro i; fin_cases i <;> simpa
  have key := integral_comp_diag_mul ![a₁, a₂] hc g
  have hprod : (∏ i : Fin 2, (![a₁, a₂] : Fin 2 → ℝ) i) = a₁ * a₂ := by
    rw [Fin.prod_univ_two]; rfl
  rw [hprod] at key
  have hne : ((|a₁ * a₂| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr (mul_ne_zero ha₁ ha₂)).ne'
  have h1 : (∫ v : Fin 2 → ℝ, g v) = ((|a₁ * a₂| : ℝ) : ℂ) * ∫ w : Fin 2 → ℝ, g (fun i => (![a₁, a₂] : Fin 2 → ℝ) i * w i) := by
    rw [key, ← mul_assoc]
    push_cast
    rw [mul_inv_cancel₀ hne, one_mul]
  show (∫ v : Fin 2 → ℝ, g v) = _
  rw [h1]
  congr 1
  congr 1
  funext w
  simp only [hg]
  rw [inner_matrix a₁ a₂ w, ← Matrix.mul_assoc, AddChar.mulShift_apply, ← ofReal_mul']
  congr 2
  simp

end PWUNFOLD

open PWUNFOLD AutomorphicForm.StandardKernel MeasureTheory LanglandsTunnell.Converse.ArchR in
theorem solution
    {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    jacquetVector3 D u₃ a₃ a ψ S
        (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ
          (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
            (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂)))) =
      ∫ e : Fin 2 → Fin 2 → ℝ,
        godementInner3 (ψ.mulShift (AutomorphicForm.StandardKernel.ofReal a₂)) S (Matrix.of e) 1 *
          ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            D.W (ArchR.diagOne a * !![a₁, 0; 0, a₂] * (Matrix.of e)⁻¹) := by
  have hqmat : ((AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, 0; 0, a₂] := rfl
  rw [jacquetVector3_eq]
  simp only [jacquetIntegrand3, realMat_iota_archRealGLAt, hqmat, embedMat2_diag_det, inner_eq ψ S _ a₁ a₂ ha₁ ha₂]
  set Qm : Matrix (Fin 2) (Fin 2) ℝ := !![a₁, 0; 0, a₂] with hQm
  have hQdet : Qm.det = a₁ * a₂ := by simp [hQm, Matrix.det_fin_two_of]
  have hQ : Qm.det ≠ 0 := by rw [hQdet]; exact mul_ne_zero ha₁ ha₂
  have hQu : IsUnit Qm.det := isUnit_iff_ne_zero.mpr hQ
  set f : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e =>
    ((|a₁ * a₂| : ℝ) : ℂ) * godementInner3 (ψ.mulShift (ofReal a₂)) S (Matrix.of e) 1 *
      quasiChar (u₃ + 2) a₃ (Matrix.of e * Qm⁻¹).det * ((((|(Matrix.of e * Qm⁻¹).det| ^ 2)⁻¹ : ℝ)) : ℂ) *
        D.W (diagOne a * (Matrix.of e * Qm⁻¹)⁻¹) with hf
  have hcomp : (fun e : Fin 2 → Fin 2 → ℝ =>
      ((|a₁ * a₂| : ℝ) : ℂ) * godementInner3 (ψ.mulShift (ofReal a₂)) S (Matrix.of e * Qm) 1 *
        quasiChar (u₃ + 2) a₃ (Matrix.of e).det * ((((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ)) : ℂ) *
          D.W (diagOne a * (Matrix.of e)⁻¹)) = fun e => f (fun i j => (Matrix.of e * Qm) i j) := by
    funext e
    simp only [hf]
    have h : Matrix.of (fun i j => (Matrix.of e * Qm) i j) = Matrix.of e * Qm := rfl
    rw [h, Matrix.mul_nonsing_inv_cancel_right _ _ hQu]
  rw [hcomp, integral_comp_mul_right Qm hQ f, ← mul_assoc, ← integral_const_mul]
  congr 1
  funext e
  simp only [hf]
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ hQu, ← Matrix.mul_assoc, hQdet]
  have key := scalar_cancel u₃ a₃ (Matrix.of e).det (a₁ * a₂) (mul_ne_zero ha₁ ha₂)
  linear_combination (godementInner3 (ψ.mulShift (ofReal a₂)) S (Matrix.of e) 1 *
    D.W (diagOne a * Qm * (Matrix.of e)⁻¹)) * key

end S_LanglandsTunnell_CubicInduction_jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift (solution)
