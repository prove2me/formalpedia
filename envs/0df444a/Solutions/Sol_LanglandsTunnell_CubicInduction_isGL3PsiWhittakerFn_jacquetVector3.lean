-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_jacquetVector3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8a54f75e-353d-54ec-b1d9-ae61c257b7b4

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3

set_option autoImplicit false

open NumberField LanglandsTunnell.Converse

noncomputable section

open MeasureTheory LanglandsTunnell.Converse.ArchR AutomorphicForm.StandardKernel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn upperUnipotent3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private def rowShearMat (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; x, 1]

private theorem det_rowShear (x : ℝ) : LinearMap.det (Matrix.toLin' (rowShearMat x)) = 1 := by
  rw [LinearMap.det_toLin']
  simp [rowShearMat, Matrix.det_fin_two_of]

private theorem rowShear_measurePreserving (x : ℝ) :
    MeasurePreserving (Matrix.toLin' (rowShearMat x)) (volume : Measure (Fin 2 → ℝ)) volume := by
  refine ⟨(Matrix.toLin' (rowShearMat x)).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (by rw [det_rowShear]; exact one_ne_zero),
    det_rowShear]
  simp

private theorem arrayShear_measurePreserving (x : ℝ) :
    MeasurePreserving (fun e : Fin 2 → Fin 2 → ℝ => fun i => Matrix.toLin' (rowShearMat x) (e i))
      (volume : Measure (Fin 2 → Fin 2 → ℝ)) volume :=
  volume_preserving_pi (fun _ : Fin 2 => rowShear_measurePreserving x)

private theorem rowShear_apply (x : ℝ) (r : Fin 2 → ℝ) :
    Matrix.toLin' (rowShearMat x) r = ![r 0, x * r 0 + r 1] := by
  funext j
  fin_cases j <;> simp [rowShearMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def arrayShearEquiv (x : ℝ) : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (Fin 2 → Fin 2 → ℝ) where
  toFun e i := Matrix.toLin' (rowShearMat x) (e i)
  invFun e i := Matrix.toLin' (rowShearMat (-x)) (e i)
  left_inv e := by
    funext i j
    simp only [rowShear_apply]
    fin_cases j <;> simp
  right_inv e := by
    funext i j
    simp only [rowShear_apply]
    fin_cases j <;> simp
  measurable_toFun := (arrayShear_measurePreserving x).measurable
  measurable_invFun := (arrayShear_measurePreserving (-x)).measurable

private theorem integral_arrayShear (x : ℝ) (F : (Fin 2 → Fin 2 → ℝ) → ℂ) :
    ∫ e : Fin 2 → Fin 2 → ℝ, F (fun i => Matrix.toLin' (rowShearMat x) (e i)) = ∫ e, F e :=
  (show MeasurePreserving (arrayShearEquiv x) volume volume from arrayShear_measurePreserving x).integral_comp' F

private theorem of_arrayShear (x : ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    Matrix.of (fun i => Matrix.toLin' (rowShearMat x) (e i)) = Matrix.of e * unip x := by
  ext i j
  rw [Matrix.of_apply, rowShear_apply]
  fin_cases j <;> simp [Matrix.mul_apply, unip, Fin.sum_univ_two]
  ring

private theorem realMat_upperUnipotent3 (x y z : InfiniteAdeleRing ℚ) :
    realMat (upperUnipotent3 x y z) = !![1, realCoord x, realCoord z; 0, 1, realCoord y; 0, 0, 1] := by
  rw [realMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]

private theorem det_realMat_upperUnipotent3 (x y z : InfiniteAdeleRing ℚ) :
    (realMat (upperUnipotent3 x y z)).det = 1 := by
  rw [realMat_upperUnipotent3, Matrix.det_fin_three]
  simp

private theorem psiArch_eq_psi_realCoord (w : InfiniteAdeleRing ℚ) :
    StandardAddChar.psiArch w = psi (realCoord w) := by
  have h1 : StandardAddChar.psiArch w =
      StandardAddChar.psiArchPlace Rat.infinitePlace (w Rat.infinitePlace) := by
    rw [StandardAddChar.psiArch_apply]
    exact finprod_eq_single _ Rat.infinitePlace fun v hv => absurd (Subsingleton.elim v Rat.infinitePlace) hv
  rw [h1, StandardAddChar.psiArchPlace_apply, psi, realCoord_apply]

private theorem ofReal_add (r s : ℝ) : ofReal (r + s) = ofReal r + ofReal s := by
  funext v
  exact map_add (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm r s

private theorem ofReal_neg (r : ℝ) : ofReal (-r) = -ofReal r := by
  funext v
  exact map_neg (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm r

private theorem psi_add (r s : ℝ) : psi (r + s) = psi r * psi s := by
  simp only [psi, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem psi_neg_mul_psi (r : ℝ) : psi (-r) * psi r = 1 := by
  rw [← psi_add, neg_add_cancel, psi]
  simp

private theorem det_unip (r : ℝ) : (unip r).det = 1 := by
  simp [unip, Matrix.det_fin_two_of]

private theorem unip_mul_unip (r s : ℝ) : unip r * unip s = unip (r + s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unip, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem inv_unip (r : ℝ) : (unip r)⁻¹ = unip (-r) := by
  rw [Matrix.inv_eq_left_inv]
  rw [unip_mul_unip, neg_add_cancel]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unip]

private theorem diagOne_mul_unip (a r : ℝ) : diagOne a * unip r = unip (a * r) * diagOne a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagOne, unip, Matrix.mul_apply, Fin.sum_univ_two]

private theorem planeShear_measurePreserving (r : ℝ) :
    MeasurePreserving (Matrix.toLin' (unip r)) (volume : Measure (Fin 2 → ℝ)) volume := by
  have hdet : LinearMap.det (Matrix.toLin' (unip r)) = 1 := by rw [LinearMap.det_toLin', det_unip]
  refine ⟨(Matrix.toLin' (unip r)).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (by rw [hdet]; exact one_ne_zero), hdet]
  simp

private theorem planeShear_apply (r : ℝ) (v : Fin 2 → ℝ) : Matrix.toLin' (unip r) v = ![v 0 + r * v 1, v 1] := by
  funext j
  fin_cases j <;> simp [unip, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def planeShearEquiv (r : ℝ) : (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) where
  toFun := Matrix.toLin' (unip r)
  invFun := Matrix.toLin' (unip (-r))
  left_inv v := by
    simp only [planeShear_apply]
    funext j
    fin_cases j <;> simp
  right_inv v := by
    simp only [planeShear_apply]
    funext j
    fin_cases j <;> simp
  measurable_toFun := (planeShear_measurePreserving r).measurable
  measurable_invFun := (planeShear_measurePreserving (-r)).measurable

private theorem integral_plane_affine (r : ℝ) (c : Fin 2 → ℝ) (F : (Fin 2 → ℝ) → ℂ) :
    ∫ v : Fin 2 → ℝ, F (Matrix.toLin' (unip r) v + c) = ∫ v, F v := by
  have h1 : ∫ v : Fin 2 → ℝ, F (Matrix.toLin' (unip r) v + c) = ∫ w : Fin 2 → ℝ, F (w + c) :=
    (show MeasurePreserving (planeShearEquiv r) volume volume from planeShear_measurePreserving r).integral_comp'
      (fun w => F (w + c))
  rw [h1]
  exact integral_add_right_eq_self F c

private theorem unip_mul_of_two_rows (r : ℝ) (r₀ r₁ : Fin 3 → ℝ) :
    unip r * Matrix.of ![r₀, r₁] = Matrix.of ![fun b => r₀ b + r * r₁ b, r₁] := by
  ext i b
  fin_cases i <;> simp [unip, Matrix.mul_apply, Fin.sum_univ_two]

private theorem godementInner3_unipotent_mul (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (h : Matrix (Fin 2) (Fin 2) ℝ) (rx ry rz : ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 ψ S h (!![1, rx, rz; 0, 1, ry; 0, 0, 1] * m) =
      ψ (ofReal ry) * godementInner3 ψ S (h * unip rx) m := by
  unfold godementInner3
  rw [← integral_const_mul]
  conv_rhs => rw [← integral_plane_affine (-rx) ![rz - rx * ry, ry]]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [planeShear_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hψ : ψ (ofReal ry) * ψ (ofReal (-(v 1 + ry))) = ψ (ofReal (-(v 1))) := by
    rw [← AddChar.map_add_eq_mul, ofReal_neg, ofReal_add, ofReal_neg]
    congr 1
    abel
  rw [mul_left_comm, hψ, Matrix.mul_assoc, unip_mul_of_two_rows]
  refine congrArg (· * ψ (ofReal (-(v 1)))) (congrArg S (congrArg (h * ·) ?_))
  ext i b
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem jacquetIntegrand3_upperUnipotent3_mul {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ w : InfiniteAdeleRing ℚ,
      psiInf w = StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * w))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (x y z : InfiniteAdeleRing ℚ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (e : Fin 2 → Fin 2 → ℝ) :
    jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S (upperUnipotent3 x y z * g) e =
      psiInf (x + y) *
        jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S g (fun i => Matrix.toLin' (rowShearMat (realCoord x)) (e i)) := by
  have hx : psiInf x = psi ((a : ℝ) * realCoord x) := by
    have hcast : realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) a) = (a : ℝ) := by
      rw [← RingHom.comp_apply]
      exact eq_ratCast (realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a
    rw [hpsiInf x, psiArch_eq_psi_realCoord, map_mul, hcast]
  have hy : psiInf (ofReal (realCoord y)) = psiInf y := by rw [ofReal_realCoord]
  unfold jacquetIntegrand3
  rw [of_arrayShear, realMat_mul, realMat_upperUnipotent3, godementInner3_unipotent_mul, hy, Matrix.det_mul, det_unip,
    mul_one, Matrix.mul_inv_rev, inv_unip, ← Matrix.mul_assoc (diagOne (a : ℝ)), diagOne_mul_unip, Matrix.mul_assoc,
    D.unip_law, AddChar.map_add_eq_mul, hx, mul_neg]
  have h1 : psi ((a : ℝ) * realCoord x) * psi (-((a : ℝ) * realCoord x)) = 1 := by
    rw [mul_comm]; exact psi_neg_mul_psi _
  linear_combination (-(godementInner3 psiInf S (Matrix.of e * unip (realCoord x)) (realMat g) *
      quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      D.W (diagOne (a : ℝ) * (Matrix.of e)⁻¹) * psiInf y)) * h1

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem solution
    (P : RealArchParam) (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    :
      IsGL3PsiWhittakerFn psiInf (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) := by

  intro x y z g
  rw [jacquetVector3_eq, jacquetVector3_eq, realMat_mul, Matrix.det_mul, det_realMat_upperUnipotent3, one_mul]
  have hint : ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S (upperUnipotent3 x y z * g) e =
      psiInf (x + y) * ∫ e, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S g e := by
    rw [← integral_arrayShear (realCoord x) (jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S g), ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun e =>
      jacquetIntegrand3_upperUnipotent3_mul D u₃ a₃ a psiInf hpsiInf S x y z g e)
  rw [hint]
  ring

end

end S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3 (solution)
