-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.WhittakerBlock.archRealLift3_one_and_ideleNorm_det_archRealLift3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1ca9640f-c30e-5206-be46-ff04e40f4fcc

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_archRealLift3_one_and_ideleNorm_det_archRealLift3
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
namespace FlowLiftAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

def realAdeleHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map realAdeleHom) :=
  rfl

theorem isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  have hdet : IsUnit ((Matrix.of e).map realAdeleHom) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 he).map realAdeleHom
  rw [archRealMat3_eq]
  exact hdet.map (archMatrixInclHomN (Fin 3) ℚ)

theorem coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3 he)]
  exact (isUnit_archRealMat3 he).unit_spec

theorem of_idArr : Matrix.of (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 := by
  ext a b
  simp [Matrix.one_apply]

theorem archRealLift3_idArr :
    WhittakerBlock.archRealLift3 (fun a b => if a = b then (1 : ℝ) else 0) = 1 := by
  have hdet : (Matrix.of fun a b : Fin 3 => if a = b then (1 : ℝ) else 0).det ≠ 0 := by
    rw [of_idArr, Matrix.det_one]
    exact one_ne_zero
  apply Units.ext
  rw [coe_archRealLift3 hdet, archRealMat3_eq, of_idArr,
    Matrix.map_one _ (map_zero _) (map_one _), AutomorphicForm.archMatrixInclN_one, Units.val_one]

theorem map_adeleFin_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) :
    (WhittakerBlock.archRealMat3 e).map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
  refine Matrix.ext fun a b => ?_
  rw [archRealMat3_eq]
  exact adeleFin_archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map realAdeleHom) a b

theorem snd_val_det_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (WhittakerBlock.archRealLift3 e) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
      AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
  have h := RingHom.map_det (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (WhittakerBlock.archRealMat3 e)
  rw [RingHom.mapMatrix_apply, map_adeleFin_archRealMat3, Matrix.det_one] at h
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_archRealLift3 he]
  exact h

theorem fst_val_det_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) (w : InfinitePlace ℚ) :
    ((Matrix.GeneralLinearGroup.det (WhittakerBlock.archRealLift3 e) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
      AdeleRing (𝓞 ℚ) ℚ).1 w =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (Matrix.of e).det := by
  have h := RingHom.map_det
    ((Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) w).comp (AdelicLevel.adeleArch (𝓞 ℚ) ℚ))
    (WhittakerBlock.archRealMat3 e)
  have hM : ((Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) w).comp
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)).mapMatrix (WhittakerBlock.archRealMat3 e) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.toRingHom.mapMatrix
        (Matrix.of e) := by
    ext i j
    rfl
  rw [hM, ← RingHom.map_det] at h
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_archRealLift3 he]
  exact h

theorem norm_ringEquivRealOfIsReal_symm (w : InfinitePlace ℚ) (r : ℝ) :
    ‖(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r‖ = |r| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).isometry.dist_eq
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r) 0
  rw [dist_zero_right] at h
  rw [← h]
  show dist (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r))
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) 0) = |r|
  rw [RingEquiv.apply_symm_apply, map_zero, Real.dist_eq, sub_zero]

theorem mult_eq_one (w : InfinitePlace ℚ) : w.mult = 1 :=
  InfinitePlace.mult_isReal ⟨w, IsTotallyReal.isReal w⟩

end LanglandsTunnell.CubicInduction.FlowLiftAux

end

open LanglandsTunnell.CubicInduction.FlowLiftAux in
theorem solution :
    WhittakerBlock.archRealLift3 (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 ∧
    ∀ e : Fin 3 → Fin 3 → ℝ, 0 < (Matrix.of e).det →
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (WhittakerBlock.archRealLift3 e)) =
        (Matrix.of e).det := by
  refine ⟨archRealLift3_idArr, fun e he => ?_⟩
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one ℚ _
    (snd_val_det_archRealLift3 he.ne'), Fintype.prod_unique, mult_eq_one, pow_one,
    fst_val_det_archRealLift3 he.ne', norm_ringEquivRealOfIsReal_symm, abs_of_pos he]

end S_LanglandsTunnell_CubicInduction_WhittakerBlock_archRealLift3_one_and_ideleNorm_det_archRealLift3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_archRealLift3_one_and_ideleNorm_det_archRealLift3 (solution)
