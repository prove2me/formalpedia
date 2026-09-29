-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isArchSmooth3_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7d852263-7471-56b0-bc76-c82d374e1dde

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace R1ArchSmoothMulRight

open AutomorphicForm AutomorphicForm.StandardKernel LanglandsTunnell.CubicInduction WhittakerBlock

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : InfinitePlace ℚ =>
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm : ℝ ≃+* v.Completion).toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

theorem ofReal_realCoord' (x : InfiniteAdeleRing ℚ) : ofRealHom (realCoord x) = x := by
  rw [ofRealHom_apply, ofReal_realCoord]

theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    archRealMat3 e = archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map ofRealHom) := rfl

theorem isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (archRealMat3 e) := by
  have h1 : IsUnit ((Matrix.of e).map ofRealHom) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr he).map _
  rw [archRealMat3_eq]
  exact h1.map (archMatrixInclHomN (Fin 3) ℚ)

theorem coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ((archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = archRealMat3 e := by
  unfold archRealLift3
  rw [dif_pos (isUnit_archRealMat3 he)]
  exact (isUnit_archRealMat3 he).unit_spec

def finPart (k : AdelicGL 3 (𝓞 ℚ) ℚ) : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) k

def realPart (k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) ℝ :=
  realMat (archComponentN (Fin 3) (𝓞 ℚ) ℚ k)

theorem det_realPart_ne_zero (k : AdelicGL 3 (𝓞 ℚ) ℚ) : (realPart k).det ≠ 0 := by
  have h : IsUnit (realPart k) := (realGL (archComponentN (Fin 3) (𝓞 ℚ) ℚ k)).isUnit
  rw [Matrix.isUnit_iff_isUnit_det] at h
  exact h.ne_zero

theorem coe_archComponentN_eq (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponentN (Fin 3) (𝓞 ℚ) ℚ k : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = (realPart k).map ofRealHom := by
  ext i j
  rw [realPart, realMat_eq, Matrix.map_apply, Matrix.map_apply, ofReal_realCoord']

theorem coe_eq_arch_mul_fin (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      archMatrixInclN (Fin 3) ℚ
          ((archComponentN (Fin 3) (𝓞 ℚ) ℚ k : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
            Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) *
        finMatrixInclN (Fin 3) ℚ
          ((finPart k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
            Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  refine Prod.ext ?_ ?_
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ _ * finMatrixInclN (Fin 3) ℚ _) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleArch_archMatrixInclN, adeleArch_finMatrixInclN]
    rw [← Matrix.mul_apply, Matrix.mul_one]
    rfl
  · change AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ _ * finMatrixInclN (Fin 3) ℚ _) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleFin_archMatrixInclN, adeleFin_finMatrixInclN]
    rw [← Matrix.mul_apply, Matrix.one_mul]
    rfl

def subst (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => (Matrix.of e * realPart k) i j

theorem of_subst (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (subst k e) = Matrix.of e * realPart k := rfl

theorem contDiff_subst (k : AdelicGL 3 (𝓞 ℚ) ℚ) : ContDiff ℝ (⊤ : ℕ∞) (subst k) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [subst, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun l _ => (contDiff_apply_apply (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (E := ℝ) i l).mul contDiff_const

theorem mapsTo_subst (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Set.MapsTo (subst k) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  intro e he
  simp only [Set.mem_setOf_eq] at he ⊢
  rw [of_subst, Matrix.det_mul]
  exact mul_ne_zero he (det_realPart_ne_zero k)

theorem archRealLift3_mul (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archRealLift3 e * k = finInclN (Fin 3) ℚ (finPart k) * archRealLift3 (subst k e) := by
  have he' : (Matrix.of (subst k e)).det ≠ 0 := mapsTo_subst k he
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_archRealLift3 he, coe_archRealLift3 he', coe_eq_arch_mul_fin k,
    coe_archComponentN_eq, archRealMat3_eq, archRealMat3_eq, ← mul_assoc, ← archMatrixInclN_mul,
    ← Matrix.map_mul, ← of_subst, archMatrixInclN_mul_finMatrixInclN]
  rfl

end R1ArchSmoothMulRight

end

open LanglandsTunnell.CubicInduction in
open R1ArchSmoothMulRight AutomorphicForm WhittakerBlock in
theorem solution (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : WhittakerBlock.IsArchSmooth3 u) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.IsArchSmooth3 (fun g => u (g * k)) := by
  intro g
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      ((fun e : Fin 3 → Fin 3 → ℝ => u (g * finInclN (Fin 3) ℚ (finPart k) * archRealLift3 e)) ∘ subst k)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    (hu (g * finInclN (Fin 3) ℚ (finPart k))).comp (contDiff_subst k).contDiffOn (mapsTo_subst k)
  refine hcomp.congr fun e he => ?_
  simp only [Function.comp_apply]
  rw [mul_assoc g (archRealLift3 e) k, archRealLift3_mul k he, mul_assoc]

end S_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right (solution)
