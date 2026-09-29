-- Prove2me | solution 1 for NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b81244c8-8c60-5e76-b289-f1e3777f32f4

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

noncomputable section

namespace Elem17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

theorem map_diagOne {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagOne a) = diagOne (Units.map f.toMonoidHom a) := by
  ext i j
  change f ((diagOne a : Matrix (Fin 2) (Fin 2) A) i j) =
    (diagOne (Units.map f.toMonoidHom a) : Matrix (Fin 2) (Fin 2) B) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem map_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom a) := by
  ext i j
  change f ((Matrix.scalar (Fin 2) (a : A)) i j) = (Matrix.scalar (Fin 2) ((Units.map f.toMonoidHom a : Bˣ) : B)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem scalar_coe_apply {A : Type*} [CommRing A] (a : Aˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      if i = j then (a : A) else 0 := by
  change (Matrix.scalar (Fin 2) (a : A)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

omit [NumberField F] in
theorem glArch_ext {x y : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w x = archComponent F w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => funext fun w => ?_
  exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

theorem archComponent_glArch_diagOne (w : InfinitePlace F) (a : (AdeleRing (𝓞 F) F)ˣ) :
    archComponent F w (glArch (𝓞 F) F (diagOne a)) =
      diagOne (Units.map (archEval F w).toMonoidHom (Units.map (adeleArch (𝓞 F) F).toMonoidHom a)) := by
  change Matrix.GeneralLinearGroup.map (archEval F w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F) (diagOne a)) = _
  rw [map_diagOne, map_diagOne]

theorem glFin_diagOne_of_snd_eq_one (a : (AdeleRing (𝓞 F) F)ˣ) (ha : ((a : AdeleRing (𝓞 F) F)).2 = 1) :
    glFin (𝓞 F) F (diagOne a) = 1 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 F) F) (diagOne a) = 1
  rw [map_diagOne]
  have : Units.map (adeleFin (𝓞 F) F).toMonoidHom a = 1 := Units.ext ha
  rw [this, map_one]

theorem archComponent_glArch_centralScalar (w : InfinitePlace F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (archEval F w).toMonoidHom (Units.map (adeleArch (𝓞 F) F).toMonoidHom z)) := by
  change Matrix.GeneralLinearGroup.map (archEval F w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F) (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) = _
  rw [map_scalar, map_scalar]

theorem glFin_centralScalar_of_snd_eq_one (z : (AdeleRing (𝓞 F) F)ˣ) (hz : ((z : AdeleRing (𝓞 F) F)).2 = 1) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F z) = 1 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 F) F) (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1
  rw [map_scalar]
  have : Units.map (adeleFin (𝓞 F) F).toMonoidHom z = 1 := Units.ext hz
  rw [this, map_one]

theorem glArch_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glArch (𝓞 F) F (archRealGLAt hw m) = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl F _

theorem archComponent_glArch_archRealGLAt_self {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

theorem archComponent_glArch_archRealGLAt_of_ne {w w' : InfinitePlace F} (hw : w.IsReal) (hw' : w' ≠ w)
    (m : GL (Fin 2) ℝ) : archComponent F w' (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_of_ne F hw']

theorem glFin_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 F) F (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl F _

end Elem17

namespace Elem17

variable {F : Type} [Field F] [NumberField F]

theorem map_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  ext i j
  change f ((unipotentGL2 x : Matrix (Fin 2) (Fin 2) A) i j) = (unipotentGL2 (f x) : Matrix (Fin 2) (Fin 2) B) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem archComponent_glArch_unipotentGL2 (w : InfinitePlace F) (X : AdeleRing (𝓞 F) F) :
    archComponent F w (glArch (𝓞 F) F (unipotentGL2 X)) = unipotentGL2 (X.1 w) := by
  change Matrix.GeneralLinearGroup.map (archEval F w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F) (unipotentGL2 X)) = _
  rw [map_unipotentGL2, map_unipotentGL2]
  rfl

theorem glFin_unipotentGL2 (X : AdeleRing (𝓞 F) F) :
    glFin (𝓞 F) F (unipotentGL2 X) = unipotentGL2 X.2 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 F) F) (unipotentGL2 X) = _
  rw [map_unipotentGL2]
  rfl

theorem glEquivOfRingEquiv_unipotentGL2 {A B : Type*} [NormedField A] [NormedField B] (e : A ≃+* B) (x : A) :
    glEquivOfRingEquiv e (unipotentGL2 x) = unipotentGL2 (e x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

open scoped Classical in
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.StandardAddChar in

theorem stdAddChar_single_half (w : InfinitePlace F) (hw : w.IsReal) :
    stdAddChar F (show (AdeleRing (𝓞 F) F) from
      (Pi.single w ((ringEquivRealOfIsReal hw).symm (1 / 2)), 0)) = -1 := by
  classical
  show (adelicTraceData F).psiK _ = -1
  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  have hfin : (adelicTraceData F).traceFin
      ((show (AdeleRing (𝓞 F) F) from (Pi.single w ((ringEquivRealOfIsReal hw).symm (1 / 2)), 0))).2 = 0 := by
    show (adelicTraceData F).traceFin 0 = 0
    exact map_zero _
  have hinf : (adelicTraceData F).traceInf
      ((show (AdeleRing (𝓞 F) F) from (Pi.single w ((ringEquivRealOfIsReal hw).symm (1 / 2)), 0))).1 =
        algebraMap ℚ (InfiniteAdeleRing ℚ) (1 / 2 : ℚ) := by
    show traceInfHom F (Pi.single w ((ringEquivRealOfIsReal hw).symm (1 / 2))) = _
    rw [traceInfHom_apply]
    have hsum : infTraceSum F (Pi.single w ((ringEquivRealOfIsReal hw).symm (1 / 2))) = ((1 / 2 : ℚ) : ℝ) := by
      unfold infTraceSum
      rw [Finset.sum_eq_single w]
      · rw [Pi.single_eq_same, mult_isReal ⟨w, hw⟩]
        have hre : (extensionEmbedding w ((ringEquivRealOfIsReal hw).symm (1 / 2))).re = 1 / 2 := by
          rw [← extensionEmbeddingOfIsReal_apply hw, Complex.ofReal_re, ← ringEquivRealOfIsReal_apply,
            RingEquiv.apply_symm_apply]
        rw [hre]
        push_cast
        ring
      · intro w' _ hw'
        rw [Pi.single_eq_of_ne hw', map_zero, Complex.zero_re, mul_zero]
      · intro h; exact absurd (Finset.mem_univ w) h
    rw [hsum, ratArchLine_ratCast]
  rw [hfin, AddChar.map_zero_eq_one, mul_one, hinf, psiArch_algebraMap]
  have : (2 * Real.pi * Complex.I) * (((1 / 2 : ℚ)) : ℂ) = Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

end Elem17

end

open scoped Classical in
open Elem17 NumberField.InfinitePlace NumberField.InfinitePlace.Completion in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : (AdeleRing (𝓞 K) K))).2 = 1) (x : ℝ) :
    diagOne a * archRealGLAt hw (unipotentGL2 x) =
        unipotentGL2 (show (AdeleRing (𝓞 K) K) from (Pi.single w (((a : (AdeleRing (𝓞 K) K))).1 w *
            (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x), 0)) * diagOne a ∧
      NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (1 / 2)), 0)) = -1 := by
  classical
  refine ⟨?_, stdAddChar_single_half w hw⟩
  refine eq_of_glArch_eq_of_glFin_eq (glArch_ext fun w' => ?_) ?_
  · rw [map_mul, map_mul, map_mul, map_mul, archComponent_glArch_diagOne, archComponent_glArch_unipotentGL2]
    by_cases hww : w' = w
    · subst hww
      rw [archComponent_glArch_archRealGLAt_self, glEquivOfRingEquiv_unipotentGL2]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
        diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply,
        unipotentGL2_coe, unipotentGL2_coe]
      simp only [Units.coe_map]
      show _ = _
      fin_cases i <;> fin_cases j
      · simp
      · simp
        exact Or.inl rfl
      · simp
      · simp
    · rw [archComponent_glArch_archRealGLAt_of_ne hw hww, mul_one]
      have h0 : ((show (AdeleRing (𝓞 K) K) from (Pi.single w (((a : (AdeleRing (𝓞 K) K))).1 w *
          (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x), 0))).1 w' = 0 := by
        show Pi.single (M := fun v : InfinitePlace K => v.Completion) w
          (((a : (AdeleRing (𝓞 K) K))).1 w * (ringEquivRealOfIsReal hw).symm x) w' = 0
        exact Pi.single_eq_of_ne hww _
      rw [h0, unipotentGL2_zero, one_mul]
  · rw [map_mul, map_mul, glFin_diagOne_of_snd_eq_one a ha, glFin_archRealGLAt, glFin_unipotentGL2]
    show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) * 1 = unipotentGL2 0 * 1
    rw [unipotentGL2_zero]

end S_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
end P2MW
export P2MW.S_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half (solution)
