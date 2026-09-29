-- Prove2me | solution 1 for NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bfc25275-d6c6-5cd7-8e37-84ca6a957cf9

import Theorems.Thm_NumberField_AdelicLevel_exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
p2m_attr_erase "simp" "AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe"

set_option autoImplicit false

noncomputable section

namespace M4aP1R
namespace LevelCoveringArch

open Matrix NumberField NumberField.InfinitePlace NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

def realProj (w : InfinitePlace ℚ) (hw : w.IsReal) :
    GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom).comp
    ((archComponent ℚ w).comp (glArch (𝓞 ℚ) ℚ))

theorem realProj_apply (w : InfinitePlace ℚ) (hw : w.IsReal) (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    realProj w hw h = Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
      (archComponent ℚ w (glArch (𝓞 ℚ) ℚ h)) := rfl

def ratToReal (w : InfinitePlace ℚ) (hw : w.IsReal) : ℚ →+* ℝ :=
  (Completion.ringEquivRealOfIsReal hw).toRingHom.comp
    ((archEval ℚ w).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))))

theorem realProj_globalPoints_apply (w : InfinitePlace ℚ) (hw : w.IsReal) (γ : GL (Fin 2) ℚ)
    (i j : Fin 2) :
    ((realProj w hw (globalPoints (𝓞 ℚ) ℚ γ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j : ℝ) := by
  show ratToReal w hw ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = _
  exact eq_ratCast (ratToReal w hw) _

theorem det_realProj_globalPoints (w : InfinitePlace ℚ) (hw : w.IsReal) (γ : GL (Fin 2) ℚ) :
    (((realProj w hw (globalPoints (𝓞 ℚ) ℚ γ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det
      = ((γ : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, realProj_globalPoints_apply,
    realProj_globalPoints_apply, realProj_globalPoints_apply, realProj_globalPoints_apply]
  push_cast
  ring

def eps : GL (Fin 2) ℚ where
  val := !![-1, 0; 0, 1]
  inv := !![-1, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem eps_val : ((eps : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, 1] := rfl
theorem eps_inv : eps⁻¹ = eps := by
  apply Units.ext; rfl

theorem det_eps : ((eps : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = -1 := by
  rw [eps_val, Matrix.det_fin_two]; simp

theorem isLevelOneMatrix_eps (N : Ideal (𝓞 ℚ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ N
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hentry : ∀ i j, ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) :
      GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j) :=
    fun _ _ => rfl
  have h00 : ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 0 0 = -1 := by
    rw [hentry]; show algebraMap ℚ _ (-1) = -1; rw [map_neg, map_one]
  have h01 : ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 0 1 = 0 := by
    rw [hentry]; show algebraMap ℚ _ 0 = 0; rw [map_zero]
  have h10 : ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 = 0 := by
    rw [hentry]; show algebraMap ℚ _ 0 = 0; rw [map_zero]
  have h11 : ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 = 1 := by
    rw [hentry]; show algebraMap ℚ _ 1 = 1; rw [map_one]
  have hneg1 : (-1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    rw [show (-1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = 0 - 1 from (zero_sub 1).symm]
    exact sub_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles one_mem_integralFiniteAdeles
  refine { integral := ?_, lowerLeft := ?_, lowerRight := ?_ }
  · refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · rw [h00]; exact hneg1
    · rw [h01]; exact zero_mem_integralFiniteAdeles
    · rw [h10]; exact zero_mem_integralFiniteAdeles
    · rw [h11]; exact one_mem_integralFiniteAdeles
  · rw [h10]; exact zero_mem_idealBall N
  · rw [h11, sub_self]; exact zero_mem_idealBall N

theorem globalPoints_eps_mem_levelOne (N : Ideal (𝓞 ℚ)) :
    globalPoints (𝓞 ℚ) ℚ eps ∈ levelOne (𝓞 ℚ) ℚ N := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_eps N, ?_⟩
  rw [← map_inv, ← map_inv, eps_inv]
  exact isLevelOneMatrix_eps N

theorem exists_globalPoints_mul_mem_levelOne_rat_impl
    {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ∃ γ : GL (Fin 2) ℚ,
      globalPoints (𝓞 ℚ) ℚ γ * g ∈ levelOne (𝓞 ℚ) ℚ N ∧
        ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
              (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ * g)))
            ∈ Matrix.GLPos (Fin 2) ℝ := by

  obtain ⟨γ₁, hγ₁⟩ := NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat
    hN (glFin (𝓞 ℚ) ℚ g)
  have hg₁ : globalPoints (𝓞 ℚ) ℚ γ₁ * g ∈ levelOne (𝓞 ℚ) ℚ N := by
    rw [mem_levelOne_iff, map_mul]; exact hγ₁

  set w₀ : InfinitePlace ℚ := Rat.infinitePlace with hw₀_def
  have hw₀ : w₀.IsReal := Rat.isReal_infinitePlace
  have key : ∀ (γ : GL (Fin 2) ℚ),
      0 < (((realProj w₀ hw₀ (globalPoints (𝓞 ℚ) ℚ γ * g) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)).det →
      ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
            (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ * g)))
          ∈ Matrix.GLPos (Fin 2) ℝ := by
    intro γ hγ w hw
    obtain rfl : w = w₀ := Subsingleton.elim _ _
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply]
    exact hγ
  by_cases hsign : 0 < (((realProj w₀ hw₀ (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)).det
  · exact ⟨γ₁, hg₁, key γ₁ hsign⟩
  · refine ⟨eps * γ₁, ?_, key (eps * γ₁) ?_⟩
    · rw [map_mul, mul_assoc]
      exact mul_mem (globalPoints_eps_mem_levelOne N) hg₁
    · have hne : (((realProj w₀ hw₀ (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
      have hlt : (((realProj w₀ hw₀ (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)).det < 0 := lt_of_le_of_ne (not_lt.mp hsign) hne
      rw [map_mul (globalPoints (𝓞 ℚ) ℚ) eps γ₁, mul_assoc, map_mul (realProj w₀ hw₀), Units.val_mul,
        Matrix.det_mul, det_realProj_globalPoints, det_eps]
      push_cast
      linarith

end M4aP1R.LevelCoveringArch

theorem solution
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g
          ∈ NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ N ∧
        ∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ
                  (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g)))
            ∈ Matrix.GLPos (Fin 2) ℝ := by
  first
    | exact M4aP1R.LevelCoveringArch.exists_globalPoints_mul_mem_levelOne_rat_impl hN g
    | (apply M4aP1R.LevelCoveringArch.exists_globalPoints_mul_mem_levelOne_rat_impl <;> assumption)

end
end S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
end P2MW
export P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat (solution)
