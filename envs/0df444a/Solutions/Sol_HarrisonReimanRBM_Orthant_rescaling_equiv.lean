-- Prove2me | solution 1 for HarrisonReimanRBM.Orthant.rescaling_equiv
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:53:51.330953+00:00
-- url     : https://prove2.me/submissions/3bdf7d8b-7e26-48c8-97d8-7d7988b513ff

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

open Reiman84.QueueLength

namespace Aux_HR_resc

open HarrisonReimanRBM.Orthant Reiman84.QueueLength Matrix

variable {K : ℕ}

lemma sp (d : Fin K → ℝ) (x : ℝ → Fin K → ℝ) (t : ℝ) (j : Fin K) :
    scalePath d x t j = x t j * d j := by
  unfold scalePath
  rw [vecMul_diagonal]

lemma resc_apply (d : Fin K → ℝ) (Q : Matrix (Fin K) (Fin K) ℝ) (i j : Fin K) :
    rescaleMatrix d Q i j = (d i)⁻¹ * Q i j * d j := by
  unfold rescaleMatrix
  rw [mul_diagonal, diagonal_mul]

lemma vecMul_resc (d : Fin K → ℝ) (hd : ∀ i, 0 < d i) (Q : Matrix (Fin K) (Fin K) ℝ)
    (v : Fin K → ℝ) (j : Fin K) :
    vecMul (fun i => v i * d i) (rescaleMatrix d Q) j = vecMul v Q j * d j := by
  simp only [vecMul, dotProduct, resc_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have := (hd i).ne'
  field_simp

lemma contOn (d : Fin K → ℝ) (x : ℝ → Fin K → ℝ) (hx : ContinuousOn x (Set.Ici 0)) :
    ContinuousOn (scalePath d x) (Set.Ici 0) := by
  have : scalePath d x = fun t j => x t j * d j := by
    funext t j; exact sp d x t j
  rw [this]
  apply continuousOn_pi.mpr
  intro j
  exact (continuousOn_pi.mp hx j).mul continuousOn_const

lemma forward (Q : Matrix (Fin K) (Fin K) ℝ) (d : Fin K → ℝ) (hd : ∀ i, 0 < d i)
    (x y z : ℝ → Fin K → ℝ) (h : IsReflectionPair Q x y z) :
    IsReflectionPair (rescaleMatrix d Q) (scalePath d x) (scalePath d y) (scalePath d z) := by
  obtain ⟨⟨hxc, hx0⟩, hyc, hzc, heq, hzpos, ⟨hymono, hy0⟩, hcomp⟩ := h
  refine ⟨⟨contOn d x hxc, ?_⟩, contOn d y hyc, contOn d z hzc, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro j
    rw [sp]
    exact mul_nonneg (hx0 j) (hd j).le
  · intro t ht
    funext j
    rw [vecMul_sub, vecMul_one]
    simp only [Pi.add_apply, Pi.sub_apply]
    have hS : scalePath d y t = fun i => y t i * d i := by funext i; exact sp d y t i
    rw [hS, vecMul_resc d hd Q, sp, sp]
    have := congrFun (heq t ht) j
    rw [vecMul_sub, vecMul_one] at this
    simp only [Pi.add_apply, Pi.sub_apply] at this
    rw [this]
    ring
  · intro t ht j
    rw [sp]
    exact mul_nonneg (hzpos t ht j) (hd j).le
  · intro s hs t ht hst j
    rw [sp, sp]
    exact mul_le_mul_of_nonneg_right (hymono hs ht hst j) (hd j).le
  · funext j
    rw [sp, hy0]
    simp
  · intro j s t hs hst hpos
    rw [sp, sp]
    have : y t j = y s j := hcomp j s t hs hst (fun r hr => by
      have := hpos r hr
      rw [sp] at this
      exact (mul_pos_iff_of_pos_right (hd j)).mp this)
    rw [this]

lemma resc_inv (d : Fin K → ℝ) (hd : ∀ i, 0 < d i) (Q : Matrix (Fin K) (Fin K) ℝ) :
    rescaleMatrix (fun i => (d i)⁻¹) (rescaleMatrix d Q) = Q := by
  ext i j
  rw [resc_apply, resc_apply]
  have := (hd i).ne'
  have := (hd j).ne'
  field_simp

lemma sp_inv (d : Fin K → ℝ) (hd : ∀ i, 0 < d i) (x : ℝ → Fin K → ℝ) :
    scalePath (fun i => (d i)⁻¹) (scalePath d x) = x := by
  funext t j
  rw [sp, sp]
  have := (hd j).ne'
  field_simp

end Aux_HR_resc

open HarrisonReimanRBM.Orthant Reiman84.QueueLength in
theorem solution {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) (d : Fin K → ℝ) (hd : ∀ i, 0 < d i)
    (x y z : ℝ → Fin K → ℝ) :
    IsReflectionPair Q x y z ↔
      IsReflectionPair (rescaleMatrix d Q) (scalePath d x) (scalePath d y) (scalePath d z) := by
  constructor
  · exact Aux_HR_resc.forward Q d hd x y z
  · intro h
    have hd' : ∀ i, 0 < (fun i => (d i)⁻¹) i := fun i => inv_pos.mpr (hd i)
    have := Aux_HR_resc.forward _ (fun i => (d i)⁻¹) hd' _ _ _ h
    rwa [Aux_HR_resc.resc_inv d hd, Aux_HR_resc.sp_inv d hd, Aux_HR_resc.sp_inv d hd,
      Aux_HR_resc.sp_inv d hd] at this
