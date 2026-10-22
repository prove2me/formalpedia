-- Prove2me | solution 1 for LLLFactor.Factors.card_le_2_18
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T06:44:39.824252+00:00
-- url     : https://prove2.me/submissions/65924f0c-ac2b-44e1-93dd-ecd68749de9e

import Definitions.Def_LLLFactor_Factors_Setting
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Polynomial

namespace Oct21FiveLLL

/-- Truncation of real polynomial coefficients into the original Euclidean space. -/
def truncatedCoefficients (m : ℕ) : ℝ[X] →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) where
  toFun p := WithLp.toLp 2 (fun i => p.coeff i.val)
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

@[simp] theorem truncatedCoefficients_map (m : ℕ) (p : ℤ[X]) :
    truncatedCoefficients m (p.map (Int.castRingHom ℝ)) = LLLFactor.Factors.coeffVec m p := by
  ext i
  simp [truncatedCoefficients, LLLFactor.Factors.coeffVec]

end Oct21FiveLLL

open LLLFactor.Factors

/-- Dividing by a common factor leaves an independent family in a lower-degree
polynomial space, whose dimension bounds the number of selected polynomials. -/
theorem solution (m : ℕ) (b : Fin (m + 1) → ℤ[X])
    (hli : LinearIndependent ℝ (coeffVec m ∘ b)) (hdeg : ∀ j, (b j).natDegree ≤ m)
    (J : Finset (Fin (m + 1))) (h₁ : ℤ[X]) (hh₁ : h₁ ≠ 0) (hdvd : ∀ j ∈ J, h₁ ∣ b j) :
    J.card ≤ m + 1 - h₁.natDegree := by
  classical
  let f : ℤ[X] → ℝ[X] := fun p => p.map (Int.castRingHom ℝ)
  have hliR : LinearIndependent ℝ (fun j => f (b j)) := by
    apply LinearIndependent.of_comp (Oct21FiveLLL.truncatedCoefficients m)
    simpa only [Function.comp_def, f, Oct21FiveLLL.truncatedCoefficients_map] using hli
  have hbj (j : Fin (m + 1)) : b j ≠ 0 := by
    intro hz
    have hn := hli.ne_zero j
    apply hn
    simp [Function.comp_def, hz, coeffVec]
    rfl
  let q : J → ℤ[X] := fun j => Classical.choose (hdvd j.val j.property)
  have hmul (j : J) : h₁ * q j = b j.val := by
    exact (Classical.choose_spec (hdvd j.val j.property)).symm
  have hq0 (j : J) : q j ≠ 0 := by
    intro hz
    have he := hmul j
    simp only [hz, mul_zero] at he
    exact hbj j.val he.symm
  let N := m + 1 - h₁.natDegree
  have hqd (j : J) : f (q j) ∈ Polynomial.degreeLT ℝ N := by
    have he := Polynomial.natDegree_mul hh₁ (hq0 j)
    rw [hmul] at he
    have hd := hdeg j.val
    have hn : (q j).natDegree < N := by dsimp [N]; omega
    have hm : (f (q j)).natDegree < N :=
      lt_of_le_of_lt (Polynomial.natDegree_map_le) hn
    exact Polynomial.mem_degreeLT.mpr
      (Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hm))
  have hmulR (j : J) : f h₁ * f (q j) = f (b j.val) := by
    simpa only [f, Polynomial.map_mul] using congrArg f (hmul j)
  have hliQ : LinearIndependent ℝ (fun j : J => f (q j)) := by
    apply LinearIndependent.of_comp (LinearMap.mulLeft ℝ (f h₁))
    change LinearIndependent ℝ (fun j : J => f h₁ * f (q j))
    simp only [hmulR]
    exact hliR.comp Subtype.val Subtype.val_injective
  let w : J → Polynomial.degreeLT ℝ N := fun j => ⟨f (q j), hqd j⟩
  have hliW : LinearIndependent ℝ w := by
    apply LinearIndependent.of_comp (Polynomial.degreeLT ℝ N).subtype
    exact hliQ
  have hliC := hliW.map' (Polynomial.degreeLTEquiv ℝ N).toLinearMap
    (LinearMap.ker_eq_bot.mpr (Polynomial.degreeLTEquiv ℝ N).injective)
  have hc := hliC.fintype_card_le_finrank
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, Fintype.card_coe, N,
    smul_eq_mul, mul_one] using hc

#print axioms solution
