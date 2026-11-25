-- Prove2me | solution 1 for GroundTheory.Brauer.isSimpleModule_columnIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:12.429046+00:00
-- url     : https://prove2.me/submissions/75120c60-0c46-44e4-bc4a-c69c4aa548d9

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v w
variable {K : Type u} [Field K]
variable {R : Type v} [Ring R] [Algebra K R] {D : Type w} [DivisionRing D] [Algebra K D]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (e : R ≃ₐ[K] Matrix ι ι D) (i₀ : ι)
namespace GroundTheory.Brauer
theorem _root_.solution : IsSimpleModule R (columnIdeal e i₀) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨⟨⟨⟨_, symm_single_mem_columnIdeal e i₀ 1⟩, 0, fun h => ?_⟩⟩, fun x hx y => ?_⟩
  · have h' := congrArg (fun z : columnIdeal e i₀ => e (z : R) i₀ i₀) h
    simp at h'
  · have hx' : ∃ i, e (x : R) i i₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx
      apply Subtype.ext
      apply e.injective
      ext i j
      by_cases hj : j = i₀
      · subst hj
        simpa using hcon i
      · simpa using x.2 i j hj
    obtain ⟨i, hi⟩ := hx'
    refine ⟨e.symm (Matrix.of fun k l => if l = i then e (y : R) k i₀ * (e (x : R) i i₀)⁻¹
      else 0), ?_⟩
    apply Subtype.ext
    apply e.injective
    ext k j
    simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, smul_eq_mul, map_mul,
      e.apply_symm_apply, Matrix.mul_apply, Matrix.of_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hj : j = i₀
    · subst hj
      rw [mul_assoc, inv_mul_cancel₀ hi, mul_one]
    · rw [x.2 i j hj, y.2 k j hj, mul_zero]
end GroundTheory.Brauer
