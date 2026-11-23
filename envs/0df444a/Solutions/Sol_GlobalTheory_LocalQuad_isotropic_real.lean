-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:11.010704+00:00
-- url     : https://prove2.me/submissions/a07aaa8b-bac7-44b4-a099-7b991f804178

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
variable {k : Type*} [Field k]
namespace GlobalTheory.LocalQuad
theorem _root_.solution {ι : Type*} [Fintype ι] {a : ι → ℝ} {i j : ι} (hi : a i < 0) (hj : 0 < a j) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  have hij : i ≠ j := by rintro rfl; linarith
  refine isotropic_of_injective ![i, j] ?_ ⟨![√(a j), √(-a i)], ?_, ?_⟩
  · intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro hc
    have := congrFun hc 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    exact (Real.sqrt_pos.2 hj).ne' this
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.sq_sqrt hj.le, Real.sq_sqrt (by linarith)]
    ring
end GlobalTheory.LocalQuad
