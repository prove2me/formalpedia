-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_four_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:09.480549+00:00
-- url     : https://prove2.me/submissions/bdde8899-c79b-46f1-a59d-b9e13725323b

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates

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
theorem _root_.solution {a : Fin 4 → k} (ha : a 0 ≠ 0) :
    (∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
        x ^ 2 - (-(a 0 * a 1)) * y ^ 2 - (-(a 0 * a 2)) * z ^ 2 + (a 0 * a 3) * t ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_four] at h
    refine ⟨a 0 * x 0, x 1, x 2, x 3, ?_, by linear_combination a 0 * h⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, h1, h2, h3⟩ := hc
    apply hx
    funext i
    fin_cases i
    · simpa [ha] using h0
    · exact h1
    · exact h2
    · exact h3
  · rintro ⟨x, y, z, t, hx, h⟩
    refine ⟨![x / a 0, y, z, t], ?_, ?_⟩
    · intro hc
      have h0 := congrFun hc 0
      have h1 := congrFun hc 1
      have h2 := congrFun hc 2
      have h3 := congrFun hc 3
      simp [ha] at h0 h1 h2 h3
      simp [h0, h1, h2, h3] at hx
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp
      linear_combination h
end GlobalTheory.LocalQuad
