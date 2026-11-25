-- Prove2me | solution 1 for GlobalTheory.UnitCase.row_det_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:35.711784+00:00
-- url     : https://prove2.me/submissions/050de0d5-1dae-40b2-86c3-d0b0157f156b

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution (n k : ℕ) (A : Fin n × Fin n →₀ ℕ) (hA : A ∈ (cayDet n ℤ ^ k).support)
    (b : Fin n) : ∑ c, A (b, c) = k := by
  have h : (cayDet n ℤ).IsWeightedHomogeneous
      (fun x : Fin n × Fin n => if x.1 = b then 1 else 0) 1 := by
    rw [cayDet, Matrix.det_apply]
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun τ _ => ?_
    have h1 := MvPolynomial.IsWeightedHomogeneous.prod (R := ℤ)
      (w := fun x : Fin n × Fin n => if x.1 = b then 1 else 0) Finset.univ
      (fun i : Fin n => MvPolynomial.X (τ i, i)) (fun i => if τ i = b then 1 else 0)
      (fun i _ => MvPolynomial.isWeightedHomogeneous_X _ _ _)
    have h2 : ∑ i : Fin n, (if τ i = b then 1 else 0) = 1 := by
      rw [Equiv.sum_comp τ fun i => if i = b then 1 else 0]
      simp
    rw [h2] at h1
    rw [Units.smul_def]
    exact (MvPolynomial.weightedHomogeneousSubmodule ℤ _ 1).smul_mem _ h1
  have h3 := (h.pow k) (MvPolynomial.mem_support_iff.1 hA)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type,
    Finset.sum_eq_single b] at h3
  · simpa using h3
  · intro b' _ hb
    simp [hb]
  · simp
end GlobalTheory.UnitCase
