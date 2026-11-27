-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_theta_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:44:19.597319+00:00
-- url     : https://prove2.me/submissions/4ab44072-e750-405d-acfa-30d7fcc6fa79

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_pos_mul_realEmb
import Theorems.Thm_GroundTheory_Automorphic_exists_sign_traceGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {H b}
namespace GroundTheory.Automorphic
theorem _root_.solution (hdef : ∀ w : InfinitePlace K, ∃ hw : w.IsReal, IsHermDefiniteAt H w hw) :
    ∃ θ : K, ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c) := by
  have hreal : ∀ w : InfinitePlace K, w.IsReal := fun w => (hdef w).1
  choose ε hε hεpos using fun w => exists_sign_traceGram (b := b) (hdef w).1 (hdef w).2
  obtain ⟨θ, hθ⟩ := exists_forall_pos_mul_realEmb hreal ε hε
  refine ⟨θ, fun w hw v hv => ?_⟩
  have h1 := hεpos w v hv
  have h2 := hθ w
  have : ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c) =
      realEmb hreal w θ * ∑ a, ∑ c, v a * v c * embedding_of_isReal (hdef w).1 (traceGram H b a c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    ring
  rw [this]
  have := mul_pos h1 h2
  nlinarith [sq_nonneg (ε w)]
end GroundTheory.Automorphic
