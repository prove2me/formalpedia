-- Prove2me | solution 1 for GroundTheory.Automorphic.realEmb_mul_hermTrace_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:54.294466+00:00
-- url     : https://prove2.me/submissions/f2d4fb58-53d3-4c71-b7fd-21e16de2228d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_realEmb_mul_hermTrace_pos
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.hermTraceBilin_apply



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
theorem _root_.solution {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {w : InfinitePlace K} (hw : w.IsReal) (x : ι → K ⊗[K] E) :
    0 ≤ embedding_of_isReal hw (θ * hermTrace K H K x x) := by
  by_cases hx : x = 0
  · subst hx
    have : hermTrace K H K (0 : ι → K ⊗[K] E) 0 = 0 := by
      rw [← hermTraceBilin_apply, map_zero]
    rw [this, mul_zero, map_zero]
  · exact (realEmb_mul_hermTrace_pos hθ hw hx).le
end GroundTheory.Automorphic
